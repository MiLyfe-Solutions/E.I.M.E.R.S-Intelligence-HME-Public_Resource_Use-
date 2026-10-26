import V185TrunkScan22Chunk159

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1428618 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_1428618 : Nat := 118140960795 + 1428618 * 2 ^ 59
def prefixEnd_1428618 : Nat := 4983230072969 + 3 ^ 40 * 1428618 * 2
def baseEnd_1428618 : Nat := 163015045703332613156647

theorem tailTrace_1428618 : CollatzResearch.WordTrace tailWord_1428618 prefixEnd_1428618 163015045703332613156647 := by
  unfold tailWord_1428618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026494784592112343647627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34737319425578966249727005 13026494784592112343647627)
  ·
    refine ⟨19539742176888168515471441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13026494784592112343647627 19539742176888168515471441)
    ·
      refine ⟨14654806632666126386603581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19539742176888168515471441 14654806632666126386603581)
      ·
        refine ⟨5495552487249797394976343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14654806632666126386603581 5495552487249797394976343)
        ·
          refine ⟨8243328730874696092464515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5495552487249797394976343 8243328730874696092464515)
          ·
            refine ⟨12364993096312044138696773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243328730874696092464515 12364993096312044138696773)
            ·
              refine ⟨2318436205558508276005645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12364993096312044138696773 2318436205558508276005645)
              ·
                refine ⟨869413577084440603502117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2318436205558508276005645 869413577084440603502117)
                ·
                  refine ⟨163015045703332613156647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869413577084440603502117 163015045703332613156647)
                  ·
                    rfl

theorem cell22_1428618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_1428618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428618 prefixEnd_1428618 := by exact prefixLift 1428618
  have htrace : WordTrace (prefixWord ++ tailWord_1428618) baseStart_1428618 baseEnd_1428618 := by
    simpa [prefixWord, tailWord_1428618, baseEnd_1428618] using wordTrace_append hprefix tailTrace_1428618
  have hstable : (prefixWord ++ tailWord_1428618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428618).length < 2 ^ (prefixWord ++ tailWord_1428618).sum := by decide
  have hdescent : baseEnd_1428618 < baseStart_1428618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428650 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1428650 : Nat := 118140960795 + 1428650 * 2 ^ 59
def prefixEnd_1428650 : Nat := 4983230072969 + 3 ^ 40 * 1428650 * 2
def baseEnd_1428650 : Nat := 489056091363960422669843

theorem tailTrace_1428650 : CollatzResearch.WordTrace tailWord_1428650 prefixEnd_1428650 489056091363960422669843 := by
  unfold tailWord_1428650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026786568563129709938851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34738097516168345893170269 13026786568563129709938851)
  ·
    refine ⟨19540179852844694564908277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13026786568563129709938851 19540179852844694564908277)
    ·
      refine ⟨1831891861204190115460151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19540179852844694564908277 1831891861204190115460151)
      ·
        refine ⟨2747837791806285173190227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831891861204190115460151 2747837791806285173190227)
        ·
          refine ⟨4121756687709427759785341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747837791806285173190227 4121756687709427759785341)
          ·
            refine ⟨1545658757891035409919503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4121756687709427759785341 1545658757891035409919503)
            ·
              refine ⟨2318488136836553114879255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545658757891035409919503 2318488136836553114879255)
              ·
                refine ⟨3477732205254829672318883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318488136836553114879255 3477732205254829672318883)
                ·
                  refine ⟨5216598307882244508478325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477732205254829672318883 5216598307882244508478325)
                  ·
                    refine ⟨489056091363960422669843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5216598307882244508478325 489056091363960422669843)
                    ·
                      rfl

theorem cell22_1428650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1428650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428650 prefixEnd_1428650 := by exact prefixLift 1428650
  have htrace : WordTrace (prefixWord ++ tailWord_1428650) baseStart_1428650 baseEnd_1428650 := by
    simpa [prefixWord, tailWord_1428650, baseEnd_1428650] using wordTrace_append hprefix tailTrace_1428650
  have hstable : (prefixWord ++ tailWord_1428650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428650).length < 2 ^ (prefixWord ++ tailWord_1428650).sum := by decide
  have hdescent : baseEnd_1428650 < baseStart_1428650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428659 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_1428659 : Nat := 118140960795 + 1428659 * 2 ^ 59
def prefixEnd_1428659 : Nat := 4983230072969 + 3 ^ 40 * 1428659 * 2
def baseEnd_1428659 : Nat := 489059172247887399194815

theorem tailTrace_1428659 : CollatzResearch.WordTrace tailWord_1428659 prefixEnd_1428659 489059172247887399194815 := by
  unfold tailWord_1428659
  simp only [CollatzResearch.WordTrace]
  refine ⟨52107474531219913376833031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34738316354146608917888687 52107474531219913376833031)
  ·
    refine ⟨78161211796829870065249547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52107474531219913376833031 78161211796829870065249547)
    ·
      refine ⟨117241817695244805097874321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78161211796829870065249547 117241817695244805097874321)
      ·
        refine ⟨87931363271433603823405741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117241817695244805097874321 87931363271433603823405741)
        ·
          refine ⟨32974261226787601433777153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87931363271433603823405741 32974261226787601433777153)
          ·
            refine ⟨24730695920090701075332865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32974261226787601433777153 24730695920090701075332865)
            ·
              refine ⟨18548021940068025806499649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24730695920090701075332865 18548021940068025806499649)
              ·
                refine ⟨13911016455051019354874737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18548021940068025806499649 13911016455051019354874737)
                ·
                  refine ⟨10433262341288264516156053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13911016455051019354874737 10433262341288264516156053)
                  ·
                    refine ⟨489059172247887399194815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10433262341288264516156053 489059172247887399194815)
                    ·
                      rfl

theorem cell22_1428659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_1428659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428659 prefixEnd_1428659 := by exact prefixLift 1428659
  have htrace : WordTrace (prefixWord ++ tailWord_1428659) baseStart_1428659 baseEnd_1428659 := by
    simpa [prefixWord, tailWord_1428659, baseEnd_1428659] using wordTrace_append hprefix tailTrace_1428659
  have hstable : (prefixWord ++ tailWord_1428659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428659).length < 2 ^ (prefixWord ++ tailWord_1428659).sum := by decide
  have hdescent : baseEnd_1428659 < baseStart_1428659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428708 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_1428708 : Nat := 118140960795 + 1428708 * 2 ^ 59
def prefixEnd_1428708 : Nat := 4983230072969 + 3 ^ 40 * 1428708 * 2
def baseEnd_1428708 : Nat := 163025315316422534906555

theorem tailTrace_1428708 : CollatzResearch.WordTrace tailWord_1428708 prefixEnd_1428708 163025315316422534906555 := by
  unfold tailWord_1428708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26054630854021197372683389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34739507805361596496911185 26054630854021197372683389)
  ·
    refine ⟨9770486570257949014756271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26054630854021197372683389 9770486570257949014756271)
    ·
      refine ⟨14655729855386923522134407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770486570257949014756271 14655729855386923522134407)
      ·
        refine ⟨21983594783080385283201611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14655729855386923522134407 21983594783080385283201611)
        ·
          refine ⟨32975392174620577924802417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21983594783080385283201611 32975392174620577924802417)
          ·
            refine ⟨24731544130965433443601813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32975392174620577924802417 24731544130965433443601813)
            ·
              refine ⟨1159291131139004692668835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24731544130965433443601813 1159291131139004692668835)
              ·
                refine ⟨1738936696708507039003253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159291131139004692668835 1738936696708507039003253)
                ·
                  refine ⟨163025315316422534906555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738936696708507039003253 163025315316422534906555)
                  ·
                    rfl

theorem cell22_1428708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_1428708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428708 prefixEnd_1428708 := by exact prefixLift 1428708
  have htrace : WordTrace (prefixWord ++ tailWord_1428708) baseStart_1428708 baseEnd_1428708 := by
    simpa [prefixWord, tailWord_1428708, baseEnd_1428708] using wordTrace_append hprefix tailTrace_1428708
  have hstable : (prefixWord ++ tailWord_1428708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428708).length < 2 ^ (prefixWord ++ tailWord_1428708).sum := by decide
  have hdescent : baseEnd_1428708 < baseStart_1428708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428753 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 4]
def baseStart_1428753 : Nat := 118140960795 + 1428753 * 2 ^ 59
def prefixEnd_1428753 : Nat := 4983230072969 + 3 ^ 40 * 1428753 * 2
def baseEnd_1428753 : Nat := 163030450122967495781509

theorem tailTrace_1428753 : CollatzResearch.WordTrace tailWord_1428753 prefixEnd_1428753 163030450122967495781509 := by
  unfold tailWord_1428753
  simp only [CollatzResearch.WordTrace]
  refine ⟨52110902992879367430754913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34740601995252911620503275 52110902992879367430754913)
  ·
    refine ⟨39083177244659525573066185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52110902992879367430754913 39083177244659525573066185)
    ·
      refine ⟨29312382933494644179799639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39083177244659525573066185 29312382933494644179799639)
      ·
        refine ⟨43968574400241966269699459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29312382933494644179799639 43968574400241966269699459)
        ·
          refine ⟨65952861600362949404549189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43968574400241966269699459 65952861600362949404549189)
          ·
            refine ⟨12366161550068053013352973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65952861600362949404549189 12366161550068053013352973)
            ·
              refine ⟨4637310581275519880007365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12366161550068053013352973 4637310581275519880007365)
              ·
                refine ⟨869495733989159977501381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4637310581275519880007365 869495733989159977501381)
                ·
                  refine ⟨163030450122967495781509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869495733989159977501381 163030450122967495781509)
                  ·
                    rfl

theorem cell22_1428753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_1428753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428753 prefixEnd_1428753 := by exact prefixLift 1428753
  have htrace : WordTrace (prefixWord ++ tailWord_1428753) baseStart_1428753 baseEnd_1428753 := by
    simpa [prefixWord, tailWord_1428753, baseEnd_1428753] using wordTrace_append hprefix tailTrace_1428753
  have hstable : (prefixWord ++ tailWord_1428753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428753).length < 2 ^ (prefixWord ++ tailWord_1428753).sum := by decide
  have hdescent : baseEnd_1428753 < baseStart_1428753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428841 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_1428841 : Nat := 118140960795 + 1428841 * 2 ^ 59
def prefixEnd_1428841 : Nat := 4983230072969 + 3 ^ 40 * 1428841 * 2
def baseEnd_1428841 : Nat := 489121474567299591144257

theorem tailTrace_1428841 : CollatzResearch.WordTrace tailWord_1428841 prefixEnd_1428841 489121474567299591144257 := by
  unfold tailWord_1428841
  simp only [CollatzResearch.WordTrace]
  refine ⟨52114112616560558459958377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34742741744373705639972251 52114112616560558459958377)
  ·
    refine ⟨39085584462420418844968783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52114112616560558459958377 39085584462420418844968783)
    ·
      refine ⟨58628376693630628267453175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39085584462420418844968783 58628376693630628267453175)
      ·
        refine ⟨87942565040445942401179763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58628376693630628267453175 87942565040445942401179763)
        ·
          refine ⟨131913847560668913601769645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87942565040445942401179763 131913847560668913601769645)
          ·
            refine ⟨49467692835250842600663617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131913847560668913601769645 49467692835250842600663617)
            ·
              refine ⟨37100769626438131950497713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49467692835250842600663617 37100769626438131950497713)
              ·
                refine ⟨27825577219828598962873285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37100769626438131950497713 27825577219828598962873285)
                ·
                  refine ⟨5217295728717862305538741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27825577219828598962873285 5217295728717862305538741)
                  ·
                    refine ⟨489121474567299591144257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5217295728717862305538741 489121474567299591144257)
                    ·
                      rfl

theorem cell22_1428841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_1428841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428841 prefixEnd_1428841 := by exact prefixLift 1428841
  have htrace : WordTrace (prefixWord ++ tailWord_1428841) baseStart_1428841 baseEnd_1428841 := by
    simpa [prefixWord, tailWord_1428841, baseEnd_1428841] using wordTrace_append hprefix tailTrace_1428841
  have hstable : (prefixWord ++ tailWord_1428841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428841).length < 2 ^ (prefixWord ++ tailWord_1428841).sum := by decide
  have hdescent : baseEnd_1428841 < baseStart_1428841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428920 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1428920 : Nat := 118140960795 + 1428920 * 2 ^ 59
def prefixEnd_1428920 : Nat := 4983230072969 + 3 ^ 40 * 1428920 * 2
def baseEnd_1428920 : Nat := 489148517881769718419015

theorem tailTrace_1428920 : CollatzResearch.WordTrace tailWord_1428920 prefixEnd_1428920 489148517881769718419015 := by
  unfold tailWord_1428920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26058496991637177476042107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34744662655516236634722809 26058496991637177476042107)
  ·
    refine ⟨39087745487455766214063161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26058496991637177476042107 39087745487455766214063161)
    ·
      refine ⟨29315809115591824660547371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39087745487455766214063161 29315809115591824660547371)
      ·
        refine ⟨43973713673387736990821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29315809115591824660547371 43973713673387736990821057)
        ·
          refine ⟨32980285255040802743115793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43973713673387736990821057 32980285255040802743115793)
          ·
            refine ⟨24735213941280602057336845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32980285255040802743115793 24735213941280602057336845)
            ·
              refine ⟨9275705227980225771501317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24735213941280602057336845 9275705227980225771501317)
              ·
                refine ⟨1739194730246292332156497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9275705227980225771501317 1739194730246292332156497)
                ·
                  refine ⟨1304396047684719249117373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1739194730246292332156497 1304396047684719249117373)
                  ·
                    refine ⟨489148517881769718419015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304396047684719249117373 489148517881769718419015)
                    ·
                      rfl

theorem cell22_1428920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1428920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428920 prefixEnd_1428920 := by exact prefixLift 1428920
  have htrace : WordTrace (prefixWord ++ tailWord_1428920) baseStart_1428920 baseEnd_1428920 := by
    simpa [prefixWord, tailWord_1428920, baseEnd_1428920] using wordTrace_append hprefix tailTrace_1428920
  have hstable : (prefixWord ++ tailWord_1428920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428920).length < 2 ^ (prefixWord ++ tailWord_1428920).sum := by decide
  have hdescent : baseEnd_1428920 < baseStart_1428920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428982 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1428982 : Nat := 118140960795 + 1428982 * 2 ^ 59
def prefixEnd_1428982 : Nat := 4983230072969 + 3 ^ 40 * 1428982 * 2
def baseEnd_1428982 : Nat := 489169741748822223368825

theorem tailTrace_1428982 : CollatzResearch.WordTrace tailWord_1428982 prefixEnd_1428982 489169741748822223368825 := by
  unfold tailWord_1428982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257453456815608721302575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34746170206033159693894133 3257453456815608721302575)
  ·
    refine ⟨4886180185223413081953863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257453456815608721302575 4886180185223413081953863)
    ·
      refine ⟨7329270277835119622930795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886180185223413081953863 7329270277835119622930795)
      ·
        refine ⟨10993905416752679434396193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7329270277835119622930795 10993905416752679434396193)
        ·
          refine ⟨8245429062564509575797145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10993905416752679434396193 8245429062564509575797145)
          ·
            refine ⟨6184071796923382181847859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8245429062564509575797145 6184071796923382181847859)
            ·
              refine ⟨9276107695385073272771789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184071796923382181847859 9276107695385073272771789)
              ·
                refine ⟨3478540385769402477289421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9276107695385073272771789 3478540385769402477289421)
                ·
                  refine ⟨1304452644663525928983533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3478540385769402477289421 1304452644663525928983533)
                  ·
                    refine ⟨489169741748822223368825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304452644663525928983533 489169741748822223368825)
                    ·
                      rfl

theorem cell22_1428982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1428982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428982 prefixEnd_1428982 := by exact prefixLift 1428982
  have htrace : WordTrace (prefixWord ++ tailWord_1428982) baseStart_1428982 baseEnd_1428982 := by
    simpa [prefixWord, tailWord_1428982, baseEnd_1428982] using wordTrace_append hprefix tailTrace_1428982
  have hstable : (prefixWord ++ tailWord_1428982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428982).length < 2 ^ (prefixWord ++ tailWord_1428982).sum := by decide
  have hdescent : baseEnd_1428982 < baseStart_1428982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429016 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 1, 3]
def baseStart_1429016 : Nat := 118140960795 + 1429016 * 2 ^ 59
def prefixEnd_1429016 : Nat := 4983230072969 + 3 ^ 40 * 1429016 * 2
def baseEnd_1429016 : Nat := 489181380643657468018721

theorem tailTrace_1429016 : CollatzResearch.WordTrace tailWord_1429016 prefixEnd_1429016 489181380643657468018721 := by
  unfold tailWord_1429016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26060247695463281673789451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34746996927284375565052601 26060247695463281673789451)
  ·
    refine ⟨39090371543194922510684177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26060247695463281673789451 39090371543194922510684177)
    ·
      refine ⟨29317778657396191883013133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39090371543194922510684177 29317778657396191883013133)
      ·
        refine ⟨10994166996523571956129925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29317778657396191883013133 10994166996523571956129925)
        ·
          refine ⟨2061406311848169741774361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10994166996523571956129925 2061406311848169741774361)
          ·
            refine ⟨1546054733886127306330771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2061406311848169741774361 1546054733886127306330771)
            ·
              refine ⟨2319082100829190959496157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546054733886127306330771 2319082100829190959496157)
              ·
                refine ⟨869655787810946609811059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2319082100829190959496157 869655787810946609811059)
                ·
                  refine ⟨1304483681716419914716589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869655787810946609811059 1304483681716419914716589)
                  ·
                    refine ⟨489181380643657468018721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304483681716419914716589 489181380643657468018721)
                    ·
                      rfl

theorem cell22_1429016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_1429016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429016 prefixEnd_1429016 := by exact prefixLift 1429016
  have htrace : WordTrace (prefixWord ++ tailWord_1429016) baseStart_1429016 baseEnd_1429016 := by
    simpa [prefixWord, tailWord_1429016, baseEnd_1429016] using wordTrace_append hprefix tailTrace_1429016
  have hstable : (prefixWord ++ tailWord_1429016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429016).length < 2 ^ (prefixWord ++ tailWord_1429016).sum := by decide
  have hdescent : baseEnd_1429016 < baseStart_1429016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429023 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 8]
def baseStart_1429023 : Nat := 118140960795 + 1429023 * 2 ^ 59
def prefixEnd_1429023 : Nat := 4983230072969 + 3 ^ 40 * 1429023 * 2
def baseEnd_1429023 : Nat := 163061258962237261031233

theorem tailTrace_1429023 : CollatzResearch.WordTrace tailWord_1429023 prefixEnd_1429023 163061258962237261031233 := by
  unfold tailWord_1429023
  simp only [CollatzResearch.WordTrace]
  refine ⟨52120750701901203543083723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34747167134600802362055815 52120750701901203543083723)
  ·
    refine ⟨78181126052851805314625585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52120750701901203543083723 78181126052851805314625585)
    ·
      refine ⟨58635844539638853985969189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78181126052851805314625585 58635844539638853985969189)
      ·
        refine ⟨10994220851182285122369223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58635844539638853985969189 10994220851182285122369223)
        ·
          refine ⟨16491331276773427683553835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10994220851182285122369223 16491331276773427683553835)
          ·
            refine ⟨24736996915160141525330753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16491331276773427683553835 24736996915160141525330753)
            ·
              refine ⟨18552747686370106143998065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24736996915160141525330753 18552747686370106143998065)
              ·
                refine ⟨13914560764777579607998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18552747686370106143998065 13914560764777579607998549)
                ·
                  refine ⟨163061258962237261031233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13914560764777579607998549 163061258962237261031233)
                  ·
                    rfl

theorem cell22_1429023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_1429023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429023 prefixEnd_1429023 := by exact prefixLift 1429023
  have htrace : WordTrace (prefixWord ++ tailWord_1429023) baseStart_1429023 baseEnd_1429023 := by
    simpa [prefixWord, tailWord_1429023, baseEnd_1429023] using wordTrace_append hprefix tailTrace_1429023
  have hstable : (prefixWord ++ tailWord_1429023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429023).length < 2 ^ (prefixWord ++ tailWord_1429023).sum := by decide
  have hdescent : baseEnd_1429023 < baseStart_1429023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429046 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1429046 : Nat := 118140960795 + 1429046 * 2 ^ 59
def prefixEnd_1429046 : Nat := 4983230072969 + 3 ^ 40 * 1429046 * 2
def baseEnd_1429046 : Nat := 163063883418915796589543

theorem tailTrace_1429046 : CollatzResearch.WordTrace tailWord_1429046 prefixEnd_1429046 163063883418915796589543 := by
  unfold tailWord_1429046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257599348801117404448187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34747726387211918980780661 3257599348801117404448187)
  ·
    refine ⟨4886399023201676106672281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257599348801117404448187 4886399023201676106672281)
    ·
      refine ⟨3664799267401257080004211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4886399023201676106672281 3664799267401257080004211)
      ·
        refine ⟨5497198901101885620006317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664799267401257080004211 5497198901101885620006317)
        ·
          refine ⟨2061449587913207107502369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5497198901101885620006317 2061449587913207107502369)
          ·
            refine ⟨1546087190934905330626777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2061449587913207107502369 1546087190934905330626777)
            ·
              refine ⟨1159565393201178997970083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546087190934905330626777 1159565393201178997970083)
              ·
                refine ⟨1739348089801768496955125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159565393201178997970083 1739348089801768496955125)
                ·
                  refine ⟨163063883418915796589543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739348089801768496955125 163063883418915796589543)
                  ·
                    rfl

theorem cell22_1429046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1429046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429046 prefixEnd_1429046 := by exact prefixLift 1429046
  have htrace : WordTrace (prefixWord ++ tailWord_1429046) baseStart_1429046 baseEnd_1429046 := by
    simpa [prefixWord, tailWord_1429046, baseEnd_1429046] using wordTrace_append hprefix tailTrace_1429046
  have hstable : (prefixWord ++ tailWord_1429046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429046).length < 2 ^ (prefixWord ++ tailWord_1429046).sum := by decide
  have hdescent : baseEnd_1429046 < baseStart_1429046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429117 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_1429117 : Nat := 118140960795 + 1429117 * 2 ^ 59
def prefixEnd_1429117 : Nat := 4983230072969 + 3 ^ 40 * 1429117 * 2
def baseEnd_1429117 : Nat := 489215955007726871243411

theorem tailTrace_1429117 : CollatzResearch.WordTrace tailWord_1429117 prefixEnd_1429117 489215955007726871243411 := by
  unfold tailWord_1429117
  simp only [CollatzResearch.WordTrace]
  refine ⟨52124179163560657597005605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34749452775707105064670403 52124179163560657597005605)
  ·
    refine ⟨9773283593167623299438551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52124179163560657597005605 9773283593167623299438551)
    ·
      refine ⟨14659925389751434949157827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773283593167623299438551 14659925389751434949157827)
      ·
        refine ⟨21989888084627152423736741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14659925389751434949157827 21989888084627152423736741)
        ·
          refine ⟨4123104015867591079450639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21989888084627152423736741 4123104015867591079450639)
          ·
            refine ⟨6184656023801386619175959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123104015867591079450639 6184656023801386619175959)
            ·
              refine ⟨9276984035702079928763939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184656023801386619175959 9276984035702079928763939)
              ·
                refine ⟨13915476053553119893145909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276984035702079928763939 13915476053553119893145909)
                ·
                  refine ⟨1304575880020604989982429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13915476053553119893145909 1304575880020604989982429)
                  ·
                    refine ⟨489215955007726871243411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304575880020604989982429 489215955007726871243411)
                    ·
                      rfl

theorem cell22_1429117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_1429117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429117 prefixEnd_1429117 := by exact prefixLift 1429117
  have htrace : WordTrace (prefixWord ++ tailWord_1429117) baseStart_1429117 baseEnd_1429117 := by
    simpa [prefixWord, tailWord_1429117, baseEnd_1429117] using wordTrace_append hprefix tailTrace_1429117
  have hstable : (prefixWord ++ tailWord_1429117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429117).length < 2 ^ (prefixWord ++ tailWord_1429117).sum := by decide
  have hdescent : baseEnd_1429117 < baseStart_1429117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429151 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 3, 3]
def baseStart_1429151 : Nat := 118140960795 + 1429151 * 2 ^ 59
def prefixEnd_1429151 : Nat := 4983230072969 + 3 ^ 40 * 1429151 * 2
def baseEnd_1429151 : Nat := 489227593902562115893307

theorem tailTrace_1429151 : CollatzResearch.WordTrace tailWord_1429151 prefixEnd_1429151 489227593902562115893307 := by
  unfold tailWord_1429151
  simp only [CollatzResearch.WordTrace]
  refine ⟨52125419245437481403743307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34750279496958320935828871 52125419245437481403743307)
  ·
    refine ⟨78188128868156222105614961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52125419245437481403743307 78188128868156222105614961)
    ·
      refine ⟨58641096651117166579211221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78188128868156222105614961 58641096651117166579211221)
      ·
        refine ⟨1374400702760558591700263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58641096651117166579211221 1374400702760558591700263)
        ·
          refine ⟨2061601054140837887550395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374400702760558591700263 2061601054140837887550395)
          ·
            refine ⟨3092401581211256831325593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061601054140837887550395 3092401581211256831325593)
            ·
              refine ⟨2319301185908442623494195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092401581211256831325593 2319301185908442623494195)
              ·
                refine ⟨3478951778862663935241293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319301185908442623494195 3478951778862663935241293)
                ·
                  refine ⟨1304606917073498975715485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3478951778862663935241293 1304606917073498975715485)
                  ·
                    refine ⟨489227593902562115893307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304606917073498975715485 489227593902562115893307)
                    ·
                      rfl

theorem cell22_1429151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_1429151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429151 prefixEnd_1429151 := by exact prefixLift 1429151
  have htrace : WordTrace (prefixWord ++ tailWord_1429151) baseStart_1429151 baseEnd_1429151 := by
    simpa [prefixWord, tailWord_1429151, baseEnd_1429151] using wordTrace_append hprefix tailTrace_1429151
  have hstable : (prefixWord ++ tailWord_1429151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429151).length < 2 ^ (prefixWord ++ tailWord_1429151).sum := by decide
  have hdescent : baseEnd_1429151 < baseStart_1429151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429177 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_1429177 : Nat := 118140960795 + 1429177 * 2 ^ 59
def prefixEnd_1429177 : Nat := 4983230072969 + 3 ^ 40 * 1429177 * 2
def baseEnd_1429177 : Nat := 489236494233906714743227

theorem tailTrace_1429177 : CollatzResearch.WordTrace tailWord_1429177 prefixEnd_1429177 489236494233906714743227 := by
  unfold tailWord_1429177
  simp only [CollatzResearch.WordTrace]
  refine ⟨52126367543343287844189785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34750911695562191896126523 52126367543343287844189785)
  ·
    refine ⟨39094775657507465883142339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52126367543343287844189785 39094775657507465883142339)
    ·
      refine ⟨58642163486261198824713509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39094775657507465883142339 58642163486261198824713509)
      ·
        refine ⟨10995405653673974779633783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58642163486261198824713509 10995405653673974779633783)
        ·
          refine ⟨16493108480510962169450675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995405653673974779633783 16493108480510962169450675)
          ·
            refine ⟨24739662720766443254176013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493108480510962169450675 24739662720766443254176013)
            ·
              refine ⟨9277373520287416220316005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24739662720766443254176013 9277373520287416220316005)
              ·
                refine ⟨1739507535053890541309251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9277373520287416220316005 1739507535053890541309251)
                ·
                  refine ⟨2609261302580835811963877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739507535053890541309251 2609261302580835811963877)
                  ·
                    refine ⟨489236494233906714743227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609261302580835811963877 489236494233906714743227)
                    ·
                      rfl

theorem cell22_1429177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_1429177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429177 prefixEnd_1429177 := by exact prefixLift 1429177
  have htrace : WordTrace (prefixWord ++ tailWord_1429177) baseStart_1429177 baseEnd_1429177 := by
    simpa [prefixWord, tailWord_1429177, baseEnd_1429177] using wordTrace_append hprefix tailTrace_1429177
  have hstable : (prefixWord ++ tailWord_1429177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429177).length < 2 ^ (prefixWord ++ tailWord_1429177).sum := by decide
  have hdescent : baseEnd_1429177 < baseStart_1429177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429207 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 4, 3]
def baseStart_1429207 : Nat := 118140960795 + 1429207 * 2 ^ 59
def prefixEnd_1429207 : Nat := 4983230072969 + 3 ^ 40 * 1429207 * 2
def baseEnd_1429207 : Nat := 489246763846996636493135

theorem tailTrace_1429207 : CollatzResearch.WordTrace tailWord_1429207 prefixEnd_1429207 489246763846996636493135 := by
  unfold tailWord_1429207
  simp only [CollatzResearch.WordTrace]
  refine ⟨52127461733234602967781875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34751641155489735311854583 52127461733234602967781875)
  ·
    refine ⟨78191192599851904451672813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52127461733234602967781875 78191192599851904451672813)
    ·
      refine ⟨29321697224944464169377305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78191192599851904451672813 29321697224944464169377305)
      ·
        refine ⟨21991272918708348127032979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29321697224944464169377305 21991272918708348127032979)
        ·
          refine ⟨32986909378062522190549469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21991272918708348127032979 32986909378062522190549469)
          ·
            refine ⟨12370091016773445821456051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32986909378062522190549469 12370091016773445821456051)
            ·
              refine ⟨18555136525160168732184077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12370091016773445821456051 18555136525160168732184077)
              ·
                refine ⟨6958176196935063274569029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18555136525160168732184077 6958176196935063274569029)
                ·
                  refine ⟨1304658036925324363981693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6958176196935063274569029 1304658036925324363981693)
                  ·
                    refine ⟨489246763846996636493135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304658036925324363981693 489246763846996636493135)
                    ·
                      rfl

theorem cell22_1429207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_1429207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429207 prefixEnd_1429207 := by exact prefixLift 1429207
  have htrace : WordTrace (prefixWord ++ tailWord_1429207) baseStart_1429207 baseEnd_1429207 := by
    simpa [prefixWord, tailWord_1429207, baseEnd_1429207] using wordTrace_append hprefix tailTrace_1429207
  have hstable : (prefixWord ++ tailWord_1429207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429207).length < 2 ^ (prefixWord ++ tailWord_1429207).sum := by decide
  have hdescent : baseEnd_1429207 < baseStart_1429207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429235 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_1429235 : Nat := 118140960795 + 1429235 * 2 ^ 59
def prefixEnd_1429235 : Nat := 4983230072969 + 3 ^ 40 * 1429235 * 2
def baseEnd_1429235 : Nat := 489256348819213896793049

theorem tailTrace_1429235 : CollatzResearch.WordTrace tailWord_1429235 prefixEnd_1429235 489256348819213896793049 := by
  unfold tailWord_1429235
  simp only [CollatzResearch.WordTrace]
  refine ⟨52128482977133163749801159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34752321984755442499867439 52128482977133163749801159)
  ·
    refine ⟨78192724465699745624701739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52128482977133163749801159 78192724465699745624701739)
    ·
      refine ⟨117289086698549618437052609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78192724465699745624701739 117289086698549618437052609)
      ·
        refine ⟨87966815023912213827789457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117289086698549618437052609 87966815023912213827789457)
        ·
          refine ⟨65975111267934160370842093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87966815023912213827789457 65975111267934160370842093)
          ·
            refine ⟨24740666725475310139065785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65975111267934160370842093 24740666725475310139065785)
            ·
              refine ⟨18555500044106482604299339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24740666725475310139065785 18555500044106482604299339)
              ·
                refine ⟨27833250066159723906449009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18555500044106482604299339 27833250066159723906449009)
                ·
                  refine ⟨20874937549619792929836757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27833250066159723906449009 20874937549619792929836757)
                  ·
                    refine ⟨489256348819213896793049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20874937549619792929836757 489256348819213896793049)
                    ·
                      rfl

theorem cell22_1429235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_1429235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429235 prefixEnd_1429235 := by exact prefixLift 1429235
  have htrace : WordTrace (prefixWord ++ tailWord_1429235) baseStart_1429235 baseEnd_1429235 := by
    simpa [prefixWord, tailWord_1429235, baseEnd_1429235] using wordTrace_append hprefix tailTrace_1429235
  have hstable : (prefixWord ++ tailWord_1429235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429235).length < 2 ^ (prefixWord ++ tailWord_1429235).sum := by decide
  have hdescent : baseEnd_1429235 < baseStart_1429235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429346 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1429346 : Nat := 118140960795 + 1429346 * 2 ^ 59
def prefixEnd_1429346 : Nat := 4983230072969 + 3 ^ 40 * 1429346 * 2
def baseEnd_1429346 : Nat := 489294346387646607267709

theorem tailTrace_1429346 : CollatzResearch.WordTrace tailWord_1429346 prefixEnd_1429346 489294346387646607267709 := by
  unfold tailWord_1429346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033132869932757426772973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34755020986487353138061261 13033132869932757426772973)
  ·
    refine ⟨4887424826224784035039865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13033132869932757426772973 4887424826224784035039865)
    ·
      refine ⟨3665568619668588026279899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4887424826224784035039865 3665568619668588026279899)
      ·
        refine ⟨5498352929502882039419849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665568619668588026279899 5498352929502882039419849)
        ·
          refine ⟨4123764697127161529564887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498352929502882039419849 4123764697127161529564887)
          ·
            refine ⟨6185647045690742294347331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123764697127161529564887 6185647045690742294347331)
            ·
              refine ⟨9278470568536113441520997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185647045690742294347331 9278470568536113441520997)
              ·
                refine ⟨1739713231600521270285187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9278470568536113441520997 1739713231600521270285187)
                ·
                  refine ⟨2609569847400781905427781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739713231600521270285187 2609569847400781905427781)
                  ·
                    refine ⟨489294346387646607267709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609569847400781905427781 489294346387646607267709)
                    ·
                      rfl

theorem cell22_1429346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1429346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429346 prefixEnd_1429346 := by exact prefixLift 1429346
  have htrace : WordTrace (prefixWord ++ tailWord_1429346) baseStart_1429346 baseEnd_1429346 := by
    simpa [prefixWord, tailWord_1429346, baseEnd_1429346] using wordTrace_append hprefix tailTrace_1429346
  have hstable : (prefixWord ++ tailWord_1429346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429346).length < 2 ^ (prefixWord ++ tailWord_1429346).sum := by decide
  have hdescent : baseEnd_1429346 < baseStart_1429346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429417 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 7]
def baseStart_1429417 : Nat := 118140960795 + 1429417 * 2 ^ 59
def prefixEnd_1429417 : Nat := 4983230072969 + 3 ^ 40 * 1429417 * 2
def baseEnd_1429417 : Nat := 163106217046208696247497

theorem tailTrace_1429417 : CollatzResearch.WordTrace tailWord_1429417 prefixEnd_1429417 163106217046208696247497 := by
  unfold tailWord_1429417
  simp only [CollatzResearch.WordTrace]
  refine ⟨52135121062473808832926505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34756747374982539221951003 52135121062473808832926505)
  ·
    refine ⟨39101340796855356624694879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52135121062473808832926505 39101340796855356624694879)
    ·
      refine ⟨58652011195283034937042319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39101340796855356624694879 58652011195283034937042319)
      ·
        refine ⟨87978016792924552405563479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58652011195283034937042319 87978016792924552405563479)
        ·
          refine ⟨131967025189386828608345219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87978016792924552405563479 131967025189386828608345219)
          ·
            refine ⟨197950537784080242912517829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131967025189386828608345219 197950537784080242912517829)
            ·
              refine ⟨37115725834515045546097093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197950537784080242912517829 37115725834515045546097093)
              ·
                refine ⟨6959198593971571039893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37115725834515045546097093 6959198593971571039893205)
                ·
                  refine ⟨163106217046208696247497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6959198593971571039893205 163106217046208696247497)
                  ·
                    rfl

theorem cell22_1429417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_1429417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429417 prefixEnd_1429417 := by exact prefixLift 1429417
  have htrace : WordTrace (prefixWord ++ tailWord_1429417) baseStart_1429417 baseEnd_1429417 := by
    simpa [prefixWord, tailWord_1429417, baseEnd_1429417] using wordTrace_append hprefix tailTrace_1429417
  have hstable : (prefixWord ++ tailWord_1429417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429417).length < 2 ^ (prefixWord ++ tailWord_1429417).sum := by decide
  have hdescent : baseEnd_1429417 < baseStart_1429417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429464 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1429464 : Nat := 118140960795 + 1429464 * 2 ^ 59
def prefixEnd_1429464 : Nat := 4983230072969 + 3 ^ 40 * 1429464 * 2
def baseEnd_1429464 : Nat := 489334740199133632817347

theorem tailTrace_1429464 : CollatzResearch.WordTrace tailWord_1429464 prefixEnd_1429464 489334740199133632817347 := by
  unfold tailWord_1429464
  simp only [CollatzResearch.WordTrace]
  refine ⟨26068417646651767929943723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34757890195535690573258297 26068417646651767929943723)
  ·
    refine ⟨39102626469977651894915585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26068417646651767929943723 39102626469977651894915585)
    ·
      refine ⟨29326969852483238921186689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39102626469977651894915585 29326969852483238921186689)
      ·
        refine ⟨21995227389362429190890017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29326969852483238921186689 21995227389362429190890017)
        ·
          refine ⟨16496420542021821893167513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21995227389362429190890017 16496420542021821893167513)
          ·
            refine ⟨12372315406516366419875635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16496420542021821893167513 12372315406516366419875635)
            ·
              refine ⟨18558473109774549629813453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12372315406516366419875635 18558473109774549629813453)
              ·
                refine ⟨6959427416165456111180045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18558473109774549629813453 6959427416165456111180045)
                ·
                  refine ⟨2609785281062046041692517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6959427416165456111180045 2609785281062046041692517)
                  ·
                    refine ⟨489334740199133632817347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609785281062046041692517 489334740199133632817347)
                    ·
                      rfl

theorem cell22_1429464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1429464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429464 prefixEnd_1429464 := by exact prefixLift 1429464
  have htrace : WordTrace (prefixWord ++ tailWord_1429464) baseStart_1429464 baseEnd_1429464 := by
    simpa [prefixWord, tailWord_1429464, baseEnd_1429464] using wordTrace_append hprefix tailTrace_1429464
  have hstable : (prefixWord ++ tailWord_1429464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429464).length < 2 ^ (prefixWord ++ tailWord_1429464).sum := by decide
  have hdescent : baseEnd_1429464 < baseStart_1429464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429485 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1429485 : Nat := 118140960795 + 1429485 * 2 ^ 59
def prefixEnd_1429485 : Nat := 4983230072969 + 3 ^ 40 * 1429485 * 2
def baseEnd_1429485 : Nat := 163113976309432192680761

theorem tailTrace_1429485 : CollatzResearch.WordTrace tailWord_1429485 prefixEnd_1429485 163113976309432192680761 := by
  unfold tailWord_1429485
  simp only [CollatzResearch.WordTrace]
  refine ⟨52137601226227456446401909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34758400817484970964267939 52137601226227456446401909)
  ·
    refine ⟨4887900114958824041850179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52137601226227456446401909 4887900114958824041850179)
    ·
      refine ⟨7331850172438236062775269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4887900114958824041850179 7331850172438236062775269)
      ·
        refine ⟨1374721907332169261770363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7331850172438236062775269 1374721907332169261770363)
        ·
          refine ⟨2062082860998253892655545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374721907332169261770363 2062082860998253892655545)
          ·
            refine ⟨1546562145748690419491659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062082860998253892655545 1546562145748690419491659)
            ·
              refine ⟨2319843218623035629237489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546562145748690419491659 2319843218623035629237489)
              ·
                refine ⟨1739882413967276721928117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319843218623035629237489 1739882413967276721928117)
                ·
                  refine ⟨163113976309432192680761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739882413967276721928117 163113976309432192680761)
                  ·
                    rfl

theorem cell22_1429485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1429485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429485 prefixEnd_1429485 := by exact prefixLift 1429485
  have htrace : WordTrace (prefixWord ++ tailWord_1429485) baseStart_1429485 baseEnd_1429485 := by
    simpa [prefixWord, tailWord_1429485, baseEnd_1429485] using wordTrace_append hprefix tailTrace_1429485
  have hstable : (prefixWord ++ tailWord_1429485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429485).length < 2 ^ (prefixWord ++ tailWord_1429485).sum := by decide
  have hdescent : baseEnd_1429485 < baseStart_1429485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429496 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_1429496 : Nat := 118140960795 + 1429496 * 2 ^ 59
def prefixEnd_1429496 : Nat := 4983230072969 + 3 ^ 40 * 1429496 * 2
def baseEnd_1429496 : Nat := 163115231484365405339083

theorem tailTrace_1429496 : CollatzResearch.WordTrace tailWord_1429496 prefixEnd_1429496 163115231484365405339083 := by
  unfold tailWord_1429496
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069001214593802662526171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34758668286125070216701561 26069001214593802662526171)
  ·
    refine ⟨39103501821890703993789257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26069001214593802662526171 39103501821890703993789257)
    ·
      refine ⟨29327626366418027995341943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39103501821890703993789257 29327626366418027995341943)
      ·
        refine ⟨43991439549627041993012915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29327626366418027995341943 43991439549627041993012915)
        ·
          refine ⟨65987159324440562989519373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43991439549627041993012915 65987159324440562989519373)
          ·
            refine ⟨24745184746665211121069765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65987159324440562989519373 24745184746665211121069765)
            ·
              refine ⟨4639722139999727085200581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24745184746665211121069765 4639722139999727085200581)
              ·
                refine ⟨869947901249948828475109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4639722139999727085200581 869947901249948828475109)
                ·
                  refine ⟨163115231484365405339083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869947901249948828475109 163115231484365405339083)
                  ·
                    rfl

theorem cell22_1429496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_1429496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429496 prefixEnd_1429496 := by exact prefixLift 1429496
  have htrace : WordTrace (prefixWord ++ tailWord_1429496) baseStart_1429496 baseEnd_1429496 := by
    simpa [prefixWord, tailWord_1429496, baseEnd_1429496] using wordTrace_append hprefix tailTrace_1429496
  have hstable : (prefixWord ++ tailWord_1429496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429496).length < 2 ^ (prefixWord ++ tailWord_1429496).sum := by decide
  have hdescent : baseEnd_1429496 < baseStart_1429496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429509 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1429509 : Nat := 118140960795 + 1429509 * 2 ^ 59
def prefixEnd_1429509 : Nat := 4983230072969 + 3 ^ 40 * 1429509 * 2
def baseEnd_1429509 : Nat := 489350144618768515442209

theorem tailTrace_1429509 : CollatzResearch.WordTrace tailWord_1429509 prefixEnd_1429509 489350144618768515442209 := by
  unfold tailWord_1429509
  simp only [CollatzResearch.WordTrace]
  refine ⟨52138476578140508545275581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34758984385427005696850387 52138476578140508545275581)
  ·
    refine ⟨19551928716802690704478343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52138476578140508545275581 19551928716802690704478343)
    ·
      refine ⟨29327893075204036056717515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19551928716802690704478343 29327893075204036056717515)
      ·
        refine ⟨43991839612806054085076273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29327893075204036056717515 43991839612806054085076273)
        ·
          refine ⟨32993879709604540563807205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43991839612806054085076273 32993879709604540563807205)
          ·
            refine ⟨6186352445550851355713851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32993879709604540563807205 6186352445550851355713851)
            ·
              refine ⟨9279528668326277033570777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186352445550851355713851 9279528668326277033570777)
              ·
                refine ⟨6959646501244707775178083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279528668326277033570777 6959646501244707775178083)
                ·
                  refine ⟨10439469751867061662767125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6959646501244707775178083 10439469751867061662767125)
                  ·
                    refine ⟨489350144618768515442209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10439469751867061662767125 489350144618768515442209)
                    ·
                      rfl

theorem cell22_1429509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1429509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429509 prefixEnd_1429509 := by exact prefixLift 1429509
  have htrace : WordTrace (prefixWord ++ tailWord_1429509) baseStart_1429509 baseEnd_1429509 := by
    simpa [prefixWord, tailWord_1429509, baseEnd_1429509] using wordTrace_append hprefix tailTrace_1429509
  have hstable : (prefixWord ++ tailWord_1429509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429509).length < 2 ^ (prefixWord ++ tailWord_1429509).sum := by decide
  have hdescent : baseEnd_1429509 < baseStart_1429509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429511 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1429511 : Nat := 118140960795 + 1429511 * 2 ^ 59
def prefixEnd_1429511 : Nat := 4983230072969 + 3 ^ 40 * 1429511 * 2
def baseEnd_1429511 : Nat := 489350829259641176892203

theorem tailTrace_1429511 : CollatzResearch.WordTrace tailWord_1429511 prefixEnd_1429511 489350829259641176892203 := by
  unfold tailWord_1429511
  simp only [CollatzResearch.WordTrace]
  refine ⟨52138549524133262886848387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34759033016088841924565591 52138549524133262886848387)
  ·
    refine ⟨78207824286199894330272581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52138549524133262886848387 78207824286199894330272581)
    ·
      refine ⟨14663967053662480186926109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78207824286199894330272581 14663967053662480186926109)
      ·
        refine ⟨5498987645123430070097291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14663967053662480186926109 5498987645123430070097291)
        ·
          refine ⟨8248481467685145105145937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498987645123430070097291 8248481467685145105145937)
          ·
            refine ⟨6186361100763858828859453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8248481467685145105145937 6186361100763858828859453)
            ·
              refine ⟨2319885412786447060822295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6186361100763858828859453 2319885412786447060822295)
              ·
                refine ⟨3479828119179670591233443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319885412786447060822295 3479828119179670591233443)
                ·
                  refine ⟨5219742178769505886850165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479828119179670591233443 5219742178769505886850165)
                  ·
                    refine ⟨489350829259641176892203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5219742178769505886850165 489350829259641176892203)
                    ·
                      rfl

theorem cell22_1429511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1429511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429511 prefixEnd_1429511 := by exact prefixLift 1429511
  have htrace : WordTrace (prefixWord ++ tailWord_1429511) baseStart_1429511 baseEnd_1429511 := by
    simpa [prefixWord, tailWord_1429511, baseEnd_1429511] using wordTrace_append hprefix tailTrace_1429511
  have hstable : (prefixWord ++ tailWord_1429511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429511).length < 2 ^ (prefixWord ++ tailWord_1429511).sum := by decide
  have hdescent : baseEnd_1429511 < baseStart_1429511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429584 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_1429584 : Nat := 118140960795 + 1429584 * 2 ^ 59
def prefixEnd_1429584 : Nat := 4983230072969 + 3 ^ 40 * 1429584 * 2
def baseEnd_1429584 : Nat := 489375818651493319816979

theorem tailTrace_1429584 : CollatzResearch.WordTrace tailWord_1429584 prefixEnd_1429584 489375818651493319816979 := by
  unfold tailWord_1429584
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070606026434398177127903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34760808035245864236170537 26070606026434398177127903)
  ·
    refine ⟨39105909039651597265691855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26070606026434398177127903 39105909039651597265691855)
    ·
      refine ⟨58658863559477395898537783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39105909039651597265691855 58658863559477395898537783)
      ·
        refine ⟨87988295339216093847806675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58658863559477395898537783 87988295339216093847806675)
        ·
          refine ⟨131982443008824140771710013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87988295339216093847806675 131982443008824140771710013)
          ·
            refine ⟨49493416128309052789391255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131982443008824140771710013 49493416128309052789391255)
            ·
              refine ⟨74240124192463579184086883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49493416128309052789391255 74240124192463579184086883)
              ·
                refine ⟨111360186288695368776130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74240124192463579184086883 111360186288695368776130325)
                ·
                  refine ⟨5220008732282595411381109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111360186288695368776130325 5220008732282595411381109)
                  ·
                    refine ⟨489375818651493319816979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5220008732282595411381109 489375818651493319816979)
                    ·
                      rfl

theorem cell22_1429584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_1429584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429584 prefixEnd_1429584 := by exact prefixLift 1429584
  have htrace : WordTrace (prefixWord ++ tailWord_1429584) baseStart_1429584 baseEnd_1429584 := by
    simpa [prefixWord, tailWord_1429584, baseEnd_1429584] using wordTrace_append hprefix tailTrace_1429584
  have hstable : (prefixWord ++ tailWord_1429584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429584).length < 2 ^ (prefixWord ++ tailWord_1429584).sum := by decide
  have hdescent : baseEnd_1429584 < baseStart_1429584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429616 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_1429616 : Nat := 118140960795 + 1429616 * 2 ^ 59
def prefixEnd_1429616 : Nat := 4983230072969 + 3 ^ 40 * 1429616 * 2
def baseEnd_1429616 : Nat := 489386772905455903016881

theorem tailTrace_1429616 : CollatzResearch.WordTrace tailWord_1429616 prefixEnd_1429616 489386772905455903016881 := by
  unfold tailWord_1429616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26071189594376432909710351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34761586125835243879613801 26071189594376432909710351)
  ·
    refine ⟨39106784391564649364565527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26071189594376432909710351 39106784391564649364565527)
    ·
      refine ⟨58660176587346974046848291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39106784391564649364565527 58660176587346974046848291)
      ·
        refine ⟨87990264881020461070272437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58660176587346974046848291 87990264881020461070272437)
        ·
          refine ⟨8249087332595668225338041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87990264881020461070272437 8249087332595668225338041)
          ·
            refine ⟨6186815499446751169003531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8249087332595668225338041 6186815499446751169003531)
            ·
              refine ⟨9280223249170126753505297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186815499446751169003531 9280223249170126753505297)
              ·
                refine ⟨6960167436877595065128973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9280223249170126753505297 6960167436877595065128973)
                ·
                  refine ⟨2610062788829098149423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6960167436877595065128973 2610062788829098149423365)
                  ·
                    refine ⟨489386772905455903016881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610062788829098149423365 489386772905455903016881)
                    ·
                      rfl

theorem cell22_1429616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_1429616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429616 prefixEnd_1429616 := by exact prefixLift 1429616
  have htrace : WordTrace (prefixWord ++ tailWord_1429616) baseStart_1429616 baseEnd_1429616 := by
    simpa [prefixWord, tailWord_1429616, baseEnd_1429616] using wordTrace_append hprefix tailTrace_1429616
  have hstable : (prefixWord ++ tailWord_1429616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429616).length < 2 ^ (prefixWord ++ tailWord_1429616).sum := by decide
  have hdescent : baseEnd_1429616 < baseStart_1429616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429648 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_1429648 : Nat := 118140960795 + 1429648 * 2 ^ 59
def prefixEnd_1429648 : Nat := 4983230072969 + 3 ^ 40 * 1429648 * 2
def baseEnd_1429648 : Nat := 163132575719806162072261

theorem tailTrace_1429648 : CollatzResearch.WordTrace tailWord_1429648 prefixEnd_1429648 163132575719806162072261 := by
  unfold tailWord_1429648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26071773162318467642292799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34762364216424623523057065 26071773162318467642292799)
  ·
    refine ⟨39107659743477701463439199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26071773162318467642292799 39107659743477701463439199)
    ·
      refine ⟨58661489615216552195158799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39107659743477701463439199 58661489615216552195158799)
      ·
        refine ⟨87992234422824828292738199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58661489615216552195158799 87992234422824828292738199)
        ·
          refine ⟨131988351634237242439107299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87992234422824828292738199 131988351634237242439107299)
          ·
            refine ⟨197982527451355863658660949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131988351634237242439107299 197982527451355863658660949)
            ·
              refine ⟨2320107743570576527249933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 197982527451355863658660949 2320107743570576527249933)
              ·
                refine ⟨870040403838966197718725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320107743570576527249933 870040403838966197718725)
                ·
                  refine ⟨163132575719806162072261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870040403838966197718725 163132575719806162072261)
                  ·
                    rfl

theorem cell22_1429648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_1429648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429648 prefixEnd_1429648 := by exact prefixLift 1429648
  have htrace : WordTrace (prefixWord ++ tailWord_1429648) baseStart_1429648 baseEnd_1429648 := by
    simpa [prefixWord, tailWord_1429648, baseEnd_1429648] using wordTrace_append hprefix tailTrace_1429648
  have hstable : (prefixWord ++ tailWord_1429648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429648).length < 2 ^ (prefixWord ++ tailWord_1429648).sum := by decide
  have hdescent : baseEnd_1429648 < baseStart_1429648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429654 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1429654 : Nat := 118140960795 + 1429654 * 2 ^ 59
def prefixEnd_1429654 : Nat := 4983230072969 + 3 ^ 40 * 1429654 * 2
def baseEnd_1429654 : Nat := 163133260360678823522255

theorem tailTrace_1429654 : CollatzResearch.WordTrace tailWord_1429654 prefixEnd_1429654 163133260360678823522255 := by
  unfold tailWord_1429654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258985322663449894331501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34762510108410132206202677 3258985322663449894331501)
  ·
    refine ⟨1222119495998793710374313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3258985322663449894331501 1222119495998793710374313)
    ·
      refine ⟨916589621999095282780735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1222119495998793710374313 916589621999095282780735)
      ·
        refine ⟨1374884432998642924171103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916589621999095282780735 1374884432998642924171103)
        ·
          refine ⟨2062326649497964386256655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374884432998642924171103 2062326649497964386256655)
          ·
            refine ⟨3093489974246946579384983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062326649497964386256655 3093489974246946579384983)
            ·
              refine ⟨4640234961370419869077475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093489974246946579384983 4640234961370419869077475)
              ·
                refine ⟨6960352442055629803616213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640234961370419869077475 6960352442055629803616213)
                ·
                  refine ⟨163133260360678823522255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6960352442055629803616213 163133260360678823522255)
                  ·
                    rfl

theorem cell22_1429654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1429654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429654 prefixEnd_1429654 := by exact prefixLift 1429654
  have htrace : WordTrace (prefixWord ++ tailWord_1429654) baseStart_1429654 baseEnd_1429654 := by
    simpa [prefixWord, tailWord_1429654, baseEnd_1429654] using wordTrace_append hprefix tailTrace_1429654
  have hstable : (prefixWord ++ tailWord_1429654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429654).length < 2 ^ (prefixWord ++ tailWord_1429654).sum := by decide
  have hdescent : baseEnd_1429654 < baseStart_1429654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429721 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 7]
def baseStart_1429721 : Nat := 118140960795 + 1429721 * 2 ^ 59
def prefixEnd_1429721 : Nat := 4983230072969 + 3 ^ 40 * 1429721 * 2
def baseEnd_1429721 : Nat := 163140905517090209713853

theorem tailTrace_1429721 : CollatzResearch.WordTrace tailWord_1429721 prefixEnd_1429721 163140905517090209713853 := by
  unfold tailWord_1429721
  simp only [CollatzResearch.WordTrace]
  refine ⟨52146208853372468751993017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34764139235581645834662011 52146208853372468751993017)
  ·
    refine ⟨39109656640029351563994763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52146208853372468751993017 39109656640029351563994763)
    ·
      refine ⟨58664484960044027345992145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39109656640029351563994763 58664484960044027345992145)
      ·
        refine ⟨43998363720033020509494109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58664484960044027345992145 43998363720033020509494109)
        ·
          refine ⟨16499386395012382691060291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43998363720033020509494109 16499386395012382691060291)
          ·
            refine ⟨24749079592518574036590437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16499386395012382691060291 24749079592518574036590437)
            ·
              refine ⟨4640452423597232631860707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24749079592518574036590437 4640452423597232631860707)
              ·
                refine ⟨6960678635395848947791061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640452423597232631860707 6960678635395848947791061)
                ·
                  refine ⟨163140905517090209713853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6960678635395848947791061 163140905517090209713853)
                  ·
                    rfl

theorem cell22_1429721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_1429721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429721 prefixEnd_1429721 := by exact prefixLift 1429721
  have htrace : WordTrace (prefixWord ++ tailWord_1429721) baseStart_1429721 baseEnd_1429721 := by
    simpa [prefixWord, tailWord_1429721, baseEnd_1429721] using wordTrace_append hprefix tailTrace_1429721
  have hstable : (prefixWord ++ tailWord_1429721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429721).length < 2 ^ (prefixWord ++ tailWord_1429721).sum := by decide
  have hdescent : baseEnd_1429721 < baseStart_1429721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429731 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 2, 3]
def baseStart_1429731 : Nat := 118140960795 + 1429731 * 2 ^ 59
def prefixEnd_1429731 : Nat := 4983230072969 + 3 ^ 40 * 1429731 * 2
def baseEnd_1429731 : Nat := 489426139755633936391529

theorem tailTrace_1429731 : CollatzResearch.WordTrace tailWord_1429731 prefixEnd_1429731 489426139755633936391529 := by
  unfold tailWord_1429731
  simp only [CollatzResearch.WordTrace]
  refine ⟨52146573583336240459857047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34764382388890826973238031 52146573583336240459857047)
  ·
    refine ⟨78219860375004360689785571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52146573583336240459857047 78219860375004360689785571)
    ·
      refine ⟨117329790562506541034678357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78219860375004360689785571 117329790562506541034678357)
      ·
        refine ⟨1374958483154373527750137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 117329790562506541034678357 1374958483154373527750137)
        ·
          refine ⟨1031218862365780145812603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1374958483154373527750137 1031218862365780145812603)
          ·
            refine ⟨1546828293548670218718905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031218862365780145812603 1546828293548670218718905)
            ·
              refine ⟨1160121220161502664039179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546828293548670218718905 1160121220161502664039179)
              ·
                refine ⟨1740181830242253996058769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160121220161502664039179 1740181830242253996058769)
                ·
                  refine ⟨1305136372681690497044077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740181830242253996058769 1305136372681690497044077)
                  ·
                    refine ⟨489426139755633936391529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305136372681690497044077 489426139755633936391529)
                    ·
                      rfl

theorem cell22_1429731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 3].length) (baseStart_1429731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429731 prefixEnd_1429731 := by exact prefixLift 1429731
  have htrace : WordTrace (prefixWord ++ tailWord_1429731) baseStart_1429731 baseEnd_1429731 := by
    simpa [prefixWord, tailWord_1429731, baseEnd_1429731] using wordTrace_append hprefix tailTrace_1429731
  have hstable : (prefixWord ++ tailWord_1429731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429731).length < 2 ^ (prefixWord ++ tailWord_1429731).sum := by decide
  have hdescent : baseEnd_1429731 < baseStart_1429731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429738 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_1429738 : Nat := 118140960795 + 1429738 * 2 ^ 59
def prefixEnd_1429738 : Nat := 4983230072969 + 3 ^ 40 * 1429738 * 2
def baseEnd_1429738 : Nat := 163142845332896083822169

theorem tailTrace_1429738 : CollatzResearch.WordTrace tailWord_1429738 prefixEnd_1429738 163142845332896083822169 := by
  unfold tailWord_1429738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036707223577720163840467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34764552596207253770241245 13036707223577720163840467)
  ·
    refine ⟨19555060835366580245760701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13036707223577720163840467 19555060835366580245760701)
    ·
      refine ⟨7333147813262467592160263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19555060835366580245760701 7333147813262467592160263)
      ·
        refine ⟨10999721719893701388240395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7333147813262467592160263 10999721719893701388240395)
        ·
          refine ⟨16499582579840552082360593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999721719893701388240395 16499582579840552082360593)
          ·
            refine ⟨12374686934880414061770445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16499582579840552082360593 12374686934880414061770445)
            ·
              refine ⟨4640507600580155273163917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12374686934880414061770445 4640507600580155273163917)
              ·
                refine ⟨1740190350217558227436469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640507600580155273163917 1740190350217558227436469)
                ·
                  refine ⟨163142845332896083822169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1740190350217558227436469 163142845332896083822169)
                  ·
                    rfl

theorem cell22_1429738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_1429738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429738 prefixEnd_1429738 := by exact prefixLift 1429738
  have htrace : WordTrace (prefixWord ++ tailWord_1429738) baseStart_1429738 baseEnd_1429738 := by
    simpa [prefixWord, tailWord_1429738, baseEnd_1429738] using wordTrace_append hprefix tailTrace_1429738
  have hstable : (prefixWord ++ tailWord_1429738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429738).length < 2 ^ (prefixWord ++ tailWord_1429738).sum := by decide
  have hdescent : baseEnd_1429738 < baseStart_1429738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429800 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_1429800 : Nat := 118140960795 + 1429800 * 2 ^ 59
def prefixEnd_1429800 : Nat := 4983230072969 + 3 ^ 40 * 1429800 * 2
def baseEnd_1429800 : Nat := 163149919955246918805439

theorem tailTrace_1429800 : CollatzResearch.WordTrace tailWord_1429800 prefixEnd_1429800 163149919955246918805439 := by
  unfold tailWord_1429800
  simp only [CollatzResearch.WordTrace]
  refine ⟨26074545110043132622059427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34766060146724176829412569 26074545110043132622059427)
  ·
    refine ⟨39111817665064698933089141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26074545110043132622059427 39111817665064698933089141)
    ·
      refine ⟨3666732906099815524977107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39111817665064698933089141 3666732906099815524977107)
      ·
        refine ⟨5500099359149723287465661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666732906099815524977107 5500099359149723287465661)
        ·
          refine ⟨2062537259681146232799623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5500099359149723287465661 2062537259681146232799623)
          ·
            refine ⟨3093805889521719349199435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062537259681146232799623 3093805889521719349199435)
            ·
              refine ⟨4640708834282579023799153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093805889521719349199435 4640708834282579023799153)
              ·
                refine ⟨3480531625711934267849365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640708834282579023799153 3480531625711934267849365)
                ·
                  refine ⟨163149919955246918805439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3480531625711934267849365 163149919955246918805439)
                  ·
                    rfl

theorem cell22_1429800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_1429800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429800 prefixEnd_1429800 := by exact prefixLift 1429800
  have htrace : WordTrace (prefixWord ++ tailWord_1429800) baseStart_1429800 baseEnd_1429800 := by
    simpa [prefixWord, tailWord_1429800, baseEnd_1429800] using wordTrace_append hprefix tailTrace_1429800
  have hstable : (prefixWord ++ tailWord_1429800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429800).length < 2 ^ (prefixWord ++ tailWord_1429800).sum := by decide
  have hdescent : baseEnd_1429800 < baseStart_1429800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429813 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1429813 : Nat := 118140960795 + 1429813 * 2 ^ 59
def prefixEnd_1429813 : Nat := 4983230072969 + 3 ^ 40 * 1429813 * 2
def baseEnd_1429813 : Nat := 489454210031413055841277

theorem tailTrace_1429813 : CollatzResearch.WordTrace tailWord_1429813 prefixEnd_1429813 489454210031413055841277 := by
  unfold tailWord_1429813
  simp only [CollatzResearch.WordTrace]
  refine ⟨52149564369039168464342093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34766376246026112309561395 52149564369039168464342093)
  ·
    refine ⟨19556086638389688174128285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52149564369039168464342093 19556086638389688174128285)
    ·
      refine ⟨7333532489396133065298107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19556086638389688174128285 7333532489396133065298107)
      ·
        refine ⟨11000298734094199597947161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7333532489396133065298107 11000298734094199597947161)
        ·
          refine ⟨8250224050570649698460371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11000298734094199597947161 8250224050570649698460371)
          ·
            refine ⟨12375336075855974547690557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250224050570649698460371 12375336075855974547690557)
            ·
              refine ⟨4640751028445990455383959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12375336075855974547690557 4640751028445990455383959)
              ·
                refine ⟨6961126542668985683075939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640751028445990455383959 6961126542668985683075939)
                ·
                  refine ⟨10441689814003478524613909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961126542668985683075939 10441689814003478524613909)
                  ·
                    refine ⟨489454210031413055841277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10441689814003478524613909 489454210031413055841277)
                    ·
                      rfl

theorem cell22_1429813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1429813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429813 prefixEnd_1429813 := by exact prefixLift 1429813
  have htrace : WordTrace (prefixWord ++ tailWord_1429813) baseStart_1429813 baseEnd_1429813 := by
    simpa [prefixWord, tailWord_1429813, baseEnd_1429813] using wordTrace_append hprefix tailTrace_1429813
  have hstable : (prefixWord ++ tailWord_1429813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429813).length < 2 ^ (prefixWord ++ tailWord_1429813).sum := by decide
  have hdescent : baseEnd_1429813 < baseStart_1429813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429817 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 4]
def baseStart_1429817 : Nat := 118140960795 + 1429817 * 2 ^ 59
def prefixEnd_1429817 : Nat := 4983230072969 + 3 ^ 40 * 1429817 * 2
def baseEnd_1429817 : Nat := 163151859771052792913755

theorem tailTrace_1429817 : CollatzResearch.WordTrace tailWord_1429817 prefixEnd_1429817 163151859771052792913755 := by
  unfold tailWord_1429817
  simp only [CollatzResearch.WordTrace]
  refine ⟨52149710261024677147487705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34766473507349784764991803 52149710261024677147487705)
  ·
    refine ⟨39112282695768507860615779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52149710261024677147487705 39112282695768507860615779)
    ·
      refine ⟨58668424043652761790923669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39112282695768507860615779 58668424043652761790923669)
      ·
        refine ⟨2750082377046223208949547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58668424043652761790923669 2750082377046223208949547)
        ·
          refine ⟨4125123565569334813424321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750082377046223208949547 4125123565569334813424321)
          ·
            refine ⟨3093842674177001110068241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125123565569334813424321 3093842674177001110068241)
            ·
              refine ⟨2320382005632750832551181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093842674177001110068241 2320382005632750832551181)
              ·
                refine ⟨870143252112281562206693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320382005632750832551181 870143252112281562206693)
                ·
                  refine ⟨163151859771052792913755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870143252112281562206693 163151859771052792913755)
                  ·
                    rfl

theorem cell22_1429817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_1429817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429817 prefixEnd_1429817 := by exact prefixLift 1429817
  have htrace : WordTrace (prefixWord ++ tailWord_1429817) baseStart_1429817 baseEnd_1429817 := by
    simpa [prefixWord, tailWord_1429817, baseEnd_1429817] using wordTrace_append hprefix tailTrace_1429817
  have hstable : (prefixWord ++ tailWord_1429817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429817).length < 2 ^ (prefixWord ++ tailWord_1429817).sum := by decide
  have hdescent : baseEnd_1429817 < baseStart_1429817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429860 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1429860 : Nat := 118140960795 + 1429860 * 2 ^ 59
def prefixEnd_1429860 : Nat := 4983230072969 + 3 ^ 40 * 1429860 * 2
def baseEnd_1429860 : Nat := 489470299091920599916133

theorem tailTrace_1429860 : CollatzResearch.WordTrace tailWord_1429860 prefixEnd_1429860 489470299091920599916133 := by
  unfold tailWord_1429860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26075639299934447745651517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34767519066579263660868689 26075639299934447745651517)
  ·
    refine ⟨9778364737475417904619319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26075639299934447745651517 9778364737475417904619319)
    ·
      refine ⟨14667547106213126856928979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778364737475417904619319 14667547106213126856928979)
      ·
        refine ⟨22001320659319690285393469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14667547106213126856928979 22001320659319690285393469)
        ·
          refine ⟨8250495247244883857022551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22001320659319690285393469 8250495247244883857022551)
          ·
            refine ⟨12375742870867325785533827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250495247244883857022551 12375742870867325785533827)
            ·
              refine ⟨18563614306300988678300741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12375742870867325785533827 18563614306300988678300741)
              ·
                refine ⟨3480677682431435377181389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18563614306300988678300741 3480677682431435377181389)
                ·
                  refine ⟨1305254130911788266443021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3480677682431435377181389 1305254130911788266443021)
                  ·
                    refine ⟨489470299091920599916133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305254130911788266443021 489470299091920599916133)
                    ·
                      rfl

theorem cell22_1429860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1429860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429860 prefixEnd_1429860 := by exact prefixLift 1429860
  have htrace : WordTrace (prefixWord ++ tailWord_1429860) baseStart_1429860 baseEnd_1429860 := by
    simpa [prefixWord, tailWord_1429860, baseEnd_1429860] using wordTrace_append hprefix tailTrace_1429860
  have hstable : (prefixWord ++ tailWord_1429860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429860).length < 2 ^ (prefixWord ++ tailWord_1429860).sum := by decide
  have hdescent : baseEnd_1429860 < baseStart_1429860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429920 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_1429920 : Nat := 118140960795 + 1429920 * 2 ^ 59
def prefixEnd_1429920 : Nat := 4983230072969 + 3 ^ 40 * 1429920 * 2
def baseEnd_1429920 : Nat := 489490838318100443415949

theorem tailTrace_1429920 : CollatzResearch.WordTrace tailWord_1429920 prefixEnd_1429920 489490838318100443415949 := by
  unfold tailWord_1429920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26076733489825762869243607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34768977986434350492324809 26076733489825762869243607)
  ·
    refine ⟨39115100234738644303865411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26076733489825762869243607 39115100234738644303865411)
    ·
      refine ⟨58672650352107966455798117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39115100234738644303865411 58672650352107966455798117)
      ·
        refine ⟨11001121941020243710462147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58672650352107966455798117 11001121941020243710462147)
        ·
          refine ⟨16501682911530365565693221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11001121941020243710462147 16501682911530365565693221)
          ·
            refine ⟨3094065545911943543567479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16501682911530365565693221 3094065545911943543567479)
            ·
              refine ⟨4641098318867915315351219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094065545911943543567479 4641098318867915315351219)
              ·
                refine ⟨6961647478301872973026829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641098318867915315351219 6961647478301872973026829)
                ·
                  refine ⟨2610617804363202364885061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6961647478301872973026829 2610617804363202364885061)
                  ·
                    refine ⟨489490838318100443415949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610617804363202364885061 489490838318100443415949)
                    ·
                      rfl

theorem cell22_1429920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_1429920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429920 prefixEnd_1429920 := by exact prefixLift 1429920
  have htrace : WordTrace (prefixWord ++ tailWord_1429920) baseStart_1429920 baseEnd_1429920 := by
    simpa [prefixWord, tailWord_1429920, baseEnd_1429920] using wordTrace_append hprefix tailTrace_1429920
  have hstable : (prefixWord ++ tailWord_1429920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429920).length < 2 ^ (prefixWord ++ tailWord_1429920).sum := by decide
  have hdescent : baseEnd_1429920 < baseStart_1429920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429993 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_1429993 : Nat := 118140960795 + 1429993 * 2 ^ 59
def prefixEnd_1429993 : Nat := 4983230072969 + 3 ^ 40 * 1429993 * 2
def baseEnd_1429993 : Nat := 489515827709952586340725

theorem tailTrace_1429993 : CollatzResearch.WordTrace tailWord_1429993 prefixEnd_1429993 489515827709952586340725 := by
  unfold tailWord_1429993
  simp only [CollatzResearch.WordTrace]
  refine ⟨52156129508387059205894633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34770753005591372803929755 52156129508387059205894633)
  ·
    refine ⟨39117097131290294404420975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52156129508387059205894633 39117097131290294404420975)
    ·
      refine ⟨58675645696935441606631463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39117097131290294404420975 58675645696935441606631463)
      ·
        refine ⟨88013468545403162409947195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58675645696935441606631463 88013468545403162409947195)
        ·
          refine ⟨132020202818104743614920793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88013468545403162409947195 132020202818104743614920793)
          ·
            refine ⟨99015152113578557711190595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132020202818104743614920793 99015152113578557711190595)
            ·
              refine ⟨148522728170367836566785893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99015152113578557711190595 148522728170367836566785893)
              ·
                refine ⟨27848011531943969356272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148522728170367836566785893 27848011531943969356272355)
                ·
                  refine ⟨41772017297915954034408533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27848011531943969356272355 41772017297915954034408533)
                  ·
                    refine ⟨489515827709952586340725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41772017297915954034408533 489515827709952586340725)
                    ·
                      rfl

theorem cell22_1429993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_1429993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429993 prefixEnd_1429993 := by exact prefixLift 1429993
  have htrace : WordTrace (prefixWord ++ tailWord_1429993) baseStart_1429993 baseEnd_1429993 := by
    simpa [prefixWord, tailWord_1429993, baseEnd_1429993] using wordTrace_append hprefix tailTrace_1429993
  have hstable : (prefixWord ++ tailWord_1429993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429993).length < 2 ^ (prefixWord ++ tailWord_1429993).sum := by decide
  have hdescent : baseEnd_1429993 < baseStart_1429993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429995 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 5, 3]
def baseStart_1429995 : Nat := 118140960795 + 1429995 * 2 ^ 59
def prefixEnd_1429995 : Nat := 4983230072969 + 3 ^ 40 * 1429995 * 2
def baseEnd_1429995 : Nat := 489516512350825247790719

theorem tailTrace_1429995 : CollatzResearch.WordTrace tailWord_1429995 prefixEnd_1429995 489516512350825247790719 := by
  unfold tailWord_1429995
  simp only [CollatzResearch.WordTrace]
  refine ⟨52156202454379813547467439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34770801636253209031644959 52156202454379813547467439)
  ·
    refine ⟨78234303681569720321201159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52156202454379813547467439 78234303681569720321201159)
    ·
      refine ⟨117351455522354580481801739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78234303681569720321201159 117351455522354580481801739)
      ·
        refine ⟨176027183283531870722702609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117351455522354580481801739 176027183283531870722702609)
        ·
          refine ⟨132020387462648903042026957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176027183283531870722702609 132020387462648903042026957)
          ·
            refine ⟨49507645298493338640760109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132020387462648903042026957 49507645298493338640760109)
            ·
              refine ⟨18565366986935001990285041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49507645298493338640760109 18565366986935001990285041)
              ·
                refine ⟨13924025240201251492713781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18565366986935001990285041 13924025240201251492713781)
                ·
                  refine ⟨1305377366268867327441917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13924025240201251492713781 1305377366268867327441917)
                  ·
                    refine ⟨489516512350825247790719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305377366268867327441917 489516512350825247790719)
                    ·
                      rfl

theorem cell22_1429995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3].length) (baseStart_1429995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1429995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1429995 prefixEnd_1429995 := by exact prefixLift 1429995
  have htrace : WordTrace (prefixWord ++ tailWord_1429995) baseStart_1429995 baseEnd_1429995 := by
    simpa [prefixWord, tailWord_1429995, baseEnd_1429995] using wordTrace_append hprefix tailTrace_1429995
  have hstable : (prefixWord ++ tailWord_1429995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429995).length < 2 ^ (prefixWord ++ tailWord_1429995).sum := by decide
  have hdescent : baseEnd_1429995 < baseStart_1429995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430018 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1430018 : Nat := 118140960795 + 1430018 * 2 ^ 59
def prefixEnd_1430018 : Nat := 4983230072969 + 3 ^ 40 * 1430018 * 2
def baseEnd_1430018 : Nat := 489524385720860854465649

theorem tailTrace_1430018 : CollatzResearch.WordTrace tailWord_1430018 prefixEnd_1430018 489524385720860854465649 := by
  unfold tailWord_1430018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039260333324122118888677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34771360888864325650369805 13039260333324122118888677)
  ·
    refine ⟨2444861312498272897291627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13039260333324122118888677 2444861312498272897291627)
    ·
      refine ⟨3667291968747409345937441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444861312498272897291627 3667291968747409345937441)
      ·
        refine ⟨2750468976560557009453081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3667291968747409345937441 2750468976560557009453081)
        ·
          refine ⟨2062851732420417757089811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750468976560557009453081 2062851732420417757089811)
          ·
            refine ⟨3094277598630626635634717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062851732420417757089811 3094277598630626635634717)
            ·
              refine ⟨1160354099486484988363019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3094277598630626635634717 1160354099486484988363019)
              ·
                refine ⟨1740531149229727482544529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160354099486484988363019 1740531149229727482544529)
                ·
                  refine ⟨1305398361922295611908397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740531149229727482544529 1305398361922295611908397)
                  ·
                    refine ⟨489524385720860854465649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305398361922295611908397 489524385720860854465649)
                    ·
                      rfl

theorem cell22_1430018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1430018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430018 prefixEnd_1430018 := by exact prefixLift 1430018
  have htrace : WordTrace (prefixWord ++ tailWord_1430018) baseStart_1430018 baseEnd_1430018 := by
    simpa [prefixWord, tailWord_1430018, baseEnd_1430018] using wordTrace_append hprefix tailTrace_1430018
  have hstable : (prefixWord ++ tailWord_1430018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430018).length < 2 ^ (prefixWord ++ tailWord_1430018).sum := by decide
  have hdescent : baseEnd_1430018 < baseStart_1430018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430147 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 5, 3]
def baseStart_1430147 : Nat := 118140960795 + 1430147 * 2 ^ 59
def prefixEnd_1430147 : Nat := 4983230072969 + 3 ^ 40 * 1430147 * 2
def baseEnd_1430147 : Nat := 489568545057147517990253

theorem tailTrace_1430147 : CollatzResearch.WordTrace tailWord_1430147 prefixEnd_1430147 489568545057147517990253 := by
  unfold tailWord_1430147
  simp only [CollatzResearch.WordTrace]
  refine ⟨52161746349829143507000695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34774497566552762338000463 52161746349829143507000695)
  ·
    refine ⟨78242619524743715260501043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52161746349829143507000695 78242619524743715260501043)
    ·
      refine ⟨117363929287115572890751565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78242619524743715260501043 117363929287115572890751565)
      ·
        refine ⟨44011473482668339834031837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117363929287115572890751565 44011473482668339834031837)
        ·
          refine ⟨16504302556000627437761939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44011473482668339834031837 16504302556000627437761939)
          ·
            refine ⟨24756453834000941156642909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16504302556000627437761939 24756453834000941156642909)
            ·
              refine ⟨9283670187750352933741091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24756453834000941156642909 9283670187750352933741091)
              ·
                refine ⟨13925505281625529400611637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9283670187750352933741091 13925505281625529400611637)
                ·
                  refine ⟨1305516120152393381307341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13925505281625529400611637 1305516120152393381307341)
                  ·
                    refine ⟨489568545057147517990253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305516120152393381307341 489568545057147517990253)
                    ·
                      rfl

theorem cell22_1430147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3].length) (baseStart_1430147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430147 prefixEnd_1430147 := by exact prefixLift 1430147
  have htrace : WordTrace (prefixWord ++ tailWord_1430147) baseStart_1430147 baseEnd_1430147 := by
    simpa [prefixWord, tailWord_1430147, baseEnd_1430147] using wordTrace_append hprefix tailTrace_1430147
  have hstable : (prefixWord ++ tailWord_1430147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430147).length < 2 ^ (prefixWord ++ tailWord_1430147).sum := by decide
  have hdescent : baseEnd_1430147 < baseStart_1430147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430170 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_1430170 : Nat := 118140960795 + 1430170 * 2 ^ 59
def prefixEnd_1430170 : Nat := 4983230072969 + 3 ^ 40 * 1430170 * 2
def baseEnd_1430170 : Nat := 489576418427183124665183

theorem tailTrace_1430170 : CollatzResearch.WordTrace tailWord_1430170 prefixEnd_1430170 489576418427183124665183 := by
  unfold tailWord_1430170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040646307186454608771991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34775056819163878956725309 13040646307186454608771991)
  ·
    refine ⟨19560969460779681913157987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13040646307186454608771991 19560969460779681913157987)
    ·
      refine ⟨29341454191169522869736981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19560969460779681913157987 29341454191169522869736981)
      ·
        refine ⟨1375380665211071384518921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29341454191169522869736981 1375380665211071384518921)
        ·
          refine ⟨1031535498908303538389191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375380665211071384518921 1031535498908303538389191)
          ·
            refine ⟨1547303248362455307583787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031535498908303538389191 1547303248362455307583787)
            ·
              refine ⟨2320954872543682961375681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547303248362455307583787 2320954872543682961375681)
              ·
                refine ⟨1740716154407762221031761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320954872543682961375681 1740716154407762221031761)
                ·
                  refine ⟨1305537115805821665773821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740716154407762221031761 1305537115805821665773821)
                  ·
                    refine ⟨489576418427183124665183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305537115805821665773821 489576418427183124665183)
                    ·
                      rfl

theorem cell22_1430170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_1430170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430170 prefixEnd_1430170 := by exact prefixLift 1430170
  have htrace : WordTrace (prefixWord ++ tailWord_1430170) baseStart_1430170 baseEnd_1430170 := by
    simpa [prefixWord, tailWord_1430170, baseEnd_1430170] using wordTrace_append hprefix tailTrace_1430170
  have hstable : (prefixWord ++ tailWord_1430170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430170).length < 2 ^ (prefixWord ++ tailWord_1430170).sum := by decide
  have hdescent : baseEnd_1430170 < baseStart_1430170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430239 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 6]
def baseStart_1430239 : Nat := 118140960795 + 1430239 * 2 ^ 59
def prefixEnd_1430239 : Nat := 4983230072969 + 3 ^ 40 * 1430239 * 2
def baseEnd_1430239 : Nat := 163200012845763314896657

theorem tailTrace_1430239 : CollatzResearch.WordTrace tailWord_1430239 prefixEnd_1430239 163200012845763314896657 := by
  unfold tailWord_1430239
  simp only [CollatzResearch.WordTrace]
  refine ⟨52165101865495843219349771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34776734576997228812899847 52165101865495843219349771)
  ·
    refine ⟨78247652798243764829024657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52165101865495843219349771 78247652798243764829024657)
    ·
      refine ⟨58685739598682823621768493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78247652798243764829024657 58685739598682823621768493)
      ·
        refine ⟨22007152349506058858163185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58685739598682823621768493 22007152349506058858163185)
        ·
          refine ⟨16505364262129544143622389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22007152349506058858163185 16505364262129544143622389)
          ·
            refine ⟨1547377899574644763464599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16505364262129544143622389 1547377899574644763464599)
            ·
              refine ⟨2321066849361967145196899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547377899574644763464599 2321066849361967145196899)
              ·
                refine ⟨3481600274042950717795349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321066849361967145196899 3481600274042950717795349)
                ·
                  refine ⟨163200012845763314896657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3481600274042950717795349 163200012845763314896657)
                  ·
                    rfl

theorem cell22_1430239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 6].length) (baseStart_1430239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430239 prefixEnd_1430239 := by exact prefixLift 1430239
  have htrace : WordTrace (prefixWord ++ tailWord_1430239) baseStart_1430239 baseEnd_1430239 := by
    simpa [prefixWord, tailWord_1430239, baseEnd_1430239] using wordTrace_append hprefix tailTrace_1430239
  have hstable : (prefixWord ++ tailWord_1430239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430239).length < 2 ^ (prefixWord ++ tailWord_1430239).sum := by decide
  have hdescent : baseEnd_1430239 < baseStart_1430239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430252 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1430252 : Nat := 118140960795 + 1430252 * 2 ^ 59
def prefixEnd_1430252 : Nat := 4983230072969 + 3 ^ 40 * 1430252 * 2
def baseEnd_1430252 : Nat := 489604488702962244114931

theorem tailTrace_1430252 : CollatzResearch.WordTrace tailWord_1430252 prefixEnd_1430252 489604488702962244114931 := by
  unfold tailWord_1430252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26082788007224373219786505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34777050676299164293048673 26082788007224373219786505)
  ·
    refine ⟨19562091005418279914839879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26082788007224373219786505 19562091005418279914839879)
    ·
      refine ⟨29343136508127419872259819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19562091005418279914839879 29343136508127419872259819)
      ·
        refine ⟨44014704762191129808389729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29343136508127419872259819 44014704762191129808389729)
        ·
          refine ⟨33011028571643347356292297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44014704762191129808389729 33011028571643347356292297)
          ·
            refine ⟨24758271428732510517219223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33011028571643347356292297 24758271428732510517219223)
            ·
              refine ⟨37137407143098765775828835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24758271428732510517219223 37137407143098765775828835)
              ·
                refine ⟨55706110714648148663743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37137407143098765775828835 55706110714648148663743253)
                ·
                  refine ⟨2611223939749131968612965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55706110714648148663743253 2611223939749131968612965)
                  ·
                    refine ⟨489604488702962244114931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611223939749131968612965 489604488702962244114931)
                    ·
                      rfl

theorem cell22_1430252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1430252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430252 prefixEnd_1430252 := by exact prefixLift 1430252
  have htrace : WordTrace (prefixWord ++ tailWord_1430252) baseStart_1430252 baseEnd_1430252 := by
    simpa [prefixWord, tailWord_1430252, baseEnd_1430252] using wordTrace_append hprefix tailTrace_1430252
  have hstable : (prefixWord ++ tailWord_1430252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430252).length < 2 ^ (prefixWord ++ tailWord_1430252).sum := by decide
  have hdescent : baseEnd_1430252 < baseStart_1430252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430269 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1430269 : Nat := 118140960795 + 1430269 * 2 ^ 59
def prefixEnd_1430269 : Nat := 4983230072969 + 3 ^ 40 * 1430269 * 2
def baseEnd_1430269 : Nat := 489610308150379866439879

theorem tailTrace_1430269 : CollatzResearch.WordTrace tailWord_1430269 prefixEnd_1430269 489610308150379866439879 := by
  unfold tailWord_1430269
  simp only [CollatzResearch.WordTrace]
  refine ⟨52166196055387158342941861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34777464036924772228627907 52166196055387158342941861)
  ·
    refine ⟨9781161760385092189301599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52166196055387158342941861 9781161760385092189301599)
    ·
      refine ⟨14671742640577638283952399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9781161760385092189301599 14671742640577638283952399)
      ·
        refine ⟨22007613960866457425928599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14671742640577638283952399 22007613960866457425928599)
        ·
          refine ⟨33011420941299686138892899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22007613960866457425928599 33011420941299686138892899)
          ·
            refine ⟨49517131411949529208339349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33011420941299686138892899 49517131411949529208339349)
            ·
              refine ⟨2321115534935134181640907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49517131411949529208339349 2321115534935134181640907)
              ·
                refine ⟨3481673302402701272461361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321115534935134181640907 3481673302402701272461361)
                ·
                  refine ⟨2611254976802025954346021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3481673302402701272461361 2611254976802025954346021)
                  ·
                    refine ⟨489610308150379866439879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611254976802025954346021 489610308150379866439879)
                    ·
                      rfl

theorem cell22_1430269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1430269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430269 prefixEnd_1430269 := by exact prefixLift 1430269
  have htrace : WordTrace (prefixWord ++ tailWord_1430269) baseStart_1430269 baseEnd_1430269 := by
    simpa [prefixWord, tailWord_1430269, baseEnd_1430269] using wordTrace_append hprefix tailTrace_1430269
  have hstable : (prefixWord ++ tailWord_1430269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430269).length < 2 ^ (prefixWord ++ tailWord_1430269).sum := by decide
  have hdescent : baseEnd_1430269 < baseStart_1430269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430327 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1430327 : Nat := 118140960795 + 1430327 * 2 ^ 59
def prefixEnd_1430327 : Nat := 4983230072969 + 3 ^ 40 * 1430327 * 2
def baseEnd_1430327 : Nat := 489630162735687048489701

theorem tailTrace_1430327 : CollatzResearch.WordTrace tailWord_1430327 prefixEnd_1430327 489630162735687048489701 := by
  unfold tailWord_1430327
  simp only [CollatzResearch.WordTrace]
  refine ⟨52168311489177034248553235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34778874326118022832368823 52168311489177034248553235)
  ·
    refine ⟨78252467233765551372829853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52168311489177034248553235 78252467233765551372829853)
    ·
      refine ⟨29344675212662081764811195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78252467233765551372829853 29344675212662081764811195)
      ·
        refine ⟨44017012818993122647216793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29344675212662081764811195 44017012818993122647216793)
        ·
          refine ⟨33012759614244841985412595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44017012818993122647216793 33012759614244841985412595)
          ·
            refine ⟨49519139421367262978118893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33012759614244841985412595 49519139421367262978118893)
            ·
              refine ⟨18569677283012723616794585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49519139421367262978118893 18569677283012723616794585)
              ·
                refine ⟨13927257962259542712595939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18569677283012723616794585 13927257962259542712595939)
                ·
                  refine ⟨20890886943389314068893909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13927257962259542712595939 20890886943389314068893909)
                  ·
                    refine ⟨489630162735687048489701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20890886943389314068893909 489630162735687048489701)
                    ·
                      rfl

theorem cell22_1430327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1430327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430327 prefixEnd_1430327 := by exact prefixLift 1430327
  have htrace : WordTrace (prefixWord ++ tailWord_1430327) baseStart_1430327 baseEnd_1430327 := by
    simpa [prefixWord, tailWord_1430327, baseEnd_1430327] using wordTrace_append hprefix tailTrace_1430327
  have hstable : (prefixWord ++ tailWord_1430327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430327).length < 2 ^ (prefixWord ++ tailWord_1430327).sum := by decide
  have hdescent : baseEnd_1430327 < baseStart_1430327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430376 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1430376 : Nat := 118140960795 + 1430376 * 2 ^ 59
def prefixEnd_1430376 : Nat := 4983230072969 + 3 ^ 40 * 1430376 * 2
def baseEnd_1430376 : Nat := 489646936437067254014551

theorem tailTrace_1430376 : CollatzResearch.WordTrace tailWord_1430376 prefixEnd_1430376 489646936437067254014551 := by
  unfold tailWord_1430376
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085049332999757808543491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34780065777333010411391321 26085049332999757808543491)
  ·
    refine ⟨39127573999499636712815237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26085049332999757808543491 39127573999499636712815237)
    ·
      refine ⟨7336420124906181883652857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39127573999499636712815237 7336420124906181883652857)
      ·
        refine ⟨5502315093679636412739643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7336420124906181883652857 5502315093679636412739643)
        ·
          refine ⟨8253472640519454619109465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5502315093679636412739643 8253472640519454619109465)
          ·
            refine ⟨6190104480389590964332099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8253472640519454619109465 6190104480389590964332099)
            ·
              refine ⟨9285156720584386446498149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6190104480389590964332099 9285156720584386446498149)
              ·
                refine ⟨1740966885109572458718403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9285156720584386446498149 1740966885109572458718403)
                ·
                  refine ⟨2611450327664358688077605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740966885109572458718403 2611450327664358688077605)
                  ·
                    refine ⟨489646936437067254014551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611450327664358688077605 489646936437067254014551)
                    ·
                      rfl

theorem cell22_1430376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1430376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430376 prefixEnd_1430376 := by exact prefixLift 1430376
  have htrace : WordTrace (prefixWord ++ tailWord_1430376) baseStart_1430376 baseEnd_1430376 := by
    simpa [prefixWord, tailWord_1430376, baseEnd_1430376] using wordTrace_append hprefix tailTrace_1430376
  have hstable : (prefixWord ++ tailWord_1430376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430376).length < 2 ^ (prefixWord ++ tailWord_1430376).sum := by decide
  have hdescent : baseEnd_1430376 < baseStart_1430376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430479 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_1430479 : Nat := 118140960795 + 1430479 * 2 ^ 59
def prefixEnd_1430479 : Nat := 4983230072969 + 3 ^ 40 * 1430479 * 2
def baseEnd_1430479 : Nat := 489682195442009318689235

theorem tailTrace_1430479 : CollatzResearch.WordTrace tailWord_1430479 prefixEnd_1430479 489682195442009318689235 := by
  unfold tailWord_1430479
  simp only [CollatzResearch.WordTrace]
  refine ⟨52173855384626364208086491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34782570256417576138724327 52173855384626364208086491)
  ·
    refine ⟨78260783076939546312129737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52173855384626364208086491 78260783076939546312129737)
    ·
      refine ⟨58695587307704659734097303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78260783076939546312129737 58695587307704659734097303)
      ·
        refine ⟨88043380961556989601145955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58695587307704659734097303 88043380961556989601145955)
        ·
          refine ⟨132065071442335484401718933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88043380961556989601145955 132065071442335484401718933)
          ·
            refine ⟨6190550223859475831330575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132065071442335484401718933 6190550223859475831330575)
            ·
              refine ⟨9285825335789213746995863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6190550223859475831330575 9285825335789213746995863)
              ·
                refine ⟨13928738003683820620493795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9285825335789213746995863 13928738003683820620493795)
                ·
                  refine ⟨20893107005525730930740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13928738003683820620493795 20893107005525730930740693)
                  ·
                    refine ⟨489682195442009318689235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20893107005525730930740693 489682195442009318689235)
                    ·
                      rfl

theorem cell22_1430479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_1430479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430479 prefixEnd_1430479 := by exact prefixLift 1430479
  have htrace : WordTrace (prefixWord ++ tailWord_1430479) baseStart_1430479 baseEnd_1430479 := by
    simpa [prefixWord, tailWord_1430479, baseEnd_1430479] using wordTrace_append hprefix tailTrace_1430479
  have hstable : (prefixWord ++ tailWord_1430479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430479).length < 2 ^ (prefixWord ++ tailWord_1430479).sum := by decide
  have hdescent : baseEnd_1430479 < baseStart_1430479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430633 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 5]
def baseStart_1430633 : Nat := 118140960795 + 1430633 * 2 ^ 59
def prefixEnd_1430633 : Nat := 4983230072969 + 3 ^ 40 * 1430633 * 2
def baseEnd_1430633 : Nat := 163244970929734750112921

theorem tailTrace_1430633 : CollatzResearch.WordTrace tailWord_1430633 prefixEnd_1430633 163244970929734750112921 := by
  unfold tailWord_1430633
  simp only [CollatzResearch.WordTrace]
  refine ⟨52179472226068448509192553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34786314817378965672795035 52179472226068448509192553)
  ·
    refine ⟨39134604169551336381894415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52179472226068448509192553 39134604169551336381894415)
    ·
      refine ⟨58701906254327004572841623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39134604169551336381894415 58701906254327004572841623)
      ·
        refine ⟨88052859381490506859262435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58701906254327004572841623 88052859381490506859262435)
        ·
          refine ⟨132079289072235760288893653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88052859381490506859262435 132079289072235760288893653)
          ·
            refine ⟨3095608337630525631770945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 132079289072235760288893653 3095608337630525631770945)
            ·
              refine ⟨2321706253222894223828209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3095608337630525631770945 2321706253222894223828209)
              ·
                refine ⟨1741279689917170667871157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321706253222894223828209 1741279689917170667871157)
                ·
                  refine ⟨163244970929734750112921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1741279689917170667871157 163244970929734750112921)
                  ·
                    rfl

theorem cell22_1430633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_1430633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430633 prefixEnd_1430633 := by exact prefixLift 1430633
  have htrace : WordTrace (prefixWord ++ tailWord_1430633) baseStart_1430633 baseEnd_1430633 := by
    simpa [prefixWord, tailWord_1430633, baseEnd_1430633] using wordTrace_append hprefix tailTrace_1430633
  have hstable : (prefixWord ++ tailWord_1430633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430633).length < 2 ^ (prefixWord ++ tailWord_1430633).sum := by decide
  have hdescent : baseEnd_1430633 < baseStart_1430633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430637 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1430637 : Nat := 118140960795 + 1430637 * 2 ^ 59
def prefixEnd_1430637 : Nat := 4983230072969 + 3 ^ 40 * 1430637 * 2
def baseEnd_1430637 : Nat := 489736282070949573238751

theorem tailTrace_1430637 : CollatzResearch.WordTrace tailWord_1430637 prefixEnd_1430637 489736282070949573238751 := by
  unfold tailWord_1430637
  simp only [CollatzResearch.WordTrace]
  refine ⟨52179618118053957192338165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34786412078702638128225443 52179618118053957192338165)
  ·
    refine ⟨4891839198567558486781703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52179618118053957192338165 4891839198567558486781703)
    ·
      refine ⟨7337758797851337730172555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891839198567558486781703 7337758797851337730172555)
      ·
        refine ⟨11006638196777006595258833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337758797851337730172555 11006638196777006595258833)
        ·
          refine ⟨8254978647582754946444125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006638196777006595258833 8254978647582754946444125)
          ·
            refine ⟨3095616992843533104916547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8254978647582754946444125 3095616992843533104916547)
            ·
              refine ⟨4643425489265299657374821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095616992843533104916547 4643425489265299657374821)
              ·
                refine ⟨870642279237243685757779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4643425489265299657374821 870642279237243685757779)
                ·
                  refine ⟨1305963418855865528636669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870642279237243685757779 1305963418855865528636669)
                  ·
                    refine ⟨489736282070949573238751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305963418855865528636669 489736282070949573238751)
                    ·
                      rfl

theorem cell22_1430637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1430637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430637 prefixEnd_1430637 := by exact prefixLift 1430637
  have htrace : WordTrace (prefixWord ++ tailWord_1430637) baseStart_1430637 baseEnd_1430637 := by
    simpa [prefixWord, tailWord_1430637, baseEnd_1430637] using wordTrace_append hprefix tailTrace_1430637
  have hstable : (prefixWord ++ tailWord_1430637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430637).length < 2 ^ (prefixWord ++ tailWord_1430637).sum := by decide
  have hdescent : baseEnd_1430637 < baseStart_1430637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430663 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1430663 : Nat := 118140960795 + 1430663 * 2 ^ 59
def prefixEnd_1430663 : Nat := 4983230072969 + 3 ^ 40 * 1430663 * 2
def baseEnd_1430663 : Nat := 489745182402294172088671

theorem tailTrace_1430663 : CollatzResearch.WordTrace tailWord_1430663 prefixEnd_1430663 489745182402294172088671 := by
  unfold tailWord_1430663
  simp only [CollatzResearch.WordTrace]
  refine ⟨52180566415959763632784643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34787044277306509088523095 52180566415959763632784643)
  ·
    refine ⟨78270849623939645449176965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52180566415959763632784643 78270849623939645449176965)
    ·
      refine ⟨14675784304488683521720681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78270849623939645449176965 14675784304488683521720681)
      ·
        refine ⟨11006838228366512641290511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14675784304488683521720681 11006838228366512641290511)
        ·
          refine ⟨16510257342549768961935767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11006838228366512641290511 16510257342549768961935767)
          ·
            refine ⟨24765386013824653442903651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16510257342549768961935767 24765386013824653442903651)
            ·
              refine ⟨37148079020736980164355477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24765386013824653442903651 37148079020736980164355477)
              ·
                refine ⟨1741316204097045945204163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37148079020736980164355477 1741316204097045945204163)
                ·
                  refine ⟨2611974306145568917806245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741316204097045945204163 2611974306145568917806245)
                  ·
                    refine ⟨489745182402294172088671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611974306145568917806245 489745182402294172088671)
                    ·
                      rfl

theorem cell22_1430663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1430663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430663 prefixEnd_1430663 := by exact prefixLift 1430663
  have htrace : WordTrace (prefixWord ++ tailWord_1430663) baseStart_1430663 baseEnd_1430663 := by
    simpa [prefixWord, tailWord_1430663, baseEnd_1430663] using wordTrace_append hprefix tailTrace_1430663
  have hstable : (prefixWord ++ tailWord_1430663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430663).length < 2 ^ (prefixWord ++ tailWord_1430663).sum := by decide
  have hdescent : baseEnd_1430663 < baseStart_1430663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430680 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_1430680 : Nat := 118140960795 + 1430680 * 2 ^ 59
def prefixEnd_1430680 : Nat := 4983230072969 + 3 ^ 40 * 1430680 * 2
def baseEnd_1430680 : Nat := 489751001849711794413619

theorem tailTrace_1430680 : CollatzResearch.WordTrace tailWord_1430680 prefixEnd_1430680 489751001849711794413619 := by
  unfold tailWord_1430680
  simp only [CollatzResearch.WordTrace]
  refine ⟨26090593228449087768076747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34787457637932117024102329 26090593228449087768076747)
  ·
    refine ⟨39135889842673631652115121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26090593228449087768076747 39135889842673631652115121)
    ·
      refine ⟨29351917382005223739086341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39135889842673631652115121 29351917382005223739086341)
      ·
        refine ⟨5503484509125979451078689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29351917382005223739086341 5503484509125979451078689)
        ·
          refine ⟨4127613381844484588309017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5503484509125979451078689 4127613381844484588309017)
          ·
            refine ⟨3095710036383363441231763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4127613381844484588309017 3095710036383363441231763)
            ·
              refine ⟨4643565054575045161847645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095710036383363441231763 4643565054575045161847645)
              ·
                refine ⟨1741336895465641935692867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4643565054575045161847645 1741336895465641935692867)
                ·
                  refine ⟨2612005343198462903539301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741336895465641935692867 2612005343198462903539301)
                  ·
                    refine ⟨489751001849711794413619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2612005343198462903539301 489751001849711794413619)
                    ·
                      rfl

theorem cell22_1430680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_1430680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430680 prefixEnd_1430680 := by exact prefixLift 1430680
  have htrace : WordTrace (prefixWord ++ tailWord_1430680) baseStart_1430680 baseEnd_1430680 := by
    simpa [prefixWord, tailWord_1430680, baseEnd_1430680] using wordTrace_append hprefix tailTrace_1430680
  have hstable : (prefixWord ++ tailWord_1430680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430680).length < 2 ^ (prefixWord ++ tailWord_1430680).sum := by decide
  have hdescent : baseEnd_1430680 < baseStart_1430680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430695 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 6]
def baseStart_1430695 : Nat := 118140960795 + 1430695 * 2 ^ 59
def prefixEnd_1430695 : Nat := 4983230072969 + 3 ^ 40 * 1430695 * 2
def baseEnd_1430695 : Nat := 163252045552085585096191

theorem tailTrace_1430695 : CollatzResearch.WordTrace tailWord_1430695 prefixEnd_1430695 163252045552085585096191 := by
  unfold tailWord_1430695
  simp only [CollatzResearch.WordTrace]
  refine ⟨52181733551843833097949539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34787822367895888731966359 52181733551843833097949539)
  ·
    refine ⟨78272600327765749646924309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52181733551843833097949539 78272600327765749646924309)
    ·
      refine ⟨3669028140364019514699577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78272600327765749646924309 3669028140364019514699577)
      ·
        refine ⟨2751771105273014636024683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3669028140364019514699577 2751771105273014636024683)
        ·
          refine ⟨4127656657909521954037025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751771105273014636024683 4127656657909521954037025)
          ·
            refine ⟨3095742493432141465527769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4127656657909521954037025 3095742493432141465527769)
            ·
              refine ⟨2321806870074106099145827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3095742493432141465527769 2321806870074106099145827)
              ·
                refine ⟨3482710305111159148718741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321806870074106099145827 3482710305111159148718741)
                ·
                  refine ⟨163252045552085585096191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3482710305111159148718741 163252045552085585096191)
                  ·
                    rfl

theorem cell22_1430695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 6].length) (baseStart_1430695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430695 prefixEnd_1430695 := by exact prefixLift 1430695
  have htrace : WordTrace (prefixWord ++ tailWord_1430695) baseStart_1430695 baseEnd_1430695 := by
    simpa [prefixWord, tailWord_1430695, baseEnd_1430695] using wordTrace_append hprefix tailTrace_1430695
  have hstable : (prefixWord ++ tailWord_1430695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430695).length < 2 ^ (prefixWord ++ tailWord_1430695).sum := by decide
  have hdescent : baseEnd_1430695 < baseStart_1430695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430847 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 4]
def baseStart_1430847 : Nat := 118140960795 + 1430847 * 2 ^ 59
def prefixEnd_1430847 : Nat := 4983230072969 + 3 ^ 40 * 1430847 * 2
def baseEnd_1430847 : Nat := 163269389787526341829369

theorem tailTrace_1430847 : CollatzResearch.WordTrace tailWord_1430847 prefixEnd_1430847 163269389787526341829369 := by
  unfold tailWord_1430847
  simp only [CollatzResearch.WordTrace]
  refine ⟨52187277447293163057482795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34791518298195442038321863 52187277447293163057482795)
  ·
    refine ⟨78280916170939744586224193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52187277447293163057482795 78280916170939744586224193)
    ·
      refine ⟨58710687128204808439668145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78280916170939744586224193 58710687128204808439668145)
      ·
        refine ⟨44033015346153606329751109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58710687128204808439668145 44033015346153606329751109)
        ·
          refine ⟨8256190377403801186828333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44033015346153606329751109 8256190377403801186828333)
          ·
            refine ⟨3096071391526425445060625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8256190377403801186828333 3096071391526425445060625)
            ·
              refine ⟨2322053543644819083795469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3096071391526425445060625 2322053543644819083795469)
              ·
                refine ⟨870770078866807156423301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2322053543644819083795469 870770078866807156423301)
                ·
                  refine ⟨163269389787526341829369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870770078866807156423301 163269389787526341829369)
                  ·
                    rfl

theorem cell22_1430847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 4].length) (baseStart_1430847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430847 prefixEnd_1430847 := by exact prefixLift 1430847
  have htrace : WordTrace (prefixWord ++ tailWord_1430847) baseStart_1430847 baseEnd_1430847 := by
    simpa [prefixWord, tailWord_1430847, baseEnd_1430847] using wordTrace_append hprefix tailTrace_1430847
  have hstable : (prefixWord ++ tailWord_1430847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430847).length < 2 ^ (prefixWord ++ tailWord_1430847).sum := by decide
  have hdescent : baseEnd_1430847 < baseStart_1430847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430849 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1430849 : Nat := 118140960795 + 1430849 * 2 ^ 59
def prefixEnd_1430849 : Nat := 4983230072969 + 3 ^ 40 * 1430849 * 2
def baseEnd_1430849 : Nat := 489808854003451686938101

theorem tailTrace_1430849 : CollatzResearch.WordTrace tailWord_1430849 prefixEnd_1430849 489808854003451686938101 := by
  unfold tailWord_1430849
  simp only [CollatzResearch.WordTrace]
  refine ⟨52187350393285917399055601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34791566928857278266037067 52187350393285917399055601)
  ·
    refine ⟨39140512794964438049291701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52187350393285917399055601 39140512794964438049291701)
    ·
      refine ⟨3669423074527916067121097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39140512794964438049291701 3669423074527916067121097)
      ·
        refine ⟨2752067305895937050340823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3669423074527916067121097 2752067305895937050340823)
        ·
          refine ⟨4128100958843905575511235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752067305895937050340823 4128100958843905575511235)
          ·
            refine ⟨6192151438265858363266853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128100958843905575511235 6192151438265858363266853)
            ·
              refine ⟨1161028394674848443112535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6192151438265858363266853 1161028394674848443112535)
              ·
                refine ⟨1741542592012272664668803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161028394674848443112535 1741542592012272664668803)
                ·
                  refine ⟨2612313888018408997003205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741542592012272664668803 2612313888018408997003205)
                  ·
                    refine ⟨489808854003451686938101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2612313888018408997003205 489808854003451686938101)
                    ·
                      rfl

theorem cell22_1430849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1430849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430849 prefixEnd_1430849 := by exact prefixLift 1430849
  have htrace : WordTrace (prefixWord ++ tailWord_1430849) baseStart_1430849 baseEnd_1430849 := by
    simpa [prefixWord, tailWord_1430849, baseEnd_1430849] using wordTrace_append hprefix tailTrace_1430849
  have hstable : (prefixWord ++ tailWord_1430849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430849).length < 2 ^ (prefixWord ++ tailWord_1430849).sum := by decide
  have hdescent : baseEnd_1430849 < baseStart_1430849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430892 : List Nat := [2, 2, 1, 1, 5, 3, 2, 6]
def baseStart_1430892 : Nat := 118140960795 + 1430892 * 2 ^ 59
def prefixEnd_1430892 : Nat := 4983230072969 + 3 ^ 40 * 1430892 * 2
def baseEnd_1430892 : Nat := 54424841531357100901441

theorem tailTrace_1430892 : CollatzResearch.WordTrace tailWord_1430892 prefixEnd_1430892 54424841531357100901441 := by
  unfold tailWord_1430892
  simp only [CollatzResearch.WordTrace]
  refine ⟨26094459366065067871435465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34792612488086757161913953 26094459366065067871435465)
  ·
    refine ⟨19570844524548800903576599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26094459366065067871435465 19570844524548800903576599)
    ·
      refine ⟨29356266786823201355364899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19570844524548800903576599 29356266786823201355364899)
      ·
        refine ⟨44034400180234802033047349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29356266786823201355364899 44034400180234802033047349)
        ·
          refine ⟨4128225016897012690598189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44034400180234802033047349 4128225016897012690598189)
          ·
            refine ⟨1548084381336379758974321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4128225016897012690598189 1548084381336379758974321)
            ·
              refine ⟨1161063286002284819230741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548084381336379758974321 1161063286002284819230741)
              ·
                refine ⟨54424841531357100901441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1161063286002284819230741 54424841531357100901441)
                ·
                  rfl

theorem cell22_1430892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_1430892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430892 prefixEnd_1430892 := by exact prefixLift 1430892
  have htrace : WordTrace (prefixWord ++ tailWord_1430892) baseStart_1430892 baseEnd_1430892 := by
    simpa [prefixWord, tailWord_1430892, baseEnd_1430892] using wordTrace_append hprefix tailTrace_1430892
  have hstable : (prefixWord ++ tailWord_1430892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430892).length < 2 ^ (prefixWord ++ tailWord_1430892).sum := by decide
  have hdescent : baseEnd_1430892 < baseStart_1430892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430903 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 9]
def baseStart_1430903 : Nat := 118140960795 + 1430903 * 2 ^ 59
def prefixEnd_1430903 : Nat := 4983230072969 + 3 ^ 40 * 1430903 * 2
def baseEnd_1430903 : Nat := 163275779769004515362645

theorem tailTrace_1430903 : CollatzResearch.WordTrace tailWord_1430903 prefixEnd_1430903 163275779769004515362645 := by
  unfold tailWord_1430903
  simp only [CollatzResearch.WordTrace]
  refine ⟨52189319935090284621521363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34792879956726856414347575 52189319935090284621521363)
  ·
    refine ⟨78283979902635426932282045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52189319935090284621521363 78283979902635426932282045)
    ·
      refine ⟨29356492463488285099605767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78283979902635426932282045 29356492463488285099605767)
      ·
        refine ⟨44034738695232427649408651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29356492463488285099605767 44034738695232427649408651)
        ·
          refine ⟨66052108042848641474112977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44034738695232427649408651 66052108042848641474112977)
          ·
            refine ⟨49539081032136481105584733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66052108042848641474112977 49539081032136481105584733)
            ·
              refine ⟨18577155387051180414594275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49539081032136481105584733 18577155387051180414594275)
              ·
                refine ⟨27865733080576770621891413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18577155387051180414594275 27865733080576770621891413)
                ·
                  refine ⟨163275779769004515362645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27865733080576770621891413 163275779769004515362645)
                  ·
                    rfl

theorem cell22_1430903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_1430903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430903 prefixEnd_1430903 := by exact prefixLift 1430903
  have htrace : WordTrace (prefixWord ++ tailWord_1430903) baseStart_1430903 baseEnd_1430903 := by
    simpa [prefixWord, tailWord_1430903, baseEnd_1430903] using wordTrace_append hprefix tailTrace_1430903
  have hstable : (prefixWord ++ tailWord_1430903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430903).length < 2 ^ (prefixWord ++ tailWord_1430903).sum := by decide
  have hdescent : baseEnd_1430903 < baseStart_1430903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430920 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_1430920 : Nat := 118140960795 + 1430920 * 2 ^ 59
def prefixEnd_1430920 : Nat := 4983230072969 + 3 ^ 40 * 1430920 * 2
def baseEnd_1430920 : Nat := 163277719584810389470961

theorem tailTrace_1430920 : CollatzResearch.WordTrace tailWord_1430920 prefixEnd_1430920 163277719584810389470961 := by
  unfold tailWord_1430920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26094969988014348262445107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34793293317352464349926809 26094969988014348262445107)
  ·
    refine ⟨39142454982021522393667661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26094969988014348262445107 39142454982021522393667661)
    ·
      refine ⟨14678420618258070897625373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39142454982021522393667661 14678420618258070897625373)
      ·
        refine ⟨5504407731846776586609515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14678420618258070897625373 5504407731846776586609515)
        ·
          refine ⟨8256611597770164879914273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5504407731846776586609515 8256611597770164879914273)
          ·
            refine ⟨6192458698327623659935705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8256611597770164879914273 6192458698327623659935705)
            ·
              refine ⟨4644344023745717744951779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6192458698327623659935705 4644344023745717744951779)
              ·
                refine ⟨6966516035618576617427669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644344023745717744951779 6966516035618576617427669)
                ·
                  refine ⟨163277719584810389470961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6966516035618576617427669 163277719584810389470961)
                  ·
                    rfl

theorem cell22_1430920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_1430920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430920 prefixEnd_1430920 := by exact prefixLift 1430920
  have htrace : WordTrace (prefixWord ++ tailWord_1430920) baseStart_1430920 baseEnd_1430920 := by
    simpa [prefixWord, tailWord_1430920, baseEnd_1430920] using wordTrace_append hprefix tailTrace_1430920
  have hstable : (prefixWord ++ tailWord_1430920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430920).length < 2 ^ (prefixWord ++ tailWord_1430920).sum := by decide
  have hdescent : baseEnd_1430920 < baseStart_1430920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430930 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1430930 : Nat := 118140960795 + 1430930 * 2 ^ 59
def prefixEnd_1430930 : Nat := 4983230072969 + 3 ^ 40 * 1430930 * 2
def baseEnd_1430930 : Nat := 489836581958794475662853

theorem tailTrace_1430930 : CollatzResearch.WordTrace tailWord_1430930 prefixEnd_1430930 489836581958794475662853 := by
  unfold tailWord_1430930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13047576176498117058188561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34793536470661645488502829 13047576176498117058188561)
  ·
    refine ⟨9785682132373587793641421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13047576176498117058188561 9785682132373587793641421)
    ·
      refine ⟨3669630799640095422615533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9785682132373587793641421 3669630799640095422615533)
      ·
        refine ⟨1376111549865035783480825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3669630799640095422615533 1376111549865035783480825)
        ·
          refine ⟨1032083662398776837610619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376111549865035783480825 1032083662398776837610619)
          ·
            refine ⟨1548125493598165256415929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032083662398776837610619 1548125493598165256415929)
            ·
              refine ⟨1161094120198623942311947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548125493598165256415929 1161094120198623942311947)
              ·
                refine ⟨1741641180297935913467921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161094120198623942311947 1741641180297935913467921)
                ·
                  refine ⟨1306230885223451935100941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741641180297935913467921 1306230885223451935100941)
                  ·
                    refine ⟨489836581958794475662853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306230885223451935100941 489836581958794475662853)
                    ·
                      rfl

theorem cell22_1430930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1430930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430930 prefixEnd_1430930 := by exact prefixLift 1430930
  have htrace : WordTrace (prefixWord ++ tailWord_1430930) baseStart_1430930 baseEnd_1430930 := by
    simpa [prefixWord, tailWord_1430930, baseEnd_1430930] using wordTrace_append hprefix tailTrace_1430930
  have hstable : (prefixWord ++ tailWord_1430930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430930).length < 2 ^ (prefixWord ++ tailWord_1430930).sum := by decide
  have hdescent : baseEnd_1430930 < baseStart_1430930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430937 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 5]
def baseStart_1430937 : Nat := 118140960795 + 1430937 * 2 ^ 59
def prefixEnd_1430937 : Nat := 4983230072969 + 3 ^ 40 * 1430937 * 2
def baseEnd_1430937 : Nat := 163279659400616263579277

theorem tailTrace_1430937 : CollatzResearch.WordTrace tailWord_1430937 prefixEnd_1430937 163279659400616263579277 := by
  unfold tailWord_1430937
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190560016967108428259065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34793706677978072285506043 52190560016967108428259065)
  ·
    refine ⟨39142920012725331321194299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52190560016967108428259065 39142920012725331321194299)
    ·
      refine ⟨58714380019087996981791449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39142920012725331321194299 58714380019087996981791449)
      ·
        refine ⟨44035785014315997736343587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58714380019087996981791449 44035785014315997736343587)
        ·
          refine ⟨66053677521473996604515381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44035785014315997736343587 66053677521473996604515381)
          ·
            refine ⟨6192532267638187181673317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66053677521473996604515381 6192532267638187181673317)
            ·
              refine ⟨1161099800182160096563747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6192532267638187181673317 1161099800182160096563747)
              ·
                refine ⟨1741649700273240144845621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161099800182160096563747 1741649700273240144845621)
                ·
                  refine ⟨163279659400616263579277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1741649700273240144845621 163279659400616263579277)
                  ·
                    rfl

theorem cell22_1430937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_1430937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430937 prefixEnd_1430937 := by exact prefixLift 1430937
  have htrace : WordTrace (prefixWord ++ tailWord_1430937) baseStart_1430937 baseEnd_1430937 := by
    simpa [prefixWord, tailWord_1430937, baseEnd_1430937] using wordTrace_append hprefix tailTrace_1430937
  have hstable : (prefixWord ++ tailWord_1430937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430937).length < 2 ^ (prefixWord ++ tailWord_1430937).sum := by decide
  have hdescent : baseEnd_1430937 < baseStart_1430937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430997 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1430997 : Nat := 118140960795 + 1430997 * 2 ^ 59
def prefixEnd_1430997 : Nat := 4983230072969 + 3 ^ 40 * 1430997 * 2
def baseEnd_1430997 : Nat := 489859517428028634237647

theorem tailTrace_1430997 : CollatzResearch.WordTrace tailWord_1430997 prefixEnd_1430997 489859517428028634237647 := by
  unfold tailWord_1430997
  simp only [CollatzResearch.WordTrace]
  refine ⟨52192748396749738675443245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34795165597833159116962163 52192748396749738675443245)
  ·
    refine ⟨19572280648781152003291217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52192748396749738675443245 19572280648781152003291217)
    ·
      refine ⟨14679210486585864002468413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19572280648781152003291217 14679210486585864002468413)
      ·
        refine ⟨5504703932469699000925655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14679210486585864002468413 5504703932469699000925655)
        ·
          refine ⟨8257055898704548501388483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5504703932469699000925655 8257055898704548501388483)
          ·
            refine ⟨12385583848056822752082725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8257055898704548501388483 12385583848056822752082725)
            ·
              refine ⟨2322296971510654266015511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12385583848056822752082725 2322296971510654266015511)
              ·
                refine ⟨3483445457265981399023267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322296971510654266015511 3483445457265981399023267)
                ·
                  refine ⟨5225168185898972098534901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483445457265981399023267 5225168185898972098534901)
                  ·
                    refine ⟨489859517428028634237647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5225168185898972098534901 489859517428028634237647)
                    ·
                      rfl

theorem cell22_1430997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1430997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1430997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1430997 prefixEnd_1430997 := by exact prefixLift 1430997
  have htrace : WordTrace (prefixWord ++ tailWord_1430997) baseStart_1430997 baseEnd_1430997 := by
    simpa [prefixWord, tailWord_1430997, baseEnd_1430997] using wordTrace_append hprefix tailTrace_1430997
  have hstable : (prefixWord ++ tailWord_1430997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430997).length < 2 ^ (prefixWord ++ tailWord_1430997).sum := by decide
  have hdescent : baseEnd_1430997 < baseStart_1430997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431018 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1431018 : Nat := 118140960795 + 1431018 * 2 ^ 59
def prefixEnd_1431018 : Nat := 4983230072969 + 3 ^ 40 * 1431018 * 2
def baseEnd_1431018 : Nat := 489866706157191579462583

theorem tailTrace_1431018 : CollatzResearch.WordTrace tailWord_1431018 prefixEnd_1431018 489866706157191579462583 := by
  unfold tailWord_1431018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13048378582418414815489427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34795676219782439507971805 13048378582418414815489427)
  ·
    refine ⟨19572567873627622223234141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13048378582418414815489427 19572567873627622223234141)
    ·
      refine ⟨7339712952610358333712803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19572567873627622223234141 7339712952610358333712803)
      ·
        refine ⟨11009569428915537500569205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7339712952610358333712803 11009569428915537500569205)
        ·
          refine ⟨1032147133960831640678363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11009569428915537500569205 1032147133960831640678363)
          ·
            refine ⟨1548220700941247461017545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032147133960831640678363 1548220700941247461017545)
            ·
              refine ⟨1161165525705935595763159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548220700941247461017545 1161165525705935595763159)
              ·
                refine ⟨1741748288558903393644739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161165525705935595763159 1741748288558903393644739)
                ·
                  refine ⟨2612622432838355090467109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741748288558903393644739 2612622432838355090467109)
                  ·
                    refine ⟨489866706157191579462583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2612622432838355090467109 489866706157191579462583)
                    ·
                      rfl

theorem cell22_1431018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1431018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431018 prefixEnd_1431018 := by exact prefixLift 1431018
  have htrace : WordTrace (prefixWord ++ tailWord_1431018) baseStart_1431018 baseEnd_1431018 := by
    simpa [prefixWord, tailWord_1431018, baseEnd_1431018] using wordTrace_append hprefix tailTrace_1431018
  have hstable : (prefixWord ++ tailWord_1431018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431018).length < 2 ^ (prefixWord ++ tailWord_1431018).sum := by decide
  have hdescent : baseEnd_1431018 < baseStart_1431018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431072 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_1431072 : Nat := 118140960795 + 1431072 * 2 ^ 59
def prefixEnd_1431072 : Nat := 4983230072969 + 3 ^ 40 * 1431072 * 2
def baseEnd_1431072 : Nat := 163295063820251146204139

theorem tailTrace_1431072 : CollatzResearch.WordTrace tailWord_1431072 prefixEnd_1431072 163295063820251146204139 := by
  unfold tailWord_1431072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26097741935739013242211735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34796989247652017656282313 26097741935739013242211735)
  ·
    refine ⟨39146612903608519863317603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26097741935739013242211735 39146612903608519863317603)
    ·
      refine ⟨58719919355412779794976405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39146612903608519863317603 58719919355412779794976405)
      ·
        refine ⟨2752496219784974052889519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58719919355412779794976405 2752496219784974052889519)
        ·
          refine ⟨4128744329677461079334279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752496219784974052889519 4128744329677461079334279)
          ·
            refine ⟨6193116494516191619001419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128744329677461079334279 6193116494516191619001419)
            ·
              refine ⟨9289674741774287428502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193116494516191619001419 9289674741774287428502129)
              ·
                refine ⟨6967256056330715571376597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9289674741774287428502129 6967256056330715571376597)
                ·
                  refine ⟨163295063820251146204139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6967256056330715571376597 163295063820251146204139)
                  ·
                    rfl

theorem cell22_1431072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_1431072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431072 prefixEnd_1431072 := by exact prefixLift 1431072
  have htrace : WordTrace (prefixWord ++ tailWord_1431072) baseStart_1431072 baseEnd_1431072 := by
    simpa [prefixWord, tailWord_1431072, baseEnd_1431072] using wordTrace_append hprefix tailTrace_1431072
  have hstable : (prefixWord ++ tailWord_1431072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431072).length < 2 ^ (prefixWord ++ tailWord_1431072).sum := by decide
  have hdescent : baseEnd_1431072 < baseStart_1431072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431093 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1431093 : Nat := 118140960795 + 1431093 * 2 ^ 59
def prefixEnd_1431093 : Nat := 4983230072969 + 3 ^ 40 * 1431093 * 2
def baseEnd_1431093 : Nat := 489892380189916383837353

theorem tailTrace_1431093 : CollatzResearch.WordTrace tailWord_1431093 prefixEnd_1431093 489892380189916383837353 := by
  unfold tailWord_1431093
  simp only [CollatzResearch.WordTrace]
  refine ⟨52196249804401947070937933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34797499869601298047291955 52196249804401947070937933)
  ·
    refine ⟨19573593676650730151601725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52196249804401947070937933 19573593676650730151601725)
    ·
      refine ⟨7340097628744023806850647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19573593676650730151601725 7340097628744023806850647)
      ·
        refine ⟨11010146443116035710275971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340097628744023806850647 11010146443116035710275971)
        ·
          refine ⟨16515219664674053565413957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010146443116035710275971 16515219664674053565413957)
          ·
            refine ⟨3096603687126385043515117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16515219664674053565413957 3096603687126385043515117)
            ·
              refine ⟨1161226382672394391318169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3096603687126385043515117 1161226382672394391318169)
              ·
                refine ⟨870919787004295793488627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161226382672394391318169 870919787004295793488627)
                ·
                  refine ⟨1306379680506443690232941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870919787004295793488627 1306379680506443690232941)
                  ·
                    refine ⟨489892380189916383837353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306379680506443690232941 489892380189916383837353)
                    ·
                      rfl

theorem cell22_1431093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1431093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431093 prefixEnd_1431093 := by exact prefixLift 1431093
  have htrace : WordTrace (prefixWord ++ tailWord_1431093) baseStart_1431093 baseEnd_1431093 := by
    simpa [prefixWord, tailWord_1431093, baseEnd_1431093] using wordTrace_append hprefix tailTrace_1431093
  have hstable : (prefixWord ++ tailWord_1431093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431093).length < 2 ^ (prefixWord ++ tailWord_1431093).sum := by decide
  have hdescent : baseEnd_1431093 < baseStart_1431093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431299 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_1431299 : Nat := 118140960795 + 1431299 * 2 ^ 59
def prefixEnd_1431299 : Nat := 4983230072969 + 3 ^ 40 * 1431299 * 2
def baseEnd_1431299 : Nat := 489962898199800513186721

theorem tailTrace_1431299 : CollatzResearch.WordTrace tailWord_1431299 prefixEnd_1431299 489962898199800513186721 := by
  unfold tailWord_1431299
  simp only [CollatzResearch.WordTrace]
  refine ⟨52203763241655644252936951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34802508827770429501957967 52203763241655644252936951)
  ·
    refine ⟨78305644862483466379405427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52203763241655644252936951 78305644862483466379405427)
    ·
      refine ⟨117458467293725199569108141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78305644862483466379405427 117458467293725199569108141)
      ·
        refine ⟨44046925235146949838415553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117458467293725199569108141 44046925235146949838415553)
        ·
          refine ⟨33035193926360212378811665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44046925235146949838415553 33035193926360212378811665)
          ·
            refine ⟨24776395444770159284108749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33035193926360212378811665 24776395444770159284108749)
            ·
              refine ⟨9291148291788809731540781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24776395444770159284108749 9291148291788809731540781)
              ·
                refine ⟨3484180609420803649327793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9291148291788809731540781 3484180609420803649327793)
                ·
                  refine ⟨2613135457065602736995845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484180609420803649327793 2613135457065602736995845)
                  ·
                    refine ⟨489962898199800513186721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2613135457065602736995845 489962898199800513186721)
                    ·
                      rfl

theorem cell22_1431299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_1431299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431299 prefixEnd_1431299 := by exact prefixLift 1431299
  have htrace : WordTrace (prefixWord ++ tailWord_1431299) baseStart_1431299 baseEnd_1431299 := by
    simpa [prefixWord, tailWord_1431299, baseEnd_1431299] using wordTrace_append hprefix tailTrace_1431299
  have hstable : (prefixWord ++ tailWord_1431299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431299).length < 2 ^ (prefixWord ++ tailWord_1431299).sum := by decide
  have hdescent : baseEnd_1431299 < baseStart_1431299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431346 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_1431346 : Nat := 118140960795 + 1431346 * 2 ^ 59
def prefixEnd_1431346 : Nat := 4983230072969 + 3 ^ 40 * 1431346 * 2
def baseEnd_1431346 : Nat := 489978987260308057261577

theorem tailTrace_1431346 : CollatzResearch.WordTrace tailWord_1431346 prefixEnd_1431346 489978987260308057261577 := by
  unfold tailWord_1431346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051369368121342819974473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34803651648323580853265261 13051369368121342819974473)
  ·
    refine ⟨9788527026091007114980855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13051369368121342819974473 9788527026091007114980855)
    ·
      refine ⟨14682790539136510672471283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9788527026091007114980855 14682790539136510672471283)
      ·
        refine ⟨22024185808704766008706925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14682790539136510672471283 22024185808704766008706925)
        ·
          refine ⟨8259069678264287253265097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22024185808704766008706925 8259069678264287253265097)
          ·
            refine ⟨6194302258698215439948823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259069678264287253265097 6194302258698215439948823)
            ·
              refine ⟨9291453388047323159923235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194302258698215439948823 9291453388047323159923235)
              ·
                refine ⟨13937180082070984739884853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9291453388047323159923235 13937180082070984739884853)
                ·
                  refine ⟨1306610632694154819364205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13937180082070984739884853 1306610632694154819364205)
                  ·
                    refine ⟨489978987260308057261577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306610632694154819364205 489978987260308057261577)
                    ·
                      rfl

theorem cell22_1431346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_1431346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431346 prefixEnd_1431346 := by exact prefixLift 1431346
  have htrace : WordTrace (prefixWord ++ tailWord_1431346) baseStart_1431346 baseEnd_1431346 := by
    simpa [prefixWord, tailWord_1431346, baseEnd_1431346] using wordTrace_append hprefix tailTrace_1431346
  have hstable : (prefixWord ++ tailWord_1431346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431346).length < 2 ^ (prefixWord ++ tailWord_1431346).sum := by decide
  have hdescent : baseEnd_1431346 < baseStart_1431346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431348 : List Nat := [2, 5, 1, 1, 2, 2, 3, 6]
def baseStart_1431348 : Nat := 118140960795 + 1431348 * 2 ^ 59
def prefixEnd_1431348 : Nat := 4983230072969 + 3 ^ 40 * 1431348 * 2
def baseEnd_1431348 : Nat := 54442185766797857634619

theorem tailTrace_1431348 : CollatzResearch.WordTrace tailWord_1431348 prefixEnd_1431348 54442185766797857634619 := by
  unfold tailWord_1431348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26102775209239062810735349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34803700278985417080980465 26102775209239062810735349)
  ·
    refine ⟨2447135175866162138506439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26102775209239062810735349 2447135175866162138506439)
    ·
      refine ⟨3670702763799243207759659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447135175866162138506439 3670702763799243207759659)
      ·
        refine ⟨5506054145698864811639489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670702763799243207759659 5506054145698864811639489)
        ·
          refine ⟨4129540609274148608729617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5506054145698864811639489 4129540609274148608729617)
          ·
            refine ⟨3097155456955611456547213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4129540609274148608729617 3097155456955611456547213)
            ·
              refine ⟨1161433296358354296205205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3097155456955611456547213 1161433296358354296205205)
              ·
                refine ⟨54442185766797857634619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1161433296358354296205205 54442185766797857634619)
                ·
                  rfl

theorem cell22_1431348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_1431348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431348 prefixEnd_1431348 := by exact prefixLift 1431348
  have htrace : WordTrace (prefixWord ++ tailWord_1431348) baseStart_1431348 baseEnd_1431348 := by
    simpa [prefixWord, tailWord_1431348, baseEnd_1431348] using wordTrace_append hprefix tailTrace_1431348
  have hstable : (prefixWord ++ tailWord_1431348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431348).length < 2 ^ (prefixWord ++ tailWord_1431348).sum := by decide
  have hdescent : baseEnd_1431348 < baseStart_1431348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431350 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1431350 : Nat := 118140960795 + 1431350 * 2 ^ 59
def prefixEnd_1431350 : Nat := 4983230072969 + 3 ^ 40 * 1431350 * 2
def baseEnd_1431350 : Nat := 489980356542053380161565

theorem tailTrace_1431350 : CollatzResearch.WordTrace tailWord_1431350 prefixEnd_1431350 489980356542053380161565 := by
  unfold tailWord_1431350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262851460279429997690219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34803748909647253308695669 3262851460279429997690219)
  ·
    refine ⟨4894277190419144996535329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262851460279429997690219 4894277190419144996535329)
    ·
      refine ⟨3670707892814358747401497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894277190419144996535329 3670707892814358747401497)
      ·
        refine ⟨2753030919610769060551123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3670707892814358747401497 2753030919610769060551123)
        ·
          refine ⟨4129546379416153590826685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753030919610769060551123 4129546379416153590826685)
          ·
            refine ⟨1548579892281057596560007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4129546379416153590826685 1548579892281057596560007)
            ·
              refine ⟨2322869838421586394840011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548579892281057596560007 2322869838421586394840011)
              ·
                refine ⟨3484304757632379592260017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322869838421586394840011 3484304757632379592260017)
                ·
                  refine ⟨2613228568224284694195013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484304757632379592260017 2613228568224284694195013)
                  ·
                    refine ⟨489980356542053380161565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2613228568224284694195013 489980356542053380161565)
                    ·
                      rfl

theorem cell22_1431350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1431350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431350 prefixEnd_1431350 := by exact prefixLift 1431350
  have htrace : WordTrace (prefixWord ++ tailWord_1431350) baseStart_1431350 baseEnd_1431350 := by
    simpa [prefixWord, tailWord_1431350, baseEnd_1431350] using wordTrace_append hprefix tailTrace_1431350
  have hstable : (prefixWord ++ tailWord_1431350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431350).length < 2 ^ (prefixWord ++ tailWord_1431350).sum := by decide
  have hdescent : baseEnd_1431350 < baseStart_1431350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431363 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 1, 3]
def baseStart_1431363 : Nat := 118140960795 + 1431363 * 2 ^ 59
def prefixEnd_1431363 : Nat := 4983230072969 + 3 ^ 40 * 1431363 * 2
def baseEnd_1431363 : Nat := 489984806707725679586525

theorem tailTrace_1431363 : CollatzResearch.WordTrace tailWord_1431363 prefixEnd_1431363 489984806707725679586525 := by
  unfold tailWord_1431363
  simp only [CollatzResearch.WordTrace]
  refine ⟨52206097513423783183266743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34804065008949188788844495 52206097513423783183266743)
  ·
    refine ⟨78309146270135674774900115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52206097513423783183266743 78309146270135674774900115)
    ·
      refine ⟨117463719405203512162350173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78309146270135674774900115 117463719405203512162350173)
      ·
        refine ⟨44048894776951317060881315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117463719405203512162350173 44048894776951317060881315)
        ·
          refine ⟨66073342165426975591321973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44048894776951317060881315 66073342165426975591321973)
          ·
            refine ⟨6194375828008778961686435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66073342165426975591321973 6194375828008778961686435)
            ·
              refine ⟨9291563742013168442529653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194375828008778961686435 9291563742013168442529653)
              ·
                refine ⟨871084100813734541487155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9291563742013168442529653 871084100813734541487155)
                ·
                  refine ⟨1306626151220601812230733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871084100813734541487155 1306626151220601812230733)
                  ·
                    refine ⟨489984806707725679586525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306626151220601812230733 489984806707725679586525)
                    ·
                      rfl

theorem cell22_1431363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 3].length) (baseStart_1431363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431363 prefixEnd_1431363 := by exact prefixLift 1431363
  have htrace : WordTrace (prefixWord ++ tailWord_1431363) baseStart_1431363 baseEnd_1431363 := by
    simpa [prefixWord, tailWord_1431363, baseEnd_1431363] using wordTrace_append hprefix tailTrace_1431363
  have hstable : (prefixWord ++ tailWord_1431363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431363).length < 2 ^ (prefixWord ++ tailWord_1431363).sum := by decide
  have hdescent : baseEnd_1431363 < baseStart_1431363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431380 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1431380 : Nat := 118140960795 + 1431380 * 2 ^ 59
def prefixEnd_1431380 : Nat := 4983230072969 + 3 ^ 40 * 1431380 * 2
def baseEnd_1431380 : Nat := 489990626155143301911473

theorem tailTrace_1431380 : CollatzResearch.WordTrace tailWord_1431380 prefixEnd_1431380 489990626155143301911473 := by
  unfold tailWord_1431380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26103358777181097543317797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34804478369574796724423729 26103358777181097543317797)
  ·
    refine ⟨4894379770721455789372087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26103358777181097543317797 4894379770721455789372087)
    ·
      refine ⟨7341569656082183684058131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4894379770721455789372087 7341569656082183684058131)
      ·
        refine ⟨11012354484123275526087197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7341569656082183684058131 11012354484123275526087197)
        ·
          refine ⟨4129632931546228322282699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11012354484123275526087197 4129632931546228322282699)
          ·
            refine ⟨6194449397319342483424049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129632931546228322282699 6194449397319342483424049)
            ·
              refine ⟨4645837047989506862568037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194449397319342483424049 4645837047989506862568037)
              ·
                refine ⟨871094446498032536731507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4645837047989506862568037 871094446498032536731507)
                ·
                  refine ⟨1306641669747048805097261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871094446498032536731507 1306641669747048805097261)
                  ·
                    refine ⟨489990626155143301911473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306641669747048805097261 489990626155143301911473)
                    ·
                      rfl

theorem cell22_1431380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1431380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431380 prefixEnd_1431380 := by exact prefixLift 1431380
  have htrace : WordTrace (prefixWord ++ tailWord_1431380) baseStart_1431380 baseEnd_1431380 := by
    simpa [prefixWord, tailWord_1431380, baseEnd_1431380] using wordTrace_append hprefix tailTrace_1431380
  have hstable : (prefixWord ++ tailWord_1431380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431380).length < 2 ^ (prefixWord ++ tailWord_1431380).sum := by decide
  have hdescent : baseEnd_1431380 < baseStart_1431380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431414 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_1431414 : Nat := 118140960795 + 1431414 * 2 ^ 59
def prefixEnd_1431414 : Nat := 4983230072969 + 3 ^ 40 * 1431414 * 2
def baseEnd_1431414 : Nat := 490002265049978546561369

theorem tailTrace_1431414 : CollatzResearch.WordTrace tailWord_1431414 prefixEnd_1431414 490002265049978546561369 := by
  unfold tailWord_1431414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262997352264938680835831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34805305090826012595582197 3262997352264938680835831)
  ·
    refine ⟨4894496028397408021253747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262997352264938680835831 4894496028397408021253747)
    ·
      refine ⟨7341744042596112031880621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4894496028397408021253747 7341744042596112031880621)
      ·
        refine ⟨2753154015973542011955233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7341744042596112031880621 2753154015973542011955233)
        ·
          refine ⟨2064865511980156508966425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753154015973542011955233 2064865511980156508966425)
          ·
            refine ⟨1548649133985117381724819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064865511980156508966425 1548649133985117381724819)
            ·
              refine ⟨2322973700977676072587229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548649133985117381724819 2322973700977676072587229)
              ·
                refine ⟨871115137866628527220211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2322973700977676072587229 871115137866628527220211)
                ·
                  refine ⟨1306672706799942790830317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871115137866628527220211 1306672706799942790830317)
                  ·
                    refine ⟨490002265049978546561369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306672706799942790830317 490002265049978546561369)
                    ·
                      rfl

theorem cell22_1431414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_1431414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431414 prefixEnd_1431414 := by exact prefixLift 1431414
  have htrace : WordTrace (prefixWord ++ tailWord_1431414) baseStart_1431414 baseEnd_1431414 := by
    simpa [prefixWord, tailWord_1431414, baseEnd_1431414] using wordTrace_append hprefix tailTrace_1431414
  have hstable : (prefixWord ++ tailWord_1431414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431414).length < 2 ^ (prefixWord ++ tailWord_1431414).sum := by decide
  have hdescent : baseEnd_1431414 < baseStart_1431414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431419 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_1431419 : Nat := 118140960795 + 1431419 * 2 ^ 59
def prefixEnd_1431419 : Nat := 4983230072969 + 3 ^ 40 * 1431419 * 2
def baseEnd_1431419 : Nat := 490003976652160200186353

theorem tailTrace_1431419 : CollatzResearch.WordTrace tailWord_1431419 prefixEnd_1431419 490003976652160200186353 := by
  unfold tailWord_1431419
  simp only [CollatzResearch.WordTrace]
  refine ⟨52208140001220904747305311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34805426667480603164870207 52208140001220904747305311)
  ·
    refine ⟨78312210001831357120957967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52208140001220904747305311 78312210001831357120957967)
    ·
      refine ⟨117468315002747035681436951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78312210001831357120957967 117468315002747035681436951)
      ·
        refine ⟨176202472504120553522155427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117468315002747035681436951 176202472504120553522155427)
        ·
          refine ⟨264303708756180830283233141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176202472504120553522155427 264303708756180830283233141)
          ·
            refine ⟨24778472695891952839053107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264303708756180830283233141 24778472695891952839053107)
            ·
              refine ⟨37167709043837929258579661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24778472695891952839053107 37167709043837929258579661)
              ·
                refine ⟨13937890891439223471967373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37167709043837929258579661 13937890891439223471967373)
                ·
                  refine ⟨5226709084289708801987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13937890891439223471967373 5226709084289708801987765)
                  ·
                    refine ⟨490003976652160200186353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5226709084289708801987765 490003976652160200186353)
                    ·
                      rfl

theorem cell22_1431419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_1431419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431419 prefixEnd_1431419 := by exact prefixLift 1431419
  have htrace : WordTrace (prefixWord ++ tailWord_1431419) baseStart_1431419 baseEnd_1431419 := by
    simpa [prefixWord, tailWord_1431419, baseEnd_1431419] using wordTrace_append hprefix tailTrace_1431419
  have hstable : (prefixWord ++ tailWord_1431419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431419).length < 2 ^ (prefixWord ++ tailWord_1431419).sum := by decide
  have hdescent : baseEnd_1431419 < baseStart_1431419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431449 : List Nat := [1, 2, 1, 2, 1, 3, 3, 9]
def baseStart_1431449 : Nat := 118140960795 + 1431449 * 2 ^ 59
def prefixEnd_1431449 : Nat := 4983230072969 + 3 ^ 40 * 1431449 * 2
def baseEnd_1431449 : Nat := 54446027362805569104029

theorem tailTrace_1431449 : CollatzResearch.WordTrace tailWord_1431449 prefixEnd_1431449 54446027362805569104029 := by
  unfold tailWord_1431449
  simp only [CollatzResearch.WordTrace]
  refine ⟨52209234191112219870897401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34806156127408146580598267 52209234191112219870897401)
  ·
    refine ⟨39156925643334164903173051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52209234191112219870897401 39156925643334164903173051)
    ·
      refine ⟨58735388465001247354759577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39156925643334164903173051 58735388465001247354759577)
      ·
        refine ⟨44051541348750935516069683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58735388465001247354759577 44051541348750935516069683)
        ·
          refine ⟨66077312023126403274104525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44051541348750935516069683 66077312023126403274104525)
          ·
            refine ⟨24778992008672401227789197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66077312023126403274104525 24778992008672401227789197)
            ·
              refine ⟨9292122003252150460420949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24778992008672401227789197 9292122003252150460420949)
              ·
                refine ⟨54446027362805569104029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9292122003252150460420949 54446027362805569104029)
                ·
                  rfl

theorem cell22_1431449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 9].length) (baseStart_1431449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431449 prefixEnd_1431449 := by exact prefixLift 1431449
  have htrace : WordTrace (prefixWord ++ tailWord_1431449) baseStart_1431449 baseEnd_1431449 := by
    simpa [prefixWord, tailWord_1431449, baseEnd_1431449] using wordTrace_append hprefix tailTrace_1431449
  have hstable : (prefixWord ++ tailWord_1431449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431449).length < 2 ^ (prefixWord ++ tailWord_1431449).sum := by decide
  have hdescent : baseEnd_1431449 < baseStart_1431449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431457 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1431457 : Nat := 118140960795 + 1431457 * 2 ^ 59
def prefixEnd_1431457 : Nat := 4983230072969 + 3 ^ 40 * 1431457 * 2
def baseEnd_1431457 : Nat := 490016984828740767736237

theorem tailTrace_1431457 : CollatzResearch.WordTrace tailWord_1431457 prefixEnd_1431457 490016984828740767736237 := by
  unfold tailWord_1431457
  simp only [CollatzResearch.WordTrace]
  refine ⟨52209525975083237237188625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34806350650055491491459083 52209525975083237237188625)
  ·
    refine ⟨39157144481312427927891469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52209525975083237237188625 39157144481312427927891469)
    ·
      refine ⟨14683929180492160472959301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39157144481312427927891469 14683929180492160472959301)
      ·
        refine ⟨2753236721342280088679869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14683929180492160472959301 2753236721342280088679869)
        ·
          refine ⟨1032463770503355033254951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2753236721342280088679869 1032463770503355033254951)
          ·
            refine ⟨1548695655755032549882427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032463770503355033254951 1548695655755032549882427)
            ·
              refine ⟨2323043483632548824823641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548695655755032549882427 2323043483632548824823641)
              ·
                refine ⟨1742282612724411618617731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323043483632548824823641 1742282612724411618617731)
                ·
                  refine ⟨2613423919086617427926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742282612724411618617731 2613423919086617427926597)
                  ·
                    refine ⟨490016984828740767736237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2613423919086617427926597 490016984828740767736237)
                    ·
                      rfl

theorem cell22_1431457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1431457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431457 prefixEnd_1431457 := by exact prefixLift 1431457
  have htrace : WordTrace (prefixWord ++ tailWord_1431457) baseStart_1431457 baseEnd_1431457 := by
    simpa [prefixWord, tailWord_1431457, baseEnd_1431457] using wordTrace_append hprefix tailTrace_1431457
  have hstable : (prefixWord ++ tailWord_1431457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431457).length < 2 ^ (prefixWord ++ tailWord_1431457).sum := by decide
  have hdescent : baseEnd_1431457 < baseStart_1431457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431496 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_1431496 : Nat := 118140960795 + 1431496 * 2 ^ 59
def prefixEnd_1431496 : Nat := 4983230072969 + 3 ^ 40 * 1431496 * 2
def baseEnd_1431496 : Nat := 490030335325757666011117

theorem tailTrace_1431496 : CollatzResearch.WordTrace tailWord_1431496 prefixEnd_1431496 490030335325757666011117 := by
  unfold tailWord_1431496
  simp only [CollatzResearch.WordTrace]
  refine ⟨26105474210970973448929171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34807298947961297931905561 26105474210970973448929171)
  ·
    refine ⟨39158211316456460173393757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26105474210970973448929171 39158211316456460173393757)
    ·
      refine ⟨14684329243671172565022659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39158211316456460173393757 14684329243671172565022659)
      ·
        refine ⟨22026493865506758847533989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684329243671172565022659 22026493865506758847533989)
        ·
          refine ⟨4129967599782517283912623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22026493865506758847533989 4129967599782517283912623)
          ·
            refine ⟨6194951399673775925868935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129967599782517283912623 6194951399673775925868935)
            ·
              refine ⟨9292427099510663888803403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194951399673775925868935 9292427099510663888803403)
              ·
                refine ⟨13938640649265995833205105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9292427099510663888803403 13938640649265995833205105)
                ·
                  refine ⟨10453980486949496874903829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13938640649265995833205105 10453980486949496874903829)
                  ·
                    refine ⟨490030335325757666011117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10453980486949496874903829 490030335325757666011117)
                    ·
                      rfl

theorem cell22_1431496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_1431496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431496 prefixEnd_1431496 := by exact prefixLift 1431496
  have htrace : WordTrace (prefixWord ++ tailWord_1431496) baseStart_1431496 baseEnd_1431496 := by
    simpa [prefixWord, tailWord_1431496, baseEnd_1431496] using wordTrace_append hprefix tailTrace_1431496
  have hstable : (prefixWord ++ tailWord_1431496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431496).length < 2 ^ (prefixWord ++ tailWord_1431496).sum := by decide
  have hdescent : baseEnd_1431496 < baseStart_1431496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431511 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 5]
def baseStart_1431511 : Nat := 118140960795 + 1431511 * 2 ^ 59
def prefixEnd_1431511 : Nat := 4983230072969 + 3 ^ 40 * 1431511 * 2
def baseEnd_1431511 : Nat := 163345156710767542295357

theorem tailTrace_1431511 : CollatzResearch.WordTrace tailWord_1431511 prefixEnd_1431511 163345156710767542295357 := by
  unfold tailWord_1431511
  simp only [CollatzResearch.WordTrace]
  refine ⟨52211495516887604459654387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34807663677925069639769591 52211495516887604459654387)
  ·
    refine ⟨78317243275331406689481581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52211495516887604459654387 78317243275331406689481581)
    ·
      refine ⟨29368966228249277508555593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78317243275331406689481581 29368966228249277508555593)
      ·
        refine ⟨22026724671186958131416695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29368966228249277508555593 22026724671186958131416695)
        ·
          refine ⟨33040087006780437197125043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22026724671186958131416695 33040087006780437197125043)
          ·
            refine ⟨49560130510170655795687565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33040087006780437197125043 49560130510170655795687565)
            ·
              refine ⟨18585048941313995923382837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49560130510170655795687565 18585048941313995923382837)
              ·
                refine ⟨1742348338248187117817141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18585048941313995923382837 1742348338248187117817141)
                ·
                  refine ⟨163345156710767542295357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742348338248187117817141 163345156710767542295357)
                  ·
                    rfl

theorem cell22_1431511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 5].length) (baseStart_1431511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431511 prefixEnd_1431511 := by exact prefixLift 1431511
  have htrace : WordTrace (prefixWord ++ tailWord_1431511) baseStart_1431511 baseEnd_1431511 := by
    simpa [prefixWord, tailWord_1431511, baseEnd_1431511] using wordTrace_append hprefix tailTrace_1431511
  have hstable : (prefixWord ++ tailWord_1431511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431511).length < 2 ^ (prefixWord ++ tailWord_1431511).sum := by decide
  have hdescent : baseEnd_1431511 < baseStart_1431511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431601 : List Nat := [1, 2, 2, 3, 1, 3, 10]
def baseStart_1431601 : Nat := 118140960795 + 1431601 * 2 ^ 59
def prefixEnd_1431601 : Nat := 4983230072969 + 3 ^ 40 * 1431601 * 2
def baseEnd_1431601 : Nat := 18150602924873051560585

theorem tailTrace_1431601 : CollatzResearch.WordTrace tailWord_1431601 prefixEnd_1431601 18150602924873051560585 := by
  unfold tailWord_1431601
  simp only [CollatzResearch.WordTrace]
  refine ⟨52214778086561549830430657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34809852057707699886953771 52214778086561549830430657)
  ·
    refine ⟨39161083564921162372822993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52214778086561549830430657 39161083564921162372822993)
    ·
      refine ⟨29370812673690871779617245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39161083564921162372822993 29370812673690871779617245)
      ·
        refine ⟨11014054752634076917356467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29370812673690871779617245 11014054752634076917356467)
        ·
          refine ⟨16521082128951115376034701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11014054752634076917356467 16521082128951115376034701)
          ·
            refine ⟨6195405798356668266013013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16521082128951115376034701 6195405798356668266013013)
            ·
              refine ⟨18150602924873051560585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6195405798356668266013013 18150602924873051560585)
              ·
                rfl

theorem cell22_1431601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 10].length) (baseStart_1431601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431601 prefixEnd_1431601 := by exact prefixLift 1431601
  have htrace : WordTrace (prefixWord ++ tailWord_1431601) baseStart_1431601 baseEnd_1431601 := by
    simpa [prefixWord, tailWord_1431601, baseEnd_1431601] using wordTrace_append hprefix tailTrace_1431601
  have hstable : (prefixWord ++ tailWord_1431601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431601).length < 2 ^ (prefixWord ++ tailWord_1431601).sum := by decide
  have hdescent : baseEnd_1431601 < baseStart_1431601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431631 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_1431631 : Nat := 118140960795 + 1431631 * 2 ^ 59
def prefixEnd_1431631 : Nat := 4983230072969 + 3 ^ 40 * 1431631 * 2
def baseEnd_1431631 : Nat := 490076548584662313885703

theorem tailTrace_1431631 : CollatzResearch.WordTrace tailWord_1431631 prefixEnd_1431631 490076548584662313885703 := by
  unfold tailWord_1431631
  simp only [CollatzResearch.WordTrace]
  refine ⟨52215872276452864954022747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34810581517635243302681831 52215872276452864954022747)
  ·
    refine ⟨78323808414679297431034121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52215872276452864954022747 78323808414679297431034121)
    ·
      refine ⟨58742856311009473073275591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78323808414679297431034121 58742856311009473073275591)
      ·
        refine ⟨88114284466514209609913387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58742856311009473073275591 88114284466514209609913387)
        ·
          refine ⟨132171426699771314414870081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88114284466514209609913387 132171426699771314414870081)
          ·
            refine ⟨99128570024828485811152561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132171426699771314414870081 99128570024828485811152561)
            ·
              refine ⟨74346427518621364358364421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99128570024828485811152561 74346427518621364358364421)
              ·
                refine ⟨13939955159741505817193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74346427518621364358364421 13939955159741505817193329)
                ·
                  refine ⟨10454966369806129362894997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13939955159741505817193329 10454966369806129362894997)
                  ·
                    refine ⟨490076548584662313885703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10454966369806129362894997 490076548584662313885703)
                    ·
                      rfl

theorem cell22_1431631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_1431631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431631 prefixEnd_1431631 := by exact prefixLift 1431631
  have htrace : WordTrace (prefixWord ++ tailWord_1431631) baseStart_1431631 baseEnd_1431631 := by
    simpa [prefixWord, tailWord_1431631, baseEnd_1431631] using wordTrace_append hprefix tailTrace_1431631
  have hstable : (prefixWord ++ tailWord_1431631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431631).length < 2 ^ (prefixWord ++ tailWord_1431631).sum := by decide
  have hdescent : baseEnd_1431631 < baseStart_1431631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431633 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_1431633 : Nat := 118140960795 + 1431633 * 2 ^ 59
def prefixEnd_1431633 : Nat := 4983230072969 + 3 ^ 40 * 1431633 * 2
def baseEnd_1431633 : Nat := 490077233225534975335697

theorem tailTrace_1431633 : CollatzResearch.WordTrace tailWord_1431633 prefixEnd_1431633 490077233225534975335697 := by
  unfold tailWord_1431633
  simp only [CollatzResearch.WordTrace]
  refine ⟨52215945222445619295595553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34810630148297079530397035 52215945222445619295595553)
  ·
    refine ⟨39161958916834214471696665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52215945222445619295595553 39161958916834214471696665)
    ·
      refine ⟨29371469187625660853772499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39161958916834214471696665 29371469187625660853772499)
      ·
        refine ⟨44057203781438491280658749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29371469187625660853772499 44057203781438491280658749)
        ·
          refine ⟨16521451418039434230247031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44057203781438491280658749 16521451418039434230247031)
          ·
            refine ⟨24782177127059151345370547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16521451418039434230247031 24782177127059151345370547)
            ·
              refine ⟨37173265690588727018055821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24782177127059151345370547 37173265690588727018055821)
              ·
                refine ⟨13939974633970772631770933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37173265690588727018055821 13939974633970772631770933)
                ·
                  refine ⟨1306872621934759934228525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13939974633970772631770933 1306872621934759934228525)
                  ·
                    refine ⟨490077233225534975335697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306872621934759934228525 490077233225534975335697)
                    ·
                      rfl

theorem cell22_1431633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_1431633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431633 prefixEnd_1431633 := by exact prefixLift 1431633
  have htrace : WordTrace (prefixWord ++ tailWord_1431633) baseStart_1431633 baseEnd_1431633 := by
    simpa [prefixWord, tailWord_1431633, baseEnd_1431633] using wordTrace_append hprefix tailTrace_1431633
  have hstable : (prefixWord ++ tailWord_1431633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431633).length < 2 ^ (prefixWord ++ tailWord_1431633).sum := by decide
  have hdescent : baseEnd_1431633 < baseStart_1431633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431663 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 5]
def baseStart_1431663 : Nat := 118140960795 + 1431663 * 2 ^ 59
def prefixEnd_1431663 : Nat := 4983230072969 + 3 ^ 40 * 1431663 * 2
def baseEnd_1431663 : Nat := 163362500946208299028535

theorem tailTrace_1431663 : CollatzResearch.WordTrace tailWord_1431663 prefixEnd_1431663 163362500946208299028535 := by
  unfold tailWord_1431663
  simp only [CollatzResearch.WordTrace]
  refine ⟨52217039412336934419187643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34811359608224622946125095 52217039412336934419187643)
  ·
    refine ⟨78325559118505401628781465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52217039412336934419187643 78325559118505401628781465)
    ·
      refine ⟨58744169338879051221586099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78325559118505401628781465 58744169338879051221586099)
      ·
        refine ⟨88116254008318576832379149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58744169338879051221586099 88116254008318576832379149)
        ·
          refine ⟨33043595253119466312142181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88116254008318576832379149 33043595253119466312142181)
          ·
            refine ⟨6195674109959899933526659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33043595253119466312142181 6195674109959899933526659)
            ·
              refine ⟨9293511164939849900289989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195674109959899933526659 9293511164939849900289989)
              ·
                refine ⟨1742533343426221856304373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9293511164939849900289989 1742533343426221856304373)
                ·
                  refine ⟨163362500946208299028535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742533343426221856304373 163362500946208299028535)
                  ·
                    rfl

theorem cell22_1431663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 5].length) (baseStart_1431663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431663 prefixEnd_1431663 := by exact prefixLift 1431663
  have htrace : WordTrace (prefixWord ++ tailWord_1431663) baseStart_1431663 baseEnd_1431663 := by
    simpa [prefixWord, tailWord_1431663, baseEnd_1431663] using wordTrace_append hprefix tailTrace_1431663
  have hstable : (prefixWord ++ tailWord_1431663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431663).length < 2 ^ (prefixWord ++ tailWord_1431663).sum := by decide
  have hdescent : baseEnd_1431663 < baseStart_1431663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431708 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_1431708 : Nat := 118140960795 + 1431708 * 2 ^ 59
def prefixEnd_1431708 : Nat := 4983230072969 + 3 ^ 40 * 1431708 * 2
def baseEnd_1431708 : Nat := 163367635752753259903489

theorem tailTrace_1431708 : CollatzResearch.WordTrace tailWord_1431708 prefixEnd_1431708 163367635752753259903489 := by
  unfold tailWord_1431708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26109340348586953552287889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34812453798115938069717185 26109340348586953552287889)
  ·
    refine ⟨19582005261440215164215917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26109340348586953552287889 19582005261440215164215917)
    ·
      refine ⟨7343251973040080686580969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19582005261440215164215917 7343251973040080686580969)
      ·
        refine ⟨5507438979780060514935727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7343251973040080686580969 5507438979780060514935727)
        ·
          refine ⟨8261158469670090772403591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5507438979780060514935727 8261158469670090772403591)
          ·
            refine ⟨12391737704505136158605387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261158469670090772403591 12391737704505136158605387)
            ·
              refine ⟨18587606556757704237908081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12391737704505136158605387 18587606556757704237908081)
              ·
                refine ⟨13940704917568278178431061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18587606556757704237908081 13940704917568278178431061)
                ·
                  refine ⟨163367635752753259903489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13940704917568278178431061 163367635752753259903489)
                  ·
                    rfl

theorem cell22_1431708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_1431708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431708 prefixEnd_1431708 := by exact prefixLift 1431708
  have htrace : WordTrace (prefixWord ++ tailWord_1431708) baseStart_1431708 baseEnd_1431708 := by
    simpa [prefixWord, tailWord_1431708, baseEnd_1431708] using wordTrace_append hprefix tailTrace_1431708
  have hstable : (prefixWord ++ tailWord_1431708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431708).length < 2 ^ (prefixWord ++ tailWord_1431708).sum := by decide
  have hdescent : baseEnd_1431708 < baseStart_1431708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431725 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1431725 : Nat := 118140960795 + 1431725 * 2 ^ 59
def prefixEnd_1431725 : Nat := 4983230072969 + 3 ^ 40 * 1431725 * 2
def baseEnd_1431725 : Nat := 163369575568559134011805

theorem tailTrace_1431725 : CollatzResearch.WordTrace tailWord_1431725 prefixEnd_1431725 163369575568559134011805 := by
  unfold tailWord_1431725
  simp only [CollatzResearch.WordTrace]
  refine ⟨52219300738112319007944629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34812867158741546005296419 52219300738112319007944629)
  ·
    refine ⟨4895559444198029906994809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52219300738112319007944629 4895559444198029906994809)
    ·
      refine ⟨3671669583148522430246107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4895559444198029906994809 3671669583148522430246107)
      ·
        refine ⟨5507504374722783645369161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671669583148522430246107 5507504374722783645369161)
        ·
          refine ⟨4130628281042087734026871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507504374722783645369161 4130628281042087734026871)
          ·
            refine ⟨6195942421563131601040307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130628281042087734026871 6195942421563131601040307)
            ·
              refine ⟨9293913632344697401560461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195942421563131601040307 9293913632344697401560461)
              ·
                refine ⟨3485217612129261525585173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9293913632344697401560461 3485217612129261525585173)
                ·
                  refine ⟨163369575568559134011805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3485217612129261525585173 163369575568559134011805)
                  ·
                    rfl

theorem cell22_1431725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1431725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431725 prefixEnd_1431725 := by exact prefixLift 1431725
  have htrace : WordTrace (prefixWord ++ tailWord_1431725) baseStart_1431725 baseEnd_1431725 := by
    simpa [prefixWord, tailWord_1431725, baseEnd_1431725] using wordTrace_append hprefix tailTrace_1431725
  have hstable : (prefixWord ++ tailWord_1431725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431725).length < 2 ^ (prefixWord ++ tailWord_1431725).sum := by decide
  have hdescent : baseEnd_1431725 < baseStart_1431725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431738 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1431738 : Nat := 118140960795 + 1431738 * 2 ^ 59
def prefixEnd_1431738 : Nat := 4983230072969 + 3 ^ 40 * 1431738 * 2
def baseEnd_1431738 : Nat := 490113176871349701460375

theorem tailTrace_1431738 : CollatzResearch.WordTrace tailWord_1431738 prefixEnd_1431738 490113176871349701460375 := by
  unfold tailWord_1431738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13054943721766305557041967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34813183258043481485445245 13054943721766305557041967)
  ·
    refine ⟨19582415582649458335562951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13054943721766305557041967 19582415582649458335562951)
    ·
      refine ⟨29373623373974187503344427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19582415582649458335562951 29373623373974187503344427)
      ·
        refine ⟨44060435060961281255016641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29373623373974187503344427 44060435060961281255016641)
        ·
          refine ⟨33045326295720960941262481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44060435060961281255016641 33045326295720960941262481)
          ·
            refine ⟨24783994721790720705946861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33045326295720960941262481 24783994721790720705946861)
            ·
              refine ⟨9293998020671520264730073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24783994721790720705946861 9293998020671520264730073)
              ·
                refine ⟨6970498515503640198547555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9293998020671520264730073 6970498515503640198547555)
                ·
                  refine ⟨10455747773255460297821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970498515503640198547555 10455747773255460297821333)
                  ·
                    refine ⟨490113176871349701460375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10455747773255460297821333 490113176871349701460375)
                    ·
                      rfl

theorem cell22_1431738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1431738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431738 prefixEnd_1431738 := by exact prefixLift 1431738
  have htrace : WordTrace (prefixWord ++ tailWord_1431738) baseStart_1431738 baseEnd_1431738 := by
    simpa [prefixWord, tailWord_1431738, baseEnd_1431738] using wordTrace_append hprefix tailTrace_1431738
  have hstable : (prefixWord ++ tailWord_1431738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431738).length < 2 ^ (prefixWord ++ tailWord_1431738).sum := by decide
  have hdescent : baseEnd_1431738 < baseStart_1431738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431813 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1431813 : Nat := 118140960795 + 1431813 * 2 ^ 59
def prefixEnd_1431813 : Nat := 4983230072969 + 3 ^ 40 * 1431813 * 2
def baseEnd_1431813 : Nat := 490138850904074505835145

theorem tailTrace_1431813 : CollatzResearch.WordTrace tailWord_1431813 prefixEnd_1431813 490138850904074505835145 := by
  unfold tailWord_1431813
  simp only [CollatzResearch.WordTrace]
  refine ⟨52222510361793510037148093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34815006907862340024765395 52222510361793510037148093)
  ·
    refine ⟨19583441385672566263930535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52222510361793510037148093 19583441385672566263930535)
    ·
      refine ⟨29375162078508849395895803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19583441385672566263930535 29375162078508849395895803)
      ·
        refine ⟨44062743117763274093843705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29375162078508849395895803 44062743117763274093843705)
        ·
          refine ⟨33047057338322455570382779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44062743117763274093843705 33047057338322455570382779)
          ·
            refine ⟨49570586007483683355574169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33047057338322455570382779 49570586007483683355574169)
            ·
              refine ⟨37177939505612762516680627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49570586007483683355574169 37177939505612762516680627)
              ·
                refine ⟨55766909258419143775020941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37177939505612762516680627 55766909258419143775020941)
                ·
                  refine ⟨20912590971907178915632853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55766909258419143775020941 20912590971907178915632853)
                  ·
                    refine ⟨490138850904074505835145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20912590971907178915632853 490138850904074505835145)
                    ·
                      rfl

theorem cell22_1431813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1431813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431813 prefixEnd_1431813 := by exact prefixLift 1431813
  have htrace : WordTrace (prefixWord ++ tailWord_1431813) baseStart_1431813 baseEnd_1431813 := by
    simpa [prefixWord, tailWord_1431813, baseEnd_1431813] using wordTrace_append hprefix tailTrace_1431813
  have hstable : (prefixWord ++ tailWord_1431813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431813).length < 2 ^ (prefixWord ++ tailWord_1431813).sum := by decide
  have hdescent : baseEnd_1431813 < baseStart_1431813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431875 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_1431875 : Nat := 118140960795 + 1431875 * 2 ^ 59
def prefixEnd_1431875 : Nat := 4983230072969 + 3 ^ 40 * 1431875 * 2
def baseEnd_1431875 : Nat := 490160074771127010784955

theorem tailTrace_1431875 : CollatzResearch.WordTrace tailWord_1431875 prefixEnd_1431875 490160074771127010784955 := by
  unfold tailWord_1431875
  simp only [CollatzResearch.WordTrace]
  refine ⟨52224771687568894625905079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34816514458379263083936719 52224771687568894625905079)
  ·
    refine ⟨78337157531353341938857619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52224771687568894625905079 78337157531353341938857619)
    ·
      refine ⟨117505736297030012908286429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78337157531353341938857619 117505736297030012908286429)
      ·
        refine ⟨44064651111386254840607411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117505736297030012908286429 44064651111386254840607411)
        ·
          refine ⟨66096976667079382260911117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44064651111386254840607411 66096976667079382260911117)
          ·
            refine ⟨24786366250154768347841669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66096976667079382260911117 24786366250154768347841669)
            ·
              refine ⟨4647443671904019065220313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24786366250154768347841669 4647443671904019065220313)
              ·
                refine ⟨3485582753928014298915235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647443671904019065220313 3485582753928014298915235)
                ·
                  refine ⟨5228374130892021448372853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485582753928014298915235 5228374130892021448372853)
                  ·
                    refine ⟨490160074771127010784955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5228374130892021448372853 490160074771127010784955)
                    ·
                      rfl

theorem cell22_1431875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_1431875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431875 prefixEnd_1431875 := by exact prefixLift 1431875
  have htrace : WordTrace (prefixWord ++ tailWord_1431875) baseStart_1431875 baseEnd_1431875 := by
    simpa [prefixWord, tailWord_1431875, baseEnd_1431875] using wordTrace_append hprefix tailTrace_1431875
  have hstable : (prefixWord ++ tailWord_1431875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431875).length < 2 ^ (prefixWord ++ tailWord_1431875).sum := by decide
  have hdescent : baseEnd_1431875 < baseStart_1431875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431922 : List Nat := [3, 2, 1, 2, 1, 3, 4, 6]
def baseStart_1431922 : Nat := 118140960795 + 1431922 * 2 ^ 59
def prefixEnd_1431922 : Nat := 4983230072969 + 3 ^ 40 * 1431922 * 2
def baseEnd_1431922 : Nat := 54464018203514950539979

theorem tailTrace_1431922 : CollatzResearch.WordTrace tailWord_1431922 prefixEnd_1431922 54464018203514950539979 := by
  unfold tailWord_1431922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13056621479599655413216505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34817657278932414435244013 13056621479599655413216505)
  ·
    refine ⟨9792466109699741559912379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13056621479599655413216505 9792466109699741559912379)
    ·
      refine ⟨14688699164549612339868569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792466109699741559912379 14688699164549612339868569)
      ·
        refine ⟨11016524373412209254901427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14688699164549612339868569 11016524373412209254901427)
        ·
          refine ⟨16524786560118313882352141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016524373412209254901427 16524786560118313882352141)
          ·
            refine ⟨6196794960044367705882053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16524786560118313882352141 6196794960044367705882053)
            ·
              refine ⟨1161899055008318944852885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6196794960044367705882053 1161899055008318944852885)
              ·
                refine ⟨54464018203514950539979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1161899055008318944852885 54464018203514950539979)
                ·
                  rfl

theorem cell22_1431922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_1431922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431922 prefixEnd_1431922 := by exact prefixLift 1431922
  have htrace : WordTrace (prefixWord ++ tailWord_1431922) baseStart_1431922 baseEnd_1431922 := by
    simpa [prefixWord, tailWord_1431922, baseEnd_1431922] using wordTrace_append hprefix tailTrace_1431922
  have hstable : (prefixWord ++ tailWord_1431922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431922).length < 2 ^ (prefixWord ++ tailWord_1431922).sum := by decide
  have hdescent : baseEnd_1431922 < baseStart_1431922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431967 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 5]
def baseStart_1431967 : Nat := 118140960795 + 1431967 * 2 ^ 59
def prefixEnd_1431967 : Nat := 4983230072969 + 3 ^ 40 * 1431967 * 2
def baseEnd_1431967 : Nat := 163397189417089812494891

theorem tailTrace_1431967 : CollatzResearch.WordTrace tailWord_1431967 prefixEnd_1431967 163397189417089812494891 := by
  unfold tailWord_1431967
  simp only [CollatzResearch.WordTrace]
  refine ⟨52228127203235594338254155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34818751468823729558836103 52228127203235594338254155)
  ·
    refine ⟨78342190804853391507381233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52228127203235594338254155 78342190804853391507381233)
    ·
      refine ⟨58756643103640043630535925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78342190804853391507381233 58756643103640043630535925)
      ·
        refine ⟨5508435290966254090362743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58756643103640043630535925 5508435290966254090362743)
        ·
          refine ⟨8262652936449381135544115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508435290966254090362743 8262652936449381135544115)
          ·
            refine ⟨12393979404674071703316173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262652936449381135544115 12393979404674071703316173)
            ·
              refine ⟨4647742276752776888743565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12393979404674071703316173 4647742276752776888743565)
              ·
                refine ⟨1742903353782291333278837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4647742276752776888743565 1742903353782291333278837)
                ·
                  refine ⟨163397189417089812494891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742903353782291333278837 163397189417089812494891)
                  ·
                    rfl

theorem cell22_1431967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 5].length) (baseStart_1431967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1431967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1431967 prefixEnd_1431967 := by exact prefixLift 1431967
  have htrace : WordTrace (prefixWord ++ tailWord_1431967) baseStart_1431967 baseEnd_1431967 := by
    simpa [prefixWord, tailWord_1431967, baseEnd_1431967] using wordTrace_append hprefix tailTrace_1431967
  have hstable : (prefixWord ++ tailWord_1431967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431967).length < 2 ^ (prefixWord ++ tailWord_1431967).sum := by decide
  have hdescent : baseEnd_1431967 < baseStart_1431967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432046 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_1432046 : Nat := 118140960795 + 1432046 * 2 ^ 59
def prefixEnd_1432046 : Nat := 4983230072969 + 3 ^ 40 * 1432046 * 2
def baseEnd_1432046 : Nat := 163406203855246521586477

theorem tailTrace_1432046 : CollatzResearch.WordTrace tailWord_1432046 prefixEnd_1432046 163406203855246521586477 := by
  unfold tailWord_1432046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528876071243673853797499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34820672379966260553586661 6528876071243673853797499)
  ·
    refine ⟨9793314106865510780696249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6528876071243673853797499 9793314106865510780696249)
    ·
      refine ⟨7344985580149133085522187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9793314106865510780696249 7344985580149133085522187)
      ·
        refine ⟨11017478370223699628283281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7344985580149133085522187 11017478370223699628283281)
        ·
          refine ⟨8263108777667774721212461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11017478370223699628283281 8263108777667774721212461)
          ·
            refine ⟨3098665791625415520454673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8263108777667774721212461 3098665791625415520454673)
            ·
              refine ⟨2323999343719061640341005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098665791625415520454673 2323999343719061640341005)
              ·
                refine ⟨871499753894648115127877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2323999343719061640341005 871499753894648115127877)
                ·
                  refine ⟨163406203855246521586477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871499753894648115127877 163406203855246521586477)
                  ·
                    rfl

theorem cell22_1432046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_1432046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432046 prefixEnd_1432046 := by exact prefixLift 1432046
  have htrace : WordTrace (prefixWord ++ tailWord_1432046) baseStart_1432046 baseEnd_1432046 := by
    simpa [prefixWord, tailWord_1432046, baseEnd_1432046] using wordTrace_append hprefix tailTrace_1432046
  have hstable : (prefixWord ++ tailWord_1432046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432046).length < 2 ^ (prefixWord ++ tailWord_1432046).sum := by decide
  have hdescent : baseEnd_1432046 < baseStart_1432046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432078 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1432078 : Nat := 118140960795 + 1432078 * 2 ^ 59
def prefixEnd_1432078 : Nat := 4983230072969 + 3 ^ 40 * 1432078 * 2
def baseEnd_1432078 : Nat := 490229565819702147959333

theorem tailTrace_1432078 : CollatzResearch.WordTrace tailWord_1432078 prefixEnd_1432078 490229565819702147959333 := by
  unfold tailWord_1432078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529021963229182536943111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34821450470555640197029925 6529021963229182536943111)
  ·
    refine ⟨9793532944843773805414667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6529021963229182536943111 9793532944843773805414667)
    ·
      refine ⟨14690299417265660708122001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9793532944843773805414667 14690299417265660708122001)
      ·
        refine ⟨11017724562949245531091501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14690299417265660708122001 11017724562949245531091501)
        ·
          refine ⟨4131646711105967074159313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11017724562949245531091501 4131646711105967074159313)
          ·
            refine ⟨3098735033329475305619485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131646711105967074159313 3098735033329475305619485)
            ·
              refine ⟨1162025637498553239607307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3098735033329475305619485 1162025637498553239607307)
              ·
                refine ⟨1743038456247829859410961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162025637498553239607307 1743038456247829859410961)
                ·
                  refine ⟨1307278842185872394558221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1743038456247829859410961 1307278842185872394558221)
                  ·
                    refine ⟨490229565819702147959333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307278842185872394558221 490229565819702147959333)
                    ·
                      rfl

theorem cell22_1432078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1432078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432078 prefixEnd_1432078 := by exact prefixLift 1432078
  have htrace : WordTrace (prefixWord ++ tailWord_1432078) baseStart_1432078 baseEnd_1432078 := by
    simpa [prefixWord, tailWord_1432078, baseEnd_1432078] using wordTrace_append hprefix tailTrace_1432078
  have hstable : (prefixWord ++ tailWord_1432078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432078).length < 2 ^ (prefixWord ++ tailWord_1432078).sum := by decide
  have hdescent : baseEnd_1432078 < baseStart_1432078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432177 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_1432177 : Nat := 118140960795 + 1432177 * 2 ^ 59
def prefixEnd_1432177 : Nat := 4983230072969 + 3 ^ 40 * 1432177 * 2
def baseEnd_1432177 : Nat := 490263455542898889734029

theorem tailTrace_1432177 : CollatzResearch.WordTrace tailWord_1432177 prefixEnd_1432177 490263455542898889734029 := by
  unfold tailWord_1432177
  simp only [CollatzResearch.WordTrace]
  refine ⟨52235786532474800203398785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34823857688316533468932523 52235786532474800203398785)
  ·
    refine ⟨39176839899356100152549089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52235786532474800203398785 39176839899356100152549089)
    ·
      refine ⟨29382629924517075114411817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39176839899356100152549089 29382629924517075114411817)
      ·
        refine ⟨22036972443387806335808863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29382629924517075114411817 22036972443387806335808863)
        ·
          refine ⟨33055458665081709503713295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22036972443387806335808863 33055458665081709503713295)
          ·
            refine ⟨49583187997622564255569943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33055458665081709503713295 49583187997622564255569943)
            ·
              refine ⟨74374781996433846383354915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49583187997622564255569943 74374781996433846383354915)
              ·
                refine ⟨111562172994650769575032373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74374781996433846383354915 111562172994650769575032373)
                ·
                  refine ⟨10458953718248509647659285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111562172994650769575032373 10458953718248509647659285)
                  ·
                    refine ⟨490263455542898889734029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10458953718248509647659285 490263455542898889734029)
                    ·
                      rfl

theorem cell22_1432177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_1432177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432177 prefixEnd_1432177 := by exact prefixLift 1432177
  have htrace : WordTrace (prefixWord ++ tailWord_1432177) baseStart_1432177 baseEnd_1432177 := by
    simpa [prefixWord, tailWord_1432177, baseEnd_1432177] using wordTrace_append hprefix tailTrace_1432177
  have hstable : (prefixWord ++ tailWord_1432177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432177).length < 2 ^ (prefixWord ++ tailWord_1432177).sum := by decide
  have hdescent : baseEnd_1432177 < baseStart_1432177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432196 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1432196 : Nat := 118140960795 + 1432196 * 2 ^ 59
def prefixEnd_1432196 : Nat := 4983230072969 + 3 ^ 40 * 1432196 * 2
def baseEnd_1432196 : Nat := 490269959631189173508971

theorem tailTrace_1432196 : CollatzResearch.WordTrace tailWord_1432196 prefixEnd_1432196 490269959631189173508971 := by
  unfold tailWord_1432196
  simp only [CollatzResearch.WordTrace]
  refine ⟨26118239759702983224170221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34824319679603977632226961 26118239759702983224170221)
  ·
    refine ⟨9794339909888618709063833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26118239759702983224170221 9794339909888618709063833)
    ·
      refine ⟨7345754932416464031797875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9794339909888618709063833 7345754932416464031797875)
      ·
        refine ⟨11018632398624696047696813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345754932416464031797875 11018632398624696047696813)
        ·
          refine ⟨4131987149484261017886305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11018632398624696047696813 4131987149484261017886305)
          ·
            refine ⟨3098990362113195763414729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131987149484261017886305 3098990362113195763414729)
            ·
              refine ⟨2324242771584896822561047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098990362113195763414729 2324242771584896822561047)
              ·
                refine ⟨3486364157377345233841571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324242771584896822561047 3486364157377345233841571)
                ·
                  refine ⟨5229546236066017850762357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486364157377345233841571 5229546236066017850762357)
                  ·
                    refine ⟨490269959631189173508971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5229546236066017850762357 490269959631189173508971)
                    ·
                      rfl

theorem cell22_1432196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1432196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432196 prefixEnd_1432196 := by exact prefixLift 1432196
  have htrace : WordTrace (prefixWord ++ tailWord_1432196) baseStart_1432196 baseEnd_1432196 := by
    simpa [prefixWord, tailWord_1432196, baseEnd_1432196] using wordTrace_append hprefix tailTrace_1432196
  have hstable : (prefixWord ++ tailWord_1432196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432196).length < 2 ^ (prefixWord ++ tailWord_1432196).sum := by decide
  have hdescent : baseEnd_1432196 < baseStart_1432196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_1432207 : Nat := 118140960795 + 1432207 * 2 ^ 59
def prefixEnd_1432207 : Nat := 4983230072969 + 3 ^ 40 * 1432207 * 2
def baseEnd_1432207 : Nat := 490273725155988811483937

theorem tailTrace_1432207 : CollatzResearch.WordTrace tailWord_1432207 prefixEnd_1432207 490273725155988811483937 := by
  unfold tailWord_1432207
  simp only [CollatzResearch.WordTrace]
  refine ⟨52236880722366115326990875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34824587148244076884660583 52236880722366115326990875)
  ·
    refine ⟨78355321083549172990486313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52236880722366115326990875 78355321083549172990486313)
    ·
      refine ⟨58766490812661879742864735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78355321083549172990486313 58766490812661879742864735)
      ·
        refine ⟨88149736218992819614297103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58766490812661879742864735 88149736218992819614297103)
        ·
          refine ⟨132224604328489229421445655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88149736218992819614297103 132224604328489229421445655)
          ·
            refine ⟨198336906492733844132168483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132224604328489229421445655 198336906492733844132168483)
            ·
              refine ⟨297505359739100766198252725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198336906492733844132168483 297505359739100766198252725)
              ·
                refine ⟨27891127475540696831086193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297505359739100766198252725 27891127475540696831086193)
                ·
                  refine ⟨20918345606655522623314645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27891127475540696831086193 20918345606655522623314645)
                  ·
                    refine ⟨490273725155988811483937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20918345606655522623314645 490273725155988811483937)
                    ·
                      rfl

theorem cell22_1432207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_1432207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432207 prefixEnd_1432207 := by exact prefixLift 1432207
  have htrace : WordTrace (prefixWord ++ tailWord_1432207) baseStart_1432207 baseEnd_1432207 := by
    simpa [prefixWord, tailWord_1432207, baseEnd_1432207] using wordTrace_append hprefix tailTrace_1432207
  have hstable : (prefixWord ++ tailWord_1432207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432207).length < 2 ^ (prefixWord ++ tailWord_1432207).sum := by decide
  have hdescent : baseEnd_1432207 < baseStart_1432207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432301 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1432301 : Nat := 118140960795 + 1432301 * 2 ^ 59
def prefixEnd_1432301 : Nat := 4983230072969 + 3 ^ 40 * 1432301 * 2
def baseEnd_1432301 : Nat := 490305903277003899633649

theorem tailTrace_1432301 : CollatzResearch.WordTrace tailWord_1432301 prefixEnd_1432301 490305903277003899633649 := by
  unfold tailWord_1432301
  simp only [CollatzResearch.WordTrace]
  refine ⟨52240309184025569380912757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34826872789350379587275171 52240309184025569380912757)
  ·
    refine ⟨4897528986002397129460571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52240309184025569380912757 4897528986002397129460571)
    ·
      refine ⟨7346293479003595694190857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897528986002397129460571 7346293479003595694190857)
      ·
        refine ⟨5509720109252696770643143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7346293479003595694190857 5509720109252696770643143)
        ·
          refine ⟨8264580163879045155964715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509720109252696770643143 8264580163879045155964715)
          ·
            refine ⟨12396870245818567733947073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264580163879045155964715 12396870245818567733947073)
            ·
              refine ⟨9297652684363925800460305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12396870245818567733947073 9297652684363925800460305)
              ·
                refine ⟨6973239513272944350345229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297652684363925800460305 6973239513272944350345229)
                ·
                  refine ⟨2614964817477354131379461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6973239513272944350345229 2614964817477354131379461)
                  ·
                    refine ⟨490305903277003899633649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2614964817477354131379461 490305903277003899633649)
                    ·
                      rfl

theorem cell22_1432301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1432301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432301 prefixEnd_1432301 := by exact prefixLift 1432301
  have htrace : WordTrace (prefixWord ++ tailWord_1432301) baseStart_1432301 baseEnd_1432301 := by
    simpa [prefixWord, tailWord_1432301, baseEnd_1432301] using wordTrace_append hprefix tailTrace_1432301
  have hstable : (prefixWord ++ tailWord_1432301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432301).length < 2 ^ (prefixWord ++ tailWord_1432301).sum := by decide
  have hdescent : baseEnd_1432301 < baseStart_1432301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432318 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1432318 : Nat := 118140960795 + 1432318 * 2 ^ 59
def prefixEnd_1432318 : Nat := 4983230072969 + 3 ^ 40 * 1432318 * 2
def baseEnd_1432318 : Nat := 490311722724421521958597

theorem tailTrace_1432318 : CollatzResearch.WordTrace tailWord_1432318 prefixEnd_1432318 490311722724421521958597 := by
  unfold tailWord_1432318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6530116153120497660535201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34827286149975987522854405 6530116153120497660535201)
  ·
    refine ⟨4897587114840373245401401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6530116153120497660535201 4897587114840373245401401)
    ·
      refine ⟨3673190336130279934051051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4897587114840373245401401 3673190336130279934051051)
      ·
        refine ⟨5509785504195419901076577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673190336130279934051051 5509785504195419901076577)
        ·
          refine ⟨4132339128146564925807433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5509785504195419901076577 4132339128146564925807433)
          ·
            refine ⟨3099254346109923694355575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4132339128146564925807433 3099254346109923694355575)
            ·
              refine ⟨4648881519164885541533363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099254346109923694355575 4648881519164885541533363)
              ·
                refine ⟨6973322278747328312300045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648881519164885541533363 6973322278747328312300045)
                ·
                  refine ⟨2614995854530248117112517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6973322278747328312300045 2614995854530248117112517)
                  ·
                    refine ⟨490311722724421521958597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2614995854530248117112517 490311722724421521958597)
                    ·
                      rfl

theorem cell22_1432318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1432318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432318 prefixEnd_1432318 := by exact prefixLift 1432318
  have htrace : WordTrace (prefixWord ++ tailWord_1432318) baseStart_1432318 baseEnd_1432318 := by
    simpa [prefixWord, tailWord_1432318, baseEnd_1432318] using wordTrace_append hprefix tailTrace_1432318
  have hstable : (prefixWord ++ tailWord_1432318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432318).length < 2 ^ (prefixWord ++ tailWord_1432318).sum := by decide
  have hdescent : baseEnd_1432318 < baseStart_1432318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432329 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_1432329 : Nat := 118140960795 + 1432329 * 2 ^ 59
def prefixEnd_1432329 : Nat := 4983230072969 + 3 ^ 40 * 1432329 * 2
def baseEnd_1432329 : Nat := 490315488249221159933563

theorem tailTrace_1432329 : CollatzResearch.WordTrace tailWord_1432329 prefixEnd_1432329 490315488249221159933563 := by
  unfold tailWord_1432329
  simp only [CollatzResearch.WordTrace]
  refine ⟨52241330427924130162932041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34827553618616086775288027 52241330427924130162932041)
  ·
    refine ⟨39180997820943097622199031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52241330427924130162932041 39180997820943097622199031)
    ·
      refine ⟨58771496731414646433298547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39180997820943097622199031 58771496731414646433298547)
      ·
        refine ⟨88157245097121969649947821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58771496731414646433298547 88157245097121969649947821)
        ·
          refine ⟨33058966911420738618730433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88157245097121969649947821 33058966911420738618730433)
          ·
            refine ⟨24794225183565553964047825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33058966911420738618730433 24794225183565553964047825)
            ·
              refine ⟨18595668887674165473035869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24794225183565553964047825 18595668887674165473035869)
              ·
                refine ⟨6973375832877812052388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18595668887674165473035869 6973375832877812052388451)
                ·
                  refine ⟨10460063749316718078582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973375832877812052388451 10460063749316718078582677)
                  ·
                    refine ⟨490315488249221159933563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10460063749316718078582677 490315488249221159933563)
                    ·
                      rfl

theorem cell22_1432329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_1432329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432329 prefixEnd_1432329 := by exact prefixLift 1432329
  have htrace : WordTrace (prefixWord ++ tailWord_1432329) baseStart_1432329 baseEnd_1432329 := by
    simpa [prefixWord, tailWord_1432329, baseEnd_1432329] using wordTrace_append hprefix tailTrace_1432329
  have hstable : (prefixWord ++ tailWord_1432329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432329).length < 2 ^ (prefixWord ++ tailWord_1432329).sum := by decide
  have hdescent : baseEnd_1432329 < baseStart_1432329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432346 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_1432346 : Nat := 118140960795 + 1432346 * 2 ^ 59
def prefixEnd_1432346 : Nat := 4983230072969 + 3 ^ 40 * 1432346 * 2
def baseEnd_1432346 : Nat := 490321307696638782258511

theorem tailTrace_1432346 : CollatzResearch.WordTrace tailWord_1432346 prefixEnd_1432346 490321307696638782258511 := by
  unfold tailWord_1432346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060487617215635516575223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34827966979241694710867261 13060487617215635516575223)
  ·
    refine ⟨19590731425823453274862835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13060487617215635516575223 19590731425823453274862835)
    ·
      refine ⟨29386097138735179912294253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19590731425823453274862835 29386097138735179912294253)
      ·
        refine ⟨11019786427025692467110345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29386097138735179912294253 11019786427025692467110345)
        ·
          refine ⟨8264839820269269350332759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11019786427025692467110345 8264839820269269350332759)
          ·
            refine ⟨12397259730403904025499139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264839820269269350332759 12397259730403904025499139)
            ·
              refine ⟨18595889595605856038248709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12397259730403904025499139 18595889595605856038248709)
              ·
                refine ⟨3486729299176098007171633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18595889595605856038248709 3486729299176098007171633)
                ·
                  refine ⟨2615046974382073505378725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3486729299176098007171633 2615046974382073505378725)
                  ·
                    refine ⟨490321307696638782258511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615046974382073505378725 490321307696638782258511)
                    ·
                      rfl

theorem cell22_1432346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_1432346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432346 prefixEnd_1432346 := by exact prefixLift 1432346
  have htrace : WordTrace (prefixWord ++ tailWord_1432346) baseStart_1432346 baseEnd_1432346 := by
    simpa [prefixWord, tailWord_1432346, baseEnd_1432346] using wordTrace_append hprefix tailTrace_1432346
  have hstable : (prefixWord ++ tailWord_1432346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432346).length < 2 ^ (prefixWord ++ tailWord_1432346).sum := by decide
  have hdescent : baseEnd_1432346 < baseStart_1432346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432348 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1432348 : Nat := 118140960795 + 1432348 * 2 ^ 59
def prefixEnd_1432348 : Nat := 4983230072969 + 3 ^ 40 * 1432348 * 2
def baseEnd_1432348 : Nat := 490321992337511443708505

theorem tailTrace_1432348 : CollatzResearch.WordTrace tailWord_1432348 prefixEnd_1432348 490321992337511443708505 := by
  unfold tailWord_1432348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26121011707427648203936849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34828015609903530938582465 26121011707427648203936849)
  ·
    refine ⟨19590758780570736152952637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26121011707427648203936849 19590758780570736152952637)
    ·
      refine ⟨7346534542714026057357239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19590758780570736152952637 7346534542714026057357239)
      ·
        refine ⟨11019801814071039086035859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346534542714026057357239 11019801814071039086035859)
        ·
          refine ⟨16529702721106558629053789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019801814071039086035859 16529702721106558629053789)
          ·
            refine ⟨6198638520414959485895171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16529702721106558629053789 6198638520414959485895171)
            ·
              refine ⟨9297957780622439228842757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198638520414959485895171 9297957780622439228842757)
              ·
                refine ⟨1743367083866707355408017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9297957780622439228842757 1743367083866707355408017)
                ·
                  refine ⟨1307525312900030516556013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1743367083866707355408017 1307525312900030516556013)
                  ·
                    refine ⟨490321992337511443708505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307525312900030516556013 490321992337511443708505)
                    ·
                      rfl

theorem cell22_1432348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1432348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432348 prefixEnd_1432348 := by exact prefixLift 1432348
  have htrace : WordTrace (prefixWord ++ tailWord_1432348) baseStart_1432348 baseEnd_1432348 := by
    simpa [prefixWord, tailWord_1432348, baseEnd_1432348] using wordTrace_append hprefix tailTrace_1432348
  have hstable : (prefixWord ++ tailWord_1432348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432348).length < 2 ^ (prefixWord ++ tailWord_1432348).sum := by decide
  have hdescent : baseEnd_1432348 < baseStart_1432348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432378 : List Nat := [3, 1, 1, 1, 6, 1, 3, 6]
def baseStart_1432378 : Nat := 118140960795 + 1432378 * 2 ^ 59
def prefixEnd_1432378 : Nat := 4983230072969 + 3 ^ 40 * 1432378 * 2
def baseEnd_1432378 : Nat := 54481362438955707273157

theorem tailTrace_1432378 : CollatzResearch.WordTrace tailWord_1432378 prefixEnd_1432378 54481362438955707273157 := by
  unfold tailWord_1432378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060779401186652882866447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34828745069831074354310525 13060779401186652882866447)
  ·
    refine ⟨19591169101779979324299671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13060779401186652882866447 19591169101779979324299671)
    ·
      refine ⟨29386753652669968986449507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19591169101779979324299671 29386753652669968986449507)
      ·
        refine ⟨44080130479004953479674261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29386753652669968986449507 44080130479004953479674261)
        ·
          refine ⟨2066256116203357194359731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44080130479004953479674261 2066256116203357194359731)
          ·
            refine ⟨3099384174305035791539597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066256116203357194359731 3099384174305035791539597)
            ·
              refine ⟨1162269065364388421827349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3099384174305035791539597 1162269065364388421827349)
              ·
                refine ⟨54481362438955707273157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1162269065364388421827349 54481362438955707273157)
                ·
                  rfl

theorem cell22_1432378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_1432378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432378 prefixEnd_1432378 := by exact prefixLift 1432378
  have htrace : WordTrace (prefixWord ++ tailWord_1432378) baseStart_1432378 baseEnd_1432378 := by
    simpa [prefixWord, tailWord_1432378, baseEnd_1432378] using wordTrace_append hprefix tailTrace_1432378
  have hstable : (prefixWord ++ tailWord_1432378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432378).length < 2 ^ (prefixWord ++ tailWord_1432378).sum := by decide
  have hdescent : baseEnd_1432378 < baseStart_1432378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432410 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_1432410 : Nat := 118140960795 + 1432410 * 2 ^ 59
def prefixEnd_1432410 : Nat := 4983230072969 + 3 ^ 40 * 1432410 * 2
def baseEnd_1432410 : Nat := 490343216204563948658315

theorem tailTrace_1432410 : CollatzResearch.WordTrace tailWord_1432410 prefixEnd_1432410 490343216204563948658315 := by
  unfold tailWord_1432410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061071185157670249157671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34829523160420453997753789 13061071185157670249157671)
  ·
    refine ⟨19591606777736505373736507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13061071185157670249157671 19591606777736505373736507)
    ·
      refine ⟨29387410166604758060604761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19591606777736505373736507 29387410166604758060604761)
      ·
        refine ⟨22040557624953568545453571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29387410166604758060604761 22040557624953568545453571)
        ·
          refine ⟨33060836437430352818180357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22040557624953568545453571 33060836437430352818180357)
          ·
            refine ⟨6198906832018191153408817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33060836437430352818180357 6198906832018191153408817)
            ·
              refine ⟨4649180124013643365056613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6198906832018191153408817 4649180124013643365056613)
              ·
                refine ⟨871721273252558130948115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4649180124013643365056613 871721273252558130948115)
                ·
                  refine ⟨1307581909878837196422173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871721273252558130948115 1307581909878837196422173)
                  ·
                    refine ⟨490343216204563948658315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307581909878837196422173 490343216204563948658315)
                    ·
                      rfl

theorem cell22_1432410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_1432410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432410 prefixEnd_1432410 := by exact prefixLift 1432410
  have htrace : WordTrace (prefixWord ++ tailWord_1432410) baseStart_1432410 baseEnd_1432410 := by
    simpa [prefixWord, tailWord_1432410, baseEnd_1432410] using wordTrace_append hprefix tailTrace_1432410
  have hstable : (prefixWord ++ tailWord_1432410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432410).length < 2 ^ (prefixWord ++ tailWord_1432410).sum := by decide
  have hdescent : baseEnd_1432410 < baseStart_1432410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432421 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1432421 : Nat := 118140960795 + 1432421 * 2 ^ 59
def prefixEnd_1432421 : Nat := 4983230072969 + 3 ^ 40 * 1432421 * 2
def baseEnd_1432421 : Nat := 490346981729363586633281

theorem tailTrace_1432421 : CollatzResearch.WordTrace tailWord_1432421 prefixEnd_1432421 490346981729363586633281 := by
  unfold tailWord_1432421
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244685943590829875281117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34829790629060553250187411 52244685943590829875281117)
  ·
    refine ⟨19591757228846561203230419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52244685943590829875281117 19591757228846561203230419)
    ·
      refine ⟨29387635843269841804845629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19591757228846561203230419 29387635843269841804845629)
      ·
        refine ⟨11020363441226190676817111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29387635843269841804845629 11020363441226190676817111)
        ·
          refine ⟨16530545161839286015225667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11020363441226190676817111 16530545161839286015225667)
          ·
            refine ⟨24795817742758929022838501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16530545161839286015225667 24795817742758929022838501)
            ·
              refine ⟨4649215826767299191782219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24795817742758929022838501 4649215826767299191782219)
              ·
                refine ⟨6973823740150948787673329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649215826767299191782219 6973823740150948787673329)
                ·
                  refine ⟨5230367805113211590754997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973823740150948787673329 5230367805113211590754997)
                  ·
                    refine ⟨490346981729363586633281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5230367805113211590754997 490346981729363586633281)
                    ·
                      rfl

theorem cell22_1432421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1432421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432421 prefixEnd_1432421 := by exact prefixLift 1432421
  have htrace : WordTrace (prefixWord ++ tailWord_1432421) baseStart_1432421 baseEnd_1432421 := by
    simpa [prefixWord, tailWord_1432421, baseEnd_1432421] using wordTrace_append hprefix tailTrace_1432421
  have hstable : (prefixWord ++ tailWord_1432421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432421).length < 2 ^ (prefixWord ++ tailWord_1432421).sum := by decide
  have hdescent : baseEnd_1432421 < baseStart_1432421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432453 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1432453 : Nat := 118140960795 + 1432453 * 2 ^ 59
def prefixEnd_1432453 : Nat := 4983230072969 + 3 ^ 40 * 1432453 * 2
def baseEnd_1432453 : Nat := 490357935983326169833183

theorem tailTrace_1432453 : CollatzResearch.WordTrace tailWord_1432453 prefixEnd_1432453 490357935983326169833183 := by
  unfold tailWord_1432453
  simp only [CollatzResearch.WordTrace]
  refine ⟨52245853079474899340446013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34830568719649932893630675 52245853079474899340446013)
  ·
    refine ⟨19592194904803087252667255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52245853079474899340446013 19592194904803087252667255)
    ·
      refine ⟨29388292357204630879000883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19592194904803087252667255 29388292357204630879000883)
      ·
        refine ⟨44082438535806946318501325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29388292357204630879000883 44082438535806946318501325)
        ·
          refine ⟨16530914450927604869437997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44082438535806946318501325 16530914450927604869437997)
          ·
            refine ⟨6199092919097851826039249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16530914450927604869437997 6199092919097851826039249)
            ·
              refine ⟨4649319689323388869529437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6199092919097851826039249 4649319689323388869529437)
              ·
                refine ⟨1743494883496270826073539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4649319689323388869529437 1743494883496270826073539)
                ·
                  refine ⟨2615242325244406239110309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743494883496270826073539 2615242325244406239110309)
                  ·
                    refine ⟨490357935983326169833183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615242325244406239110309 490357935983326169833183)
                    ·
                      rfl

theorem cell22_1432453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1432453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432453 prefixEnd_1432453 := by exact prefixLift 1432453
  have htrace : WordTrace (prefixWord ++ tailWord_1432453) baseStart_1432453 baseEnd_1432453 := by
    simpa [prefixWord, tailWord_1432453, baseEnd_1432453] using wordTrace_append hprefix tailTrace_1432453
  have hstable : (prefixWord ++ tailWord_1432453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432453).length < 2 ^ (prefixWord ++ tailWord_1432453).sum := by decide
  have hdescent : baseEnd_1432453 < baseStart_1432453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432487 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1432487 : Nat := 118140960795 + 1432487 * 2 ^ 59
def prefixEnd_1432487 : Nat := 4983230072969 + 3 ^ 40 * 1432487 * 2
def baseEnd_1432487 : Nat := 490369574878161414483079

theorem tailTrace_1432487 : CollatzResearch.WordTrace tailWord_1432487 prefixEnd_1432487 490369574878161414483079 := by
  unfold tailWord_1432487
  simp only [CollatzResearch.WordTrace]
  refine ⟨52247093161351723147183715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34831395440901148764789143 52247093161351723147183715)
  ·
    refine ⟨78370639742027584720775573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52247093161351723147183715 78370639742027584720775573)
    ·
      refine ⟨3673623737907543033786355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78370639742027584720775573 3673623737907543033786355)
      ·
        refine ⟨5510435606861314550679533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673623737907543033786355 5510435606861314550679533)
        ·
          refine ⟨2066413352572992956504825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5510435606861314550679533 2066413352572992956504825)
          ·
            refine ⟨1549810014429744717378619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066413352572992956504825 1549810014429744717378619)
            ·
              refine ⟨2324715021644617076067929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549810014429744717378619 2324715021644617076067929)
              ·
                refine ⟨1743536266233462807050947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324715021644617076067929 1743536266233462807050947)
                ·
                  refine ⟨2615304399350194210576421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743536266233462807050947 2615304399350194210576421)
                  ·
                    refine ⟨490369574878161414483079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615304399350194210576421 490369574878161414483079)
                    ·
                      rfl

theorem cell22_1432487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1432487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432487 prefixEnd_1432487 := by exact prefixLift 1432487
  have htrace : WordTrace (prefixWord ++ tailWord_1432487) baseStart_1432487 baseEnd_1432487 := by
    simpa [prefixWord, tailWord_1432487, baseEnd_1432487] using wordTrace_append hprefix tailTrace_1432487
  have hstable : (prefixWord ++ tailWord_1432487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432487).length < 2 ^ (prefixWord ++ tailWord_1432487).sum := by decide
  have hdescent : baseEnd_1432487 < baseStart_1432487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432500 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1432500 : Nat := 118140960795 + 1432500 * 2 ^ 59
def prefixEnd_1432500 : Nat := 4983230072969 + 3 ^ 40 * 1432500 * 2
def baseEnd_1432500 : Nat := 490374025043833713908039

theorem tailTrace_1432500 : CollatzResearch.WordTrace tailWord_1432500 prefixEnd_1432500 490374025043833713908039 := by
  unfold tailWord_1432500
  simp only [CollatzResearch.WordTrace]
  refine ⟨26123783655152313183703477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34831711540203084244937969 26123783655152313183703477)
  ·
    refine ⟨2449104717670529360972201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26123783655152313183703477 2449104717670529360972201)
    ·
      refine ⟨1836828538252897020729151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2449104717670529360972201 1836828538252897020729151)
      ·
        refine ⟨2755242807379345531093727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836828538252897020729151 2755242807379345531093727)
        ·
          refine ⟨4132864211069018296640591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755242807379345531093727 4132864211069018296640591)
          ·
            refine ⟨6199296316603527444960887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132864211069018296640591 6199296316603527444960887)
            ·
              refine ⟨9298944474905291167441331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199296316603527444960887 9298944474905291167441331)
              ·
                refine ⟨13948416712357936751161997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298944474905291167441331 13948416712357936751161997)
                ·
                  refine ⟨5230656267134226281685749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13948416712357936751161997 5230656267134226281685749)
                  ·
                    refine ⟨490374025043833713908039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5230656267134226281685749 490374025043833713908039)
                    ·
                      rfl

theorem cell22_1432500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1432500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432500 prefixEnd_1432500 := by exact prefixLift 1432500
  have htrace : WordTrace (prefixWord ++ tailWord_1432500) baseStart_1432500 baseEnd_1432500 := by
    simpa [prefixWord, tailWord_1432500, baseEnd_1432500] using wordTrace_append hprefix tailTrace_1432500
  have hstable : (prefixWord ++ tailWord_1432500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432500).length < 2 ^ (prefixWord ++ tailWord_1432500).sum := by decide
  have hdescent : baseEnd_1432500 < baseStart_1432500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432528 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_1432528 : Nat := 118140960795 + 1432528 * 2 ^ 59
def prefixEnd_1432528 : Nat := 4983230072969 + 3 ^ 40 * 1432528 * 2
def baseEnd_1432528 : Nat := 490383610016050974207953

theorem tailTrace_1432528 : CollatzResearch.WordTrace tailWord_1432528 prefixEnd_1432528 490383610016050974207953 := by
  unfold tailWord_1432528
  simp only [CollatzResearch.WordTrace]
  refine ⟨26124294277101593574713119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34832392369468791432950825 26124294277101593574713119)
  ·
    refine ⟨39186441415652390362069679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26124294277101593574713119 39186441415652390362069679)
    ·
      refine ⟨58779662123478585543104519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39186441415652390362069679 58779662123478585543104519)
      ·
        refine ⟨88169493185217878314656779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58779662123478585543104519 88169493185217878314656779)
        ·
          refine ⟨132254239777826817471985169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88169493185217878314656779 132254239777826817471985169)
          ·
            refine ⟨99190679833370113103988877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132254239777826817471985169 99190679833370113103988877)
            ·
              refine ⟨37196504937513792413995829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99190679833370113103988877 37196504937513792413995829)
              ·
                refine ⟨3487172337891918038812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37196504937513792413995829 3487172337891918038812109)
                ·
                  refine ⟨1307689626709469264554541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3487172337891918038812109 1307689626709469264554541)
                  ·
                    refine ⟨490383610016050974207953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307689626709469264554541 490383610016050974207953)
                    ·
                      rfl

theorem cell22_1432528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_1432528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432528 prefixEnd_1432528 := by exact prefixLift 1432528
  have htrace : WordTrace (prefixWord ++ tailWord_1432528) baseStart_1432528 baseEnd_1432528 := by
    simpa [prefixWord, tailWord_1432528, baseEnd_1432528] using wordTrace_append hprefix tailTrace_1432528
  have hstable : (prefixWord ++ tailWord_1432528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432528).length < 2 ^ (prefixWord ++ tailWord_1432528).sum := by decide
  have hdescent : baseEnd_1432528 < baseStart_1432528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432530 : List Nat := [3, 2, 2, 3, 1, 3, 1, 7]
def baseStart_1432530 : Nat := 118140960795 + 1432530 * 2 ^ 59
def prefixEnd_1432530 : Nat := 4983230072969 + 3 ^ 40 * 1432530 * 2
def baseEnd_1432530 : Nat := 54487143850769292850883

theorem tailTrace_1432530 : CollatzResearch.WordTrace tailWord_1432530 prefixEnd_1432530 54487143850769292850883 := by
  unfold tailWord_1432530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062165375048985372749761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34832441000130627660666029 13062165375048985372749761)
  ·
    refine ⟨9796624031286739029562321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13062165375048985372749761 9796624031286739029562321)
    ·
      refine ⟨7347468023465054272171741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796624031286739029562321 7347468023465054272171741)
      ·
        refine ⟨2755300508799395352064403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7347468023465054272171741 2755300508799395352064403)
        ·
          refine ⟨4132950763199093028096605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755300508799395352064403 4132950763199093028096605)
          ·
            refine ⟨1549856536199659885536227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4132950763199093028096605 1549856536199659885536227)
            ·
              refine ⟨2324784804299489828304341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549856536199659885536227 2324784804299489828304341)
              ·
                refine ⟨54487143850769292850883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2324784804299489828304341 54487143850769292850883)
                ·
                  rfl

theorem cell22_1432530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_1432530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432530 prefixEnd_1432530 := by exact prefixLift 1432530
  have htrace : WordTrace (prefixWord ++ tailWord_1432530) baseStart_1432530 baseEnd_1432530 := by
    simpa [prefixWord, tailWord_1432530, baseEnd_1432530] using wordTrace_append hprefix tailTrace_1432530
  have hstable : (prefixWord ++ tailWord_1432530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432530).length < 2 ^ (prefixWord ++ tailWord_1432530).sum := by decide
  have hdescent : baseEnd_1432530 < baseStart_1432530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432549 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_1432549 : Nat := 118140960795 + 1432549 * 2 ^ 59
def prefixEnd_1432549 : Nat := 4983230072969 + 3 ^ 40 * 1432549 * 2
def baseEnd_1432549 : Nat := 490390798745213919432889

theorem tailTrace_1432549 : CollatzResearch.WordTrace tailWord_1432549 prefixEnd_1432549 490390798745213919432889 := by
  unfold tailWord_1432549
  simp only [CollatzResearch.WordTrace]
  refine ⟨52249354487127107735940701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34832902991418071823960467 52249354487127107735940701)
  ·
    refine ⟨19593507932672665400977763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52249354487127107735940701 19593507932672665400977763)
    ·
      refine ⟨29390261899008998101466645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19593507932672665400977763 29390261899008998101466645)
      ·
        refine ⟨1377668526516046786006249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29390261899008998101466645 1377668526516046786006249)
        ·
          refine ⟨1033251394887035089504687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377668526516046786006249 1033251394887035089504687)
          ·
            refine ⟨1549877092330552634257031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033251394887035089504687 1549877092330552634257031)
            ·
              refine ⟨2324815638495828951385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549877092330552634257031 2324815638495828951385547)
              ·
                refine ⟨3487223457743743427078321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324815638495828951385547 3487223457743743427078321)
                ·
                  refine ⟨2615417593307807570308741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487223457743743427078321 2615417593307807570308741)
                  ·
                    refine ⟨490390798745213919432889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615417593307807570308741 490390798745213919432889)
                    ·
                      rfl

theorem cell22_1432549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_1432549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432549 prefixEnd_1432549 := by exact prefixLift 1432549
  have htrace : WordTrace (prefixWord ++ tailWord_1432549) baseStart_1432549 baseEnd_1432549 := by
    simpa [prefixWord, tailWord_1432549, baseEnd_1432549] using wordTrace_append hprefix tailTrace_1432549
  have hstable : (prefixWord ++ tailWord_1432549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432549).length < 2 ^ (prefixWord ++ tailWord_1432549).sum := by decide
  have hdescent : baseEnd_1432549 < baseStart_1432549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432564 : List Nat := [2, 6, 2, 1, 1, 1, 9]
def baseStart_1432564 : Nat := 118140960795 + 1432564 * 2 ^ 59
def prefixEnd_1432564 : Nat := 4983230072969 + 3 ^ 40 * 1432564 * 2
def baseEnd_1432564 : Nat := 18162812353768847418809

theorem tailTrace_1432564 : CollatzResearch.WordTrace tailWord_1432564 prefixEnd_1432564 18162812353768847418809 := by
  unfold tailWord_1432564
  simp only [CollatzResearch.WordTrace]
  refine ⟨26124950791036382648868373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34833267721381843531824497 26124950791036382648868373)
  ·
    refine ⟨1224607068329830436665705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26124950791036382648868373 1224607068329830436665705)
    ·
      refine ⟨918455301247372827499279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224607068329830436665705 918455301247372827499279)
      ·
        refine ⟨1377682951871059241248919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918455301247372827499279 1377682951871059241248919)
        ·
          refine ⟨2066524427806588861873379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377682951871059241248919 2066524427806588861873379)
          ·
            refine ⟨3099786641709883292810069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066524427806588861873379 3099786641709883292810069)
            ·
              refine ⟨18162812353768847418809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3099786641709883292810069 18162812353768847418809)
              ·
                rfl

theorem cell22_1432564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 9].length) (baseStart_1432564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432564 prefixEnd_1432564 := by exact prefixLift 1432564
  have htrace : WordTrace (prefixWord ++ tailWord_1432564) baseStart_1432564 baseEnd_1432564 := by
    simpa [prefixWord, tailWord_1432564, baseEnd_1432564] using wordTrace_append hprefix tailTrace_1432564
  have hstable : (prefixWord ++ tailWord_1432564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432564).length < 2 ^ (prefixWord ++ tailWord_1432564).sum := by decide
  have hdescent : baseEnd_1432564 < baseStart_1432564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432648 : List Nat := [2, 1, 3, 1, 1, 1, 6, 7]
def baseStart_1432648 : Nat := 118140960795 + 1432648 * 2 ^ 59
def prefixEnd_1432648 : Nat := 4983230072969 + 3 ^ 40 * 1432648 * 2
def baseEnd_1432648 : Nat := 54491632052045629023065

theorem tailTrace_1432648 : CollatzResearch.WordTrace tailWord_1432648 prefixEnd_1432648 54491632052045629023065 := by
  unfold tailWord_1432648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26126482656884223821897299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34835310209178965095863065 26126482656884223821897299)
  ·
    refine ⟨39189723985326335732845949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26126482656884223821897299 39189723985326335732845949)
    ·
      refine ⟨14696146494497375899817231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39189723985326335732845949 14696146494497375899817231)
      ·
        refine ⟨22044219741746063849725847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14696146494497375899817231 22044219741746063849725847)
        ·
          refine ⟨33066329612619095774588771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22044219741746063849725847 33066329612619095774588771)
          ·
            refine ⟨49599494418928643661883157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33066329612619095774588771 49599494418928643661883157)
            ·
              refine ⟨2324976300887280171650773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49599494418928643661883157 2324976300887280171650773)
              ·
                refine ⟨54491632052045629023065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2324976300887280171650773 54491632052045629023065)
                ·
                  rfl

theorem cell22_1432648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_1432648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432648 prefixEnd_1432648 := by exact prefixLift 1432648
  have htrace : WordTrace (prefixWord ++ tailWord_1432648) baseStart_1432648 baseEnd_1432648 := by
    simpa [prefixWord, tailWord_1432648, baseEnd_1432648] using wordTrace_append hprefix tailTrace_1432648
  have hstable : (prefixWord ++ tailWord_1432648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432648).length < 2 ^ (prefixWord ++ tailWord_1432648).sum := by decide
  have hdescent : baseEnd_1432648 < baseStart_1432648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432785 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_1432785 : Nat := 118140960795 + 1432785 * 2 ^ 59
def prefixEnd_1432785 : Nat := 4983230072969 + 3 ^ 40 * 1432785 * 2
def baseEnd_1432785 : Nat := 490471586368187970532165

theorem tailTrace_1432785 : CollatzResearch.WordTrace tailWord_1432785 prefixEnd_1432785 490471586368187970532165 := by
  unfold tailWord_1432785
  simp only [CollatzResearch.WordTrace]
  refine ⟨52257962114272120041531809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34838641409514746694354539 52257962114272120041531809)
  ·
    refine ⟨39193471585704090031148857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52257962114272120041531809 39193471585704090031148857)
    ·
      refine ⟨29395103689278067523361643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39193471585704090031148857 29395103689278067523361643)
      ·
        refine ⟨44092655533917101285042465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29395103689278067523361643 44092655533917101285042465)
        ·
          refine ⟨33069491650437825963781849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44092655533917101285042465 33069491650437825963781849)
          ·
            refine ⟨24802118737828369472836387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33069491650437825963781849 24802118737828369472836387)
            ·
              refine ⟨37203178106742554209254581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24802118737828369472836387 37203178106742554209254581)
              ·
                refine ⟨3487797947507114457117617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37203178106742554209254581 3487797947507114457117617)
                ·
                  refine ⟨2615848460630335842838213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487797947507114457117617 2615848460630335842838213)
                  ·
                    refine ⟨490471586368187970532165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615848460630335842838213 490471586368187970532165)
                    ·
                      rfl

theorem cell22_1432785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_1432785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432785 prefixEnd_1432785 := by exact prefixLift 1432785
  have htrace : WordTrace (prefixWord ++ tailWord_1432785) baseStart_1432785 baseEnd_1432785 := by
    simpa [prefixWord, tailWord_1432785, baseEnd_1432785] using wordTrace_append hprefix tailTrace_1432785
  have hstable : (prefixWord ++ tailWord_1432785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432785).length < 2 ^ (prefixWord ++ tailWord_1432785).sum := by decide
  have hdescent : baseEnd_1432785 < baseStart_1432785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432789 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 4]
def baseStart_1432789 : Nat := 118140960795 + 1432789 * 2 ^ 59
def prefixEnd_1432789 : Nat := 4983230072969 + 3 ^ 40 * 1432789 * 2
def baseEnd_1432789 : Nat := 163490985216644431144051

theorem tailTrace_1432789 : CollatzResearch.WordTrace tailWord_1432789 prefixEnd_1432789 163490985216644431144051 := by
  unfold tailWord_1432789
  simp only [CollatzResearch.WordTrace]
  refine ⟨52258108006257628724677421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34838738670838419149784947 52258108006257628724677421)
  ·
    refine ⟨19596790502346610771754033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52258108006257628724677421 19596790502346610771754033)
    ·
      refine ⟨14697592876759958078815525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19596790502346610771754033 14697592876759958078815525)
      ·
        refine ⟨2755798664392492139777911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14697592876759958078815525 2755798664392492139777911)
        ·
          refine ⟨4133697996588738209666867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755798664392492139777911 4133697996588738209666867)
          ·
            refine ⟨6200546994883107314500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133697996588738209666867 6200546994883107314500301)
            ·
              refine ⟨2325205123081165242937613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6200546994883107314500301 2325205123081165242937613)
              ·
                refine ⟨871951921155436966101605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2325205123081165242937613 871951921155436966101605)
                ·
                  refine ⟨163490985216644431144051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871951921155436966101605 163490985216644431144051)
                  ·
                    rfl

theorem cell22_1432789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_1432789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432789 prefixEnd_1432789 := by exact prefixLift 1432789
  have htrace : WordTrace (prefixWord ++ tailWord_1432789) baseStart_1432789 baseEnd_1432789 := by
    simpa [prefixWord, tailWord_1432789, baseEnd_1432789] using wordTrace_append hprefix tailTrace_1432789
  have hstable : (prefixWord ++ tailWord_1432789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432789).length < 2 ^ (prefixWord ++ tailWord_1432789).sum := by decide
  have hdescent : baseEnd_1432789 < baseStart_1432789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432800 : List Nat := [2, 1, 1, 3, 1, 6, 8]
def baseStart_1432800 : Nat := 118140960795 + 1432800 * 2 ^ 59
def prefixEnd_1432800 : Nat := 4983230072969 + 3 ^ 40 * 1432800 * 2
def baseEnd_1432800 : Nat := 18165804487953071533597

theorem tailTrace_1432800 : CollatzResearch.WordTrace tailWord_1432800 prefixEnd_1432800 18165804487953071533597 := by
  unfold tailWord_1432800
  simp only [CollatzResearch.WordTrace]
  refine ⟨26129254604608888801663927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34839006139478518402218569 26129254604608888801663927)
  ·
    refine ⟨39193881906913333202495891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26129254604608888801663927 39193881906913333202495891)
    ·
      refine ⟨58790822860369999803743837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39193881906913333202495891 58790822860369999803743837)
      ·
        refine ⟨22046558572638749926403939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58790822860369999803743837 22046558572638749926403939)
        ·
          refine ⟨33069837858958124889605909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22046558572638749926403939 33069837858958124889605909)
          ·
            refine ⟨1550148649638662104200277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33069837858958124889605909 1550148649638662104200277)
            ·
              refine ⟨18165804487953071533597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1550148649638662104200277 18165804487953071533597)
              ·
                rfl

theorem cell22_1432800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 8].length) (baseStart_1432800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432800 prefixEnd_1432800 := by exact prefixLift 1432800
  have htrace : WordTrace (prefixWord ++ tailWord_1432800) baseStart_1432800 baseEnd_1432800 := by
    simpa [prefixWord, tailWord_1432800, baseEnd_1432800] using wordTrace_append hprefix tailTrace_1432800
  have hstable : (prefixWord ++ tailWord_1432800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432800).length < 2 ^ (prefixWord ++ tailWord_1432800).sum := by decide
  have hdescent : baseEnd_1432800 < baseStart_1432800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432849 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 1, 3]
def baseStart_1432849 : Nat := 118140960795 + 1432849 * 2 ^ 59
def prefixEnd_1432849 : Nat := 4983230072969 + 3 ^ 40 * 1432849 * 2
def baseEnd_1432849 : Nat := 490493494876113136931969

theorem tailTrace_1432849 : CollatzResearch.WordTrace tailWord_1432849 prefixEnd_1432849 490493494876113136931969 := by
  unfold tailWord_1432849
  simp only [CollatzResearch.WordTrace]
  refine ⟨52260296386040258971861601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34840197590693505981241067 52260296386040258971861601)
  ·
    refine ⟨39195222289530194228896201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52260296386040258971861601 39195222289530194228896201)
    ·
      refine ⟨29396416717147645671672151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39195222289530194228896201 29396416717147645671672151)
      ·
        refine ⟨44094625075721468507508227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29396416717147645671672151 44094625075721468507508227)
        ·
          refine ⟨66141937613582202761262341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44094625075721468507508227 66141937613582202761262341)
          ·
            refine ⟨12401613302546663017736689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66141937613582202761262341 12401613302546663017736689)
            ·
              refine ⟨9301209976909997263302517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12401613302546663017736689 9301209976909997263302517)
              ·
                refine ⟨871988435335312243434611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9301209976909997263302517 871988435335312243434611)
                ·
                  refine ⟨1307982653002968365151917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871988435335312243434611 1307982653002968365151917)
                  ·
                    refine ⟨490493494876113136931969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307982653002968365151917 490493494876113136931969)
                    ·
                      rfl

theorem cell22_1432849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_1432849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432849 prefixEnd_1432849 := by exact prefixLift 1432849
  have htrace : WordTrace (prefixWord ++ tailWord_1432849) baseStart_1432849 baseEnd_1432849 := by
    simpa [prefixWord, tailWord_1432849, baseEnd_1432849] using wordTrace_append hprefix tailTrace_1432849
  have hstable : (prefixWord ++ tailWord_1432849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432849).length < 2 ^ (prefixWord ++ tailWord_1432849).sum := by decide
  have hdescent : baseEnd_1432849 < baseStart_1432849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432892 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1432892 : Nat := 118140960795 + 1432892 * 2 ^ 59
def prefixEnd_1432892 : Nat := 4983230072969 + 3 ^ 40 * 1432892 * 2
def baseEnd_1432892 : Nat := 490508214654875358106837

theorem tailTrace_1432892 : CollatzResearch.WordTrace tailWord_1432892 prefixEnd_1432892 490508214654875358106837 := by
  unfold tailWord_1432892
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130932362442238657838465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34841243149922984877117953 26130932362442238657838465)
  ·
    refine ⟨19598199271831678993378849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26130932362442238657838465 19598199271831678993378849)
    ·
      refine ⟨14698649453873759245034137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19598199271831678993378849 14698649453873759245034137)
      ·
        refine ⟨11023987090405319433775603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14698649453873759245034137 11023987090405319433775603)
        ·
          refine ⟨16535980635607979150663405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023987090405319433775603 16535980635607979150663405)
          ·
            refine ⟨6200992738352992181498777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16535980635607979150663405 6200992738352992181498777)
            ·
              refine ⟨4650744553764744136124083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200992738352992181498777 4650744553764744136124083)
              ·
                refine ⟨6976116830647116204186125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650744553764744136124083 6976116830647116204186125)
                ·
                  refine ⟨2616043811492668576569797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6976116830647116204186125 2616043811492668576569797)
                  ·
                    refine ⟨490508214654875358106837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2616043811492668576569797 490508214654875358106837)
                    ·
                      rfl

theorem cell22_1432892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1432892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432892 prefixEnd_1432892 := by exact prefixLift 1432892
  have htrace : WordTrace (prefixWord ++ tailWord_1432892) baseStart_1432892 baseEnd_1432892 := by
    simpa [prefixWord, tailWord_1432892, baseEnd_1432892] using wordTrace_append hprefix tailTrace_1432892
  have hstable : (prefixWord ++ tailWord_1432892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432892).length < 2 ^ (prefixWord ++ tailWord_1432892).sum := by decide
  have hdescent : baseEnd_1432892 < baseStart_1432892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432969 : List Nat := [1, 2, 1, 1, 8, 1, 8]
def baseStart_1432969 : Nat := 118140960795 + 1432969 * 2 ^ 59
def prefixEnd_1432969 : Nat := 4983230072969 + 3 ^ 40 * 1432969 * 2
def baseEnd_1432969 : Nat := 18167947160313808293763

theorem tailTrace_1432969 : CollatzResearch.WordTrace tailWord_1432969 prefixEnd_1432969 18167947160313808293763 := by
  unfold tailWord_1432969
  simp only [CollatzResearch.WordTrace]
  refine ⟨52264673145605519466229961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34843115430403679644153307 52264673145605519466229961)
  ·
    refine ⟨39198504859204139599672471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52264673145605519466229961 39198504859204139599672471)
    ·
      refine ⟨58797757288806209399508707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39198504859204139599672471 58797757288806209399508707)
      ·
        refine ⟨88196635933209314099263061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58797757288806209399508707 88196635933209314099263061)
        ·
          refine ⟨1033554327342296649600739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 88196635933209314099263061 1033554327342296649600739)
          ·
            refine ⟨1550331491013444974401109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033554327342296649600739 1550331491013444974401109)
            ·
              refine ⟨18167947160313808293763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1550331491013444974401109 18167947160313808293763)
              ·
                rfl

theorem cell22_1432969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 8].length) (baseStart_1432969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1432969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1432969 prefixEnd_1432969 := by exact prefixLift 1432969
  have htrace : WordTrace (prefixWord ++ tailWord_1432969) baseStart_1432969 baseEnd_1432969 := by
    simpa [prefixWord, tailWord_1432969, baseEnd_1432969] using wordTrace_append hprefix tailTrace_1432969
  have hstable : (prefixWord ++ tailWord_1432969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432969).length < 2 ^ (prefixWord ++ tailWord_1432969).sum := by decide
  have hdescent : baseEnd_1432969 < baseStart_1432969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433026 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1433026 : Nat := 118140960795 + 1433026 * 2 ^ 59
def prefixEnd_1433026 : Nat := 4983230072969 + 3 ^ 40 * 1433026 * 2
def baseEnd_1433026 : Nat := 163518028531114558418809

theorem tailTrace_1433026 : CollatzResearch.WordTrace tailWord_1433026 prefixEnd_1433026 163518028531114558418809 := by
  unfold tailWord_1433026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066688026599754550263733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34844501404266012134036621 13066688026599754550263733)
  ·
    refine ⟨1225002002493726989087225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13066688026599754550263733 1225002002493726989087225)
    ·
      refine ⟨918751501870295241815419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1225002002493726989087225 918751501870295241815419)
      ·
        refine ⟨1378127252805442862723129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918751501870295241815419 1378127252805442862723129)
        ·
          refine ⟨1033595439604082147042347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378127252805442862723129 1033595439604082147042347)
          ·
            refine ⟨1550393159406123220563521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033595439604082147042347 1550393159406123220563521)
            ·
              refine ⟨1162794869554592415422641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550393159406123220563521 1162794869554592415422641)
              ·
                refine ⟨872096152165944311566981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162794869554592415422641 872096152165944311566981)
                ·
                  refine ⟨163518028531114558418809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872096152165944311566981 163518028531114558418809)
                  ·
                    rfl

theorem cell22_1433026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1433026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433026 prefixEnd_1433026 := by exact prefixLift 1433026
  have htrace : WordTrace (prefixWord ++ tailWord_1433026) baseStart_1433026 baseEnd_1433026 := by
    simpa [prefixWord, tailWord_1433026, baseEnd_1433026] using wordTrace_append hprefix tailTrace_1433026
  have hstable : (prefixWord ++ tailWord_1433026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433026).length < 2 ^ (prefixWord ++ tailWord_1433026).sum := by decide
  have hdescent : baseEnd_1433026 < baseStart_1433026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433046 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1433046 : Nat := 118140960795 + 1433046 * 2 ^ 59
def prefixEnd_1433046 : Nat := 4983230072969 + 3 ^ 40 * 1433046 * 2
def baseEnd_1433046 : Nat := 490560932002070289756365

theorem tailTrace_1433046 : CollatzResearch.WordTrace tailWord_1433046 prefixEnd_1433046 490560932002070289756365 := by
  unfold tailWord_1433046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266717597895410101048937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34844987710884374411188661 3266717597895410101048937)
  ·
    refine ⟨2450038198421557575786703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3266717597895410101048937 2450038198421557575786703)
    ·
      refine ⟨3675057297632336363680055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450038198421557575786703 3675057297632336363680055)
      ·
        refine ⟨5512585946448504545520083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3675057297632336363680055 5512585946448504545520083)
        ·
          refine ⟨8268878919672756818280125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512585946448504545520083 8268878919672756818280125)
          ·
            refine ⟨3100829594877283806855047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8268878919672756818280125 3100829594877283806855047)
            ·
              refine ⟨4651244392315925710282571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100829594877283806855047 4651244392315925710282571)
              ·
                refine ⟨6976866588473888565423857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651244392315925710282571 6976866588473888565423857)
                ·
                  refine ⟨5232649941355416424067893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6976866588473888565423857 5232649941355416424067893)
                  ·
                    refine ⟨490560932002070289756365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5232649941355416424067893 490560932002070289756365)
                    ·
                      rfl

theorem cell22_1433046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1433046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433046 prefixEnd_1433046 := by exact prefixLift 1433046
  have htrace : WordTrace (prefixWord ++ tailWord_1433046) baseStart_1433046 baseEnd_1433046 := by
    simpa [prefixWord, tailWord_1433046, baseEnd_1433046] using wordTrace_append hprefix tailTrace_1433046
  have hstable : (prefixWord ++ tailWord_1433046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433046).length < 2 ^ (prefixWord ++ tailWord_1433046).sum := by decide
  have hdescent : baseEnd_1433046 < baseStart_1433046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433059 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 6]
def baseStart_1433059 : Nat := 118140960795 + 1433059 * 2 ^ 59
def prefixEnd_1433059 : Nat := 4983230072969 + 3 ^ 40 * 1433059 * 2
def baseEnd_1433059 : Nat := 163521794055914196393775

theorem tailTrace_1433059 : CollatzResearch.WordTrace tailWord_1433059 prefixEnd_1433059 163521794055914196393775 := by
  unfold tailWord_1433059
  simp only [CollatzResearch.WordTrace]
  refine ⟨52267955715279464837006231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34845303810186309891337487 52267955715279464837006231)
  ·
    refine ⟨78401933572919197255509347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52267955715279464837006231 78401933572919197255509347)
    ·
      refine ⟨117602900359378795883264021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78401933572919197255509347 117602900359378795883264021)
      ·
        refine ⟨5512635954345881057028001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117602900359378795883264021 5512635954345881057028001)
        ·
          refine ⟨4134476965759410792771001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5512635954345881057028001 4134476965759410792771001)
          ·
            refine ⟨3100857724319558094578251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4134476965759410792771001 3100857724319558094578251)
            ·
              refine ⟨4651286586479337141867377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100857724319558094578251 4651286586479337141867377)
              ·
                refine ⟨3488464939859502856400533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4651286586479337141867377 3488464939859502856400533)
                ·
                  refine ⟨163521794055914196393775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3488464939859502856400533 163521794055914196393775)
                  ·
                    rfl

theorem cell22_1433059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_1433059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433059 prefixEnd_1433059 := by exact prefixLift 1433059
  have htrace : WordTrace (prefixWord ++ tailWord_1433059) baseStart_1433059 baseEnd_1433059 := by
    simpa [prefixWord, tailWord_1433059, baseEnd_1433059] using wordTrace_append hprefix tailTrace_1433059
  have hstable : (prefixWord ++ tailWord_1433059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433059).length < 2 ^ (prefixWord ++ tailWord_1433059).sum := by decide
  have hdescent : baseEnd_1433059 < baseStart_1433059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433078 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1433078 : Nat := 118140960795 + 1433078 * 2 ^ 59
def prefixEnd_1433078 : Nat := 4983230072969 + 3 ^ 40 * 1433078 * 2
def baseEnd_1433078 : Nat := 490571886256032872956267

theorem tailTrace_1433078 : CollatzResearch.WordTrace tailWord_1433078 prefixEnd_1433078 490571886256032872956267 := by
  unfold tailWord_1433078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266790543888164442621743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34845765801473754054631925 3266790543888164442621743)
  ·
    refine ⟨4900185815832246663932615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266790543888164442621743 4900185815832246663932615)
    ·
      refine ⟨7350278723748369995898923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900185815832246663932615 7350278723748369995898923)
      ·
        refine ⟨11025418085622554993848385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350278723748369995898923 11025418085622554993848385)
        ·
          refine ⟨8269063564216916245386289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11025418085622554993848385 8269063564216916245386289)
          ·
            refine ⟨6201797673162687184039717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8269063564216916245386289 6201797673162687184039717)
            ·
              refine ⟨1162837063718003847007447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6201797673162687184039717 1162837063718003847007447)
              ·
                refine ⟨1744255595577005770511171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162837063718003847007447 1744255595577005770511171)
                ·
                  refine ⟨2616383393365508655766757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744255595577005770511171 2616383393365508655766757)
                  ·
                    refine ⟨490571886256032872956267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2616383393365508655766757 490571886256032872956267)
                    ·
                      rfl

theorem cell22_1433078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1433078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433078 prefixEnd_1433078 := by exact prefixLift 1433078
  have htrace : WordTrace (prefixWord ++ tailWord_1433078) baseStart_1433078 baseEnd_1433078 := by
    simpa [prefixWord, tailWord_1433078, baseEnd_1433078] using wordTrace_append hprefix tailTrace_1433078
  have hstable : (prefixWord ++ tailWord_1433078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433078).length < 2 ^ (prefixWord ++ tailWord_1433078).sum := by decide
  have hdescent : baseEnd_1433078 < baseStart_1433078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433121 : List Nat := [1, 2, 3, 2, 2, 4, 2, 6]
def baseStart_1433121 : Nat := 118140960795 + 1433121 * 2 ^ 59
def prefixEnd_1433121 : Nat := 4983230072969 + 3 ^ 40 * 1433121 * 2
def baseEnd_1433121 : Nat := 54509622892755010459015

theorem tailTrace_1433121 : CollatzResearch.WordTrace tailWord_1433121 prefixEnd_1433121 54509622892755010459015 := by
  unfold tailWord_1433121
  simp only [CollatzResearch.WordTrace]
  refine ⟨52270217041054849425763217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34846811360703232950508811 52270217041054849425763217)
  ·
    refine ⟨39202662780791137069322413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52270217041054849425763217 39202662780791137069322413)
    ·
      refine ⟨14700998542796676400995905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39202662780791137069322413 14700998542796676400995905)
      ·
        refine ⟨11025748907097507300746929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14700998542796676400995905 11025748907097507300746929)
        ·
          refine ⟨8269311680323130475560197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11025748907097507300746929 8269311680323130475560197)
          ·
            refine ⟨1550495940060586964167537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8269311680323130475560197 1550495940060586964167537)
            ·
              refine ⟨1162871955045440223125653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550495940060586964167537 1162871955045440223125653)
              ·
                refine ⟨54509622892755010459015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1162871955045440223125653 54509622892755010459015)
                ·
                  rfl

theorem cell22_1433121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 6].length) (baseStart_1433121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433121 prefixEnd_1433121 := by exact prefixLift 1433121
  have htrace : WordTrace (prefixWord ++ tailWord_1433121) baseStart_1433121 baseEnd_1433121 := by
    simpa [prefixWord, tailWord_1433121, baseEnd_1433121] using wordTrace_append hprefix tailTrace_1433121
  have hstable : (prefixWord ++ tailWord_1433121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433121).length < 2 ^ (prefixWord ++ tailWord_1433121).sum := by decide
  have hdescent : baseEnd_1433121 < baseStart_1433121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433209 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_1433209 : Nat := 118140960795 + 1433209 * 2 ^ 59
def prefixEnd_1433209 : Nat := 4983230072969 + 3 ^ 40 * 1433209 * 2
def baseEnd_1433209 : Nat := 490616730233192197930865

theorem tailTrace_1433209 : CollatzResearch.WordTrace tailWord_1433209 prefixEnd_1433209 490616730233192197930865 := by
  unfold tailWord_1433209
  simp only [CollatzResearch.WordTrace]
  refine ⟨52273426664736040454966681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34848951109824026969977787 52273426664736040454966681)
  ·
    refine ⟨39205069998552030341225011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52273426664736040454966681 39205069998552030341225011)
    ·
      refine ⟨58807604997828045511837517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39205069998552030341225011 58807604997828045511837517)
      ·
        refine ⟨22052851874185517066939069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58807604997828045511837517 22052851874185517066939069)
        ·
          refine ⟨8269819452819568900102151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22052851874185517066939069 8269819452819568900102151)
          ·
            refine ⟨12404729179229353350153227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269819452819568900102151 12404729179229353350153227)
            ·
              refine ⟨18607093768844030025229841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404729179229353350153227 18607093768844030025229841)
              ·
                refine ⟨13955320326633022518922381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18607093768844030025229841 13955320326633022518922381)
                ·
                  refine ⟨5233245122487383444595893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13955320326633022518922381 5233245122487383444595893)
                  ·
                    refine ⟨490616730233192197930865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5233245122487383444595893 490616730233192197930865)
                    ·
                      rfl

theorem cell22_1433209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_1433209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433209 prefixEnd_1433209 := by exact prefixLift 1433209
  have htrace : WordTrace (prefixWord ++ tailWord_1433209) baseStart_1433209 baseEnd_1433209 := by
    simpa [prefixWord, tailWord_1433209, baseEnd_1433209] using wordTrace_append hprefix tailTrace_1433209
  have hstable : (prefixWord ++ tailWord_1433209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433209).length < 2 ^ (prefixWord ++ tailWord_1433209).sum := by decide
  have hdescent : baseEnd_1433209 < baseStart_1433209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433211 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 4]
def baseStart_1433211 : Nat := 118140960795 + 1433211 * 2 ^ 59
def prefixEnd_1433211 : Nat := 4983230072969 + 3 ^ 40 * 1433211 * 2
def baseEnd_1433211 : Nat := 163539138291354953126953

theorem tailTrace_1433211 : CollatzResearch.WordTrace tailWord_1433211 prefixEnd_1433211 163539138291354953126953 := by
  unfold tailWord_1433211
  simp only [CollatzResearch.WordTrace]
  refine ⟨52273499610728794796539487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34848999740485863197692991 52273499610728794796539487)
  ·
    refine ⟨78410249416093192194809231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52273499610728794796539487 78410249416093192194809231)
    ·
      refine ⟨117615374124139788292213847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78410249416093192194809231 117615374124139788292213847)
      ·
        refine ⟨176423061186209682438320771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117615374124139788292213847 176423061186209682438320771)
        ·
          refine ⟨264634591779314523657481157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176423061186209682438320771 264634591779314523657481157)
          ·
            refine ⟨49618985958621473185777717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264634591779314523657481157 49618985958621473185777717)
            ·
              refine ⟨4651779933620763111166661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49618985958621473185777717 4651779933620763111166661)
              ·
                refine ⟨872208737553893083343749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4651779933620763111166661 872208737553893083343749)
                ·
                  refine ⟨163539138291354953126953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872208737553893083343749 163539138291354953126953)
                  ·
                    rfl

theorem cell22_1433211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 4].length) (baseStart_1433211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433211 prefixEnd_1433211 := by exact prefixLift 1433211
  have htrace : WordTrace (prefixWord ++ tailWord_1433211) baseStart_1433211 baseEnd_1433211 := by
    simpa [prefixWord, tailWord_1433211, baseEnd_1433211] using wordTrace_append hprefix tailTrace_1433211
  have hstable : (prefixWord ++ tailWord_1433211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433211).length < 2 ^ (prefixWord ++ tailWord_1433211).sum := by decide
  have hdescent : baseEnd_1433211 < baseStart_1433211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433226 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1433226 : Nat := 118140960795 + 1433226 * 2 ^ 59
def prefixEnd_1433226 : Nat := 4983230072969 + 3 ^ 40 * 1433226 * 2
def baseEnd_1433226 : Nat := 490622549680609820255813

theorem tailTrace_1433226 : CollatzResearch.WordTrace tailWord_1433226 prefixEnd_1433226 490622549680609820255813 := by
  unfold tailWord_1433226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13068511676418613089583883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34849364470449634905557021 13068511676418613089583883)
  ·
    refine ⟨19602767514627919634375825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13068511676418613089583883 19602767514627919634375825)
    ·
      refine ⟨14702075635970939725781869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19602767514627919634375825 14702075635970939725781869)
      ·
        refine ⟨5513278363489102397168201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14702075635970939725781869 5513278363489102397168201)
        ·
          refine ⟨4134958772616826797876151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5513278363489102397168201 4134958772616826797876151)
          ·
            refine ⟨6202438158925240196814227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134958772616826797876151 6202438158925240196814227)
            ·
              refine ⟨9303657238387860295221341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202438158925240196814227 9303657238387860295221341)
              ·
                refine ⟨3488871464395447610708003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9303657238387860295221341 3488871464395447610708003)
                ·
                  refine ⟨5233307196593171416062005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488871464395447610708003 5233307196593171416062005)
                  ·
                    refine ⟨490622549680609820255813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5233307196593171416062005 490622549680609820255813)
                    ·
                      rfl

theorem cell22_1433226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1433226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433226 prefixEnd_1433226 := by exact prefixLift 1433226
  have htrace : WordTrace (prefixWord ++ tailWord_1433226) baseStart_1433226 baseEnd_1433226 := by
    simpa [prefixWord, tailWord_1433226, baseEnd_1433226] using wordTrace_append hprefix tailTrace_1433226
  have hstable : (prefixWord ++ tailWord_1433226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433226).length < 2 ^ (prefixWord ++ tailWord_1433226).sum := by decide
  have hdescent : baseEnd_1433226 < baseStart_1433226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433247 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 1, 4]
def baseStart_1433247 : Nat := 118140960795 + 1433247 * 2 ^ 59
def prefixEnd_1433247 : Nat := 4983230072969 + 3 ^ 40 * 1433247 * 2
def baseEnd_1433247 : Nat := 490629738409772765480749

theorem tailTrace_1433247 : CollatzResearch.WordTrace tailWord_1433247 prefixEnd_1433247 490629738409772765480749 := by
  unfold tailWord_1433247
  simp only [CollatzResearch.WordTrace]
  refine ⟨52274812638598372944849995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34849875092398915296566663 52274812638598372944849995)
  ·
    refine ⟨78412218957897559417274993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52274812638598372944849995 78412218957897559417274993)
    ·
      refine ⟨58809164218423169562956245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78412218957897559417274993 58809164218423169562956245)
      ·
        refine ⟨1378339786369293036631787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58809164218423169562956245 1378339786369293036631787)
        ·
          refine ⟨2067509679553939554947681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378339786369293036631787 2067509679553939554947681)
          ·
            refine ⟨1550632259665454666210761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067509679553939554947681 1550632259665454666210761)
            ·
              refine ⟨1162974194749090999658071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550632259665454666210761 1162974194749090999658071)
              ·
                refine ⟨1744461292123636499487107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162974194749090999658071 1744461292123636499487107)
                ·
                  refine ⟨2616691938185454749230661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744461292123636499487107 2616691938185454749230661)
                  ·
                    refine ⟨490629738409772765480749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2616691938185454749230661 490629738409772765480749)
                    ·
                      rfl

theorem cell22_1433247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_1433247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433247 prefixEnd_1433247 := by exact prefixLift 1433247
  have htrace : WordTrace (prefixWord ++ tailWord_1433247) baseStart_1433247 baseEnd_1433247 := by
    simpa [prefixWord, tailWord_1433247, baseEnd_1433247] using wordTrace_append hprefix tailTrace_1433247
  have hstable : (prefixWord ++ tailWord_1433247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433247).length < 2 ^ (prefixWord ++ tailWord_1433247).sum := by decide
  have hdescent : baseEnd_1433247 < baseStart_1433247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433290 : List Nat := [3, 1, 2, 1, 6, 1, 2, 6]
def baseStart_1433290 : Nat := 118140960795 + 1433290 * 2 ^ 59
def prefixEnd_1433290 : Nat := 4983230072969 + 3 ^ 40 * 1433290 * 2
def baseEnd_1433290 : Nat := 54516050909837220739513

theorem tailTrace_1433290 : CollatzResearch.WordTrace tailWord_1433290 prefixEnd_1433290 54516050909837220739513 := by
  unfold tailWord_1433290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069095244360647822166331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34850920651628394192443549 13069095244360647822166331)
  ·
    refine ⟨19603642866540971733249497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13069095244360647822166331 19603642866540971733249497)
    ·
      refine ⟨14702732149905728799937123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19603642866540971733249497 14702732149905728799937123)
      ·
        refine ⟨22054098224858593199905685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14702732149905728799937123 22054098224858593199905685)
        ·
          refine ⟨1033785854290246556245579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22054098224858593199905685 1033785854290246556245579)
          ·
            refine ⟨1550678781435369834368369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033785854290246556245579 1550678781435369834368369)
            ·
              refine ⟨1163009086076527375776277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550678781435369834368369 1163009086076527375776277)
              ·
                refine ⟨54516050909837220739513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1163009086076527375776277 54516050909837220739513)
                ·
                  rfl

theorem cell22_1433290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_1433290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433290 prefixEnd_1433290 := by exact prefixLift 1433290
  have htrace : WordTrace (prefixWord ++ tailWord_1433290) baseStart_1433290 baseEnd_1433290 := by
    simpa [prefixWord, tailWord_1433290, baseEnd_1433290] using wordTrace_append hprefix tailTrace_1433290
  have hstable : (prefixWord ++ tailWord_1433290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433290).length < 2 ^ (prefixWord ++ tailWord_1433290).sum := by decide
  have hdescent : baseEnd_1433290 < baseStart_1433290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433305 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 1, 3]
def baseStart_1433305 : Nat := 118140960795 + 1433305 * 2 ^ 59
def prefixEnd_1433305 : Nat := 4983230072969 + 3 ^ 40 * 1433305 * 2
def baseEnd_1433305 : Nat := 490649592995079947530571

theorem tailTrace_1433305 : CollatzResearch.WordTrace tailWord_1433305 prefixEnd_1433305 490649592995079947530571 := by
  unfold tailWord_1433305
  simp only [CollatzResearch.WordTrace]
  refine ⟨52276928072388248850461369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34851285381592165900307579 52276928072388248850461369)
  ·
    refine ⟨39207696054291186637846027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52276928072388248850461369 39207696054291186637846027)
    ·
      refine ⟨58811544081436779956769041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39207696054291186637846027 58811544081436779956769041)
      ·
        refine ⟨44108658061077584967576781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58811544081436779956769041 44108658061077584967576781)
        ·
          refine ⟨16540746772904094362841293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44108658061077584967576781 16540746772904094362841293)
          ·
            refine ⟨6202780039839035386065485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16540746772904094362841293 6202780039839035386065485)
            ·
              refine ⟨2326042514939638269774557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6202780039839035386065485 2326042514939638269774557)
              ·
                refine ⟨872265943102364351165459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326042514939638269774557 872265943102364351165459)
                ·
                  refine ⟨1308398914653546526748189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872265943102364351165459 1308398914653546526748189)
                  ·
                    refine ⟨490649592995079947530571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308398914653546526748189 490649592995079947530571)
                    ·
                      rfl

theorem cell22_1433305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_1433305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433305 prefixEnd_1433305 := by exact prefixLift 1433305
  have htrace : WordTrace (prefixWord ++ tailWord_1433305) baseStart_1433305 baseEnd_1433305 := by
    simpa [prefixWord, tailWord_1433305, baseEnd_1433305] using wordTrace_append hprefix tailTrace_1433305
  have hstable : (prefixWord ++ tailWord_1433305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433305).length < 2 ^ (prefixWord ++ tailWord_1433305).sum := by decide
  have hdescent : baseEnd_1433305 < baseStart_1433305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433348 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1433348 : Nat := 118140960795 + 1433348 * 2 ^ 59
def prefixEnd_1433348 : Nat := 4983230072969 + 3 ^ 40 * 1433348 * 2
def baseEnd_1433348 : Nat := 490664312773842168705439

theorem tailTrace_1433348 : CollatzResearch.WordTrace tailWord_1433348 prefixEnd_1433348 490664312773842168705439 := by
  unfold tailWord_1433348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26139248205616233597138349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34852330940821644796184465 26139248205616233597138349)
  ·
    refine ⟨9802218077106087598926881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26139248205616233597138349 9802218077106087598926881)
    ·
      refine ⟨7351663557829565699195161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9802218077106087598926881 7351663557829565699195161)
      ·
        refine ⟨5513747668372174274396371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7351663557829565699195161 5513747668372174274396371)
        ·
          refine ⟨8270621502558261411594557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513747668372174274396371 8270621502558261411594557)
          ·
            refine ⟨3101483063459348029347959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8270621502558261411594557 3101483063459348029347959)
            ·
              refine ⟨4652224595189022044021939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101483063459348029347959 4652224595189022044021939)
              ·
                refine ⟨6978336892783533066032909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652224595189022044021939 6978336892783533066032909)
                ·
                  refine ⟨2616876334793824899762341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6978336892783533066032909 2616876334793824899762341)
                  ·
                    refine ⟨490664312773842168705439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2616876334793824899762341 490664312773842168705439)
                    ·
                      rfl

theorem cell22_1433348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1433348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433348 prefixEnd_1433348 := by exact prefixLift 1433348
  have htrace : WordTrace (prefixWord ++ tailWord_1433348) baseStart_1433348 baseEnd_1433348 := by
    simpa [prefixWord, tailWord_1433348, baseEnd_1433348] using wordTrace_append hprefix tailTrace_1433348
  have hstable : (prefixWord ++ tailWord_1433348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433348).length < 2 ^ (prefixWord ++ tailWord_1433348).sum := by decide
  have hdescent : baseEnd_1433348 < baseStart_1433348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433365 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1433365 : Nat := 118140960795 + 1433365 * 2 ^ 59
def prefixEnd_1433365 : Nat := 4983230072969 + 3 ^ 40 * 1433365 * 2
def baseEnd_1433365 : Nat := 490670132221259791030387

theorem tailTrace_1433365 : CollatzResearch.WordTrace tailWord_1433365 prefixEnd_1433365 490670132221259791030387 := by
  unfold tailWord_1433365
  simp only [CollatzResearch.WordTrace]
  refine ⟨52279116452170879097645549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34852744301447252731763699 52279116452170879097645549)
  ·
    refine ⟨19604668669564079661617081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52279116452170879097645549 19604668669564079661617081)
    ·
      refine ⟨14703501502173059746212811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19604668669564079661617081 14703501502173059746212811)
      ·
        refine ⟨22055252253259589619319217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14703501502173059746212811 22055252253259589619319217)
        ·
          refine ⟨16541439189944692214489413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22055252253259589619319217 16541439189944692214489413)
          ·
            refine ⟨3101519848114629790216765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16541439189944692214489413 3101519848114629790216765)
            ·
              refine ⟨1163069943042986171331287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3101519848114629790216765 1163069943042986171331287)
              ·
                refine ⟨1744604914564479256996931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163069943042986171331287 1744604914564479256996931)
                ·
                  refine ⟨2616907371846718885495397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744604914564479256996931 2616907371846718885495397)
                  ·
                    refine ⟨490670132221259791030387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2616907371846718885495397 490670132221259791030387)
                    ·
                      rfl

theorem cell22_1433365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1433365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433365 prefixEnd_1433365 := by exact prefixLift 1433365
  have htrace : WordTrace (prefixWord ++ tailWord_1433365) baseStart_1433365 baseEnd_1433365 := by
    simpa [prefixWord, tailWord_1433365, baseEnd_1433365] using wordTrace_append hprefix tailTrace_1433365
  have hstable : (prefixWord ++ tailWord_1433365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433365).length < 2 ^ (prefixWord ++ tailWord_1433365).sum := by decide
  have hdescent : baseEnd_1433365 < baseStart_1433365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433380 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1433380 : Nat := 118140960795 + 1433380 * 2 ^ 59
def prefixEnd_1433380 : Nat := 4983230072969 + 3 ^ 40 * 1433380 * 2
def baseEnd_1433380 : Nat := 163558422342601583968447

theorem tailTrace_1433380 : CollatzResearch.WordTrace tailWord_1433380 prefixEnd_1433380 163558422342601583968447 := by
  unfold tailWord_1433380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26139831773558268329720797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34853109031411024439627729 26139831773558268329720797)
  ·
    refine ⟨9802436915084350623645299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26139831773558268329720797 9802436915084350623645299)
    ·
      refine ⟨14703655372626525935467949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9802436915084350623645299 14703655372626525935467949)
      ·
        refine ⟨5513870764734947225800481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14703655372626525935467949 5513870764734947225800481)
        ·
          refine ⟨4135403073551210419350361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5513870764734947225800481 4135403073551210419350361)
          ·
            refine ⟨3101552305163407814512771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4135403073551210419350361 3101552305163407814512771)
            ·
              refine ⟨4652328457745111721769157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101552305163407814512771 4652328457745111721769157)
              ·
                refine ⟨872311585827208447831717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4652328457745111721769157 872311585827208447831717)
                ·
                  refine ⟨163558422342601583968447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872311585827208447831717 163558422342601583968447)
                  ·
                    rfl

theorem cell22_1433380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1433380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433380 prefixEnd_1433380 := by exact prefixLift 1433380
  have htrace : WordTrace (prefixWord ++ tailWord_1433380) baseStart_1433380 baseEnd_1433380 := by
    simpa [prefixWord, tailWord_1433380, baseEnd_1433380] using wordTrace_append hprefix tailTrace_1433380
  have hstable : (prefixWord ++ tailWord_1433380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433380).length < 2 ^ (prefixWord ++ tailWord_1433380).sum := by decide
  have hdescent : baseEnd_1433380 < baseStart_1433380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433414 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1433414 : Nat := 118140960795 + 1433414 * 2 ^ 59
def prefixEnd_1433414 : Nat := 4983230072969 + 3 ^ 40 * 1433414 * 2
def baseEnd_1433414 : Nat := 163562301974213332185079

theorem tailTrace_1433414 : CollatzResearch.WordTrace tailWord_1433414 prefixEnd_1433414 163562301974213332185079 := by
  unfold tailWord_1433414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633778238406042514568103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34853935752662240310786197 1633778238406042514568103)
  ·
    refine ⟨2450667357609063771852155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633778238406042514568103 2450667357609063771852155)
    ·
      refine ⟨3676001036413595657778233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450667357609063771852155 3676001036413595657778233)
      ·
        refine ⟨2757000777310196743333675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3676001036413595657778233 2757000777310196743333675)
        ·
          refine ⟨4135501165965295115000513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757000777310196743333675 4135501165965295115000513)
          ·
            refine ⟨3101625874473971336250385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4135501165965295115000513 3101625874473971336250385)
            ·
              refine ⟨2326219405855478502187789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3101625874473971336250385 2326219405855478502187789)
              ·
                refine ⟨872332277195804438320421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326219405855478502187789 872332277195804438320421)
                ·
                  refine ⟨163562301974213332185079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872332277195804438320421 163562301974213332185079)
                  ·
                    rfl

theorem cell22_1433414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1433414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433414 prefixEnd_1433414 := by exact prefixLift 1433414
  have htrace : WordTrace (prefixWord ++ tailWord_1433414) baseStart_1433414 baseEnd_1433414 := by
    simpa [prefixWord, tailWord_1433414, baseEnd_1433414] using wordTrace_append hprefix tailTrace_1433414
  have hstable : (prefixWord ++ tailWord_1433414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433414).length < 2 ^ (prefixWord ++ tailWord_1433414).sum := by decide
  have hdescent : baseEnd_1433414 < baseStart_1433414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433440 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_1433440 : Nat := 118140960795 + 1433440 * 2 ^ 59
def prefixEnd_1433440 : Nat := 4983230072969 + 3 ^ 40 * 1433440 * 2
def baseEnd_1433440 : Nat := 490695806253984595405157

theorem tailTrace_1433440 : CollatzResearch.WordTrace tailWord_1433440 prefixEnd_1433440 490695806253984595405157 := by
  unfold tailWord_1433440
  simp only [CollatzResearch.WordTrace]
  refine ⟨26140925963449583453312887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34854567951266111271083849 26140925963449583453312887)
  ·
    refine ⟨39211388945174375179969331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26140925963449583453312887 39211388945174375179969331)
    ·
      refine ⟨58817083417761562769953997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39211388945174375179969331 58817083417761562769953997)
      ·
        refine ⟨22056406281660586038732749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58817083417761562769953997 22056406281660586038732749)
        ·
          refine ⟨8271152355622719764524781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22056406281660586038732749 8271152355622719764524781)
          ·
            refine ⟨3101682133358519911696793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8271152355622719764524781 3101682133358519911696793)
            ·
              refine ⟨2326261600018889933772595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3101682133358519911696793 2326261600018889933772595)
              ·
                refine ⟨3489392400028334900658893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326261600018889933772595 3489392400028334900658893)
                ·
                  refine ⟨1308522150010625587747085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3489392400028334900658893 1308522150010625587747085)
                  ·
                    refine ⟨490695806253984595405157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308522150010625587747085 490695806253984595405157)
                    ·
                      rfl

theorem cell22_1433440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_1433440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433440 prefixEnd_1433440 := by exact prefixLift 1433440
  have htrace : WordTrace (prefixWord ++ tailWord_1433440) baseStart_1433440 baseEnd_1433440 := by
    simpa [prefixWord, tailWord_1433440, baseEnd_1433440] using wordTrace_append hprefix tailTrace_1433440
  have hstable : (prefixWord ++ tailWord_1433440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433440).length < 2 ^ (prefixWord ++ tailWord_1433440).sum := by decide
  have hdescent : baseEnd_1433440 < baseStart_1433440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433453 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1433453 : Nat := 118140960795 + 1433453 * 2 ^ 59
def prefixEnd_1433453 : Nat := 4983230072969 + 3 ^ 40 * 1433453 * 2
def baseEnd_1433453 : Nat := 163566752139885631610039

theorem tailTrace_1433453 : CollatzResearch.WordTrace tailWord_1433453 prefixEnd_1433453 163566752139885631610039 := by
  unfold tailWord_1433453
  simp only [CollatzResearch.WordTrace]
  refine ⟨52282326075852070126849013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34854884050568046751232675 52282326075852070126849013)
  ·
    refine ⟨4901468069611131574392095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52282326075852070126849013 4901468069611131574392095)
    ·
      refine ⟨7352202104416697361588143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901468069611131574392095 7352202104416697361588143)
      ·
        refine ⟨11028303156625046042382215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352202104416697361588143 11028303156625046042382215)
        ·
          refine ⟨16542454734937569063573323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028303156625046042382215 16542454734937569063573323)
          ·
            refine ⟨24813682102406353595359985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16542454734937569063573323 24813682102406353595359985)
            ·
              refine ⟨18610261576804765196519989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24813682102406353595359985 18610261576804765196519989)
              ·
                refine ⟨1744712022825446737173749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18610261576804765196519989 1744712022825446737173749)
                ·
                  refine ⟨163566752139885631610039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1744712022825446737173749 163566752139885631610039)
                  ·
                    rfl

theorem cell22_1433453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1433453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433453 prefixEnd_1433453 := by exact prefixLift 1433453
  have htrace : WordTrace (prefixWord ++ tailWord_1433453) baseStart_1433453 baseEnd_1433453 := by
    simpa [prefixWord, tailWord_1433453, baseEnd_1433453] using wordTrace_append hprefix tailTrace_1433453
  have hstable : (prefixWord ++ tailWord_1433453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433453).length < 2 ^ (prefixWord ++ tailWord_1433453).sum := by decide
  have hdescent : baseEnd_1433453 < baseStart_1433453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433470 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1433470 : Nat := 118140960795 + 1433470 * 2 ^ 59
def prefixEnd_1433470 : Nat := 4983230072969 + 3 ^ 40 * 1433470 * 2
def baseEnd_1433470 : Nat := 163568691955691505718355

theorem tailTrace_1433470 : CollatzResearch.WordTrace tailWord_1433470 prefixEnd_1433470 163568691955691505718355 := by
  unfold tailWord_1433470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535368264598810253777233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34855297411193654686811909 6535368264598810253777233)
  ·
    refine ⟨4901526198449107690332925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6535368264598810253777233 4901526198449107690332925)
    ·
      refine ⟨1838072324418415383874847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4901526198449107690332925 1838072324418415383874847)
      ·
        refine ⟨2757108486627623075812271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838072324418415383874847 2757108486627623075812271)
        ·
          refine ⟨4135662729941434613718407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757108486627623075812271 4135662729941434613718407)
          ·
            refine ⟨6203494094912151920577611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135662729941434613718407 6203494094912151920577611)
            ·
              refine ⟨9305241142368227880866417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203494094912151920577611 9305241142368227880866417)
              ·
                refine ⟨6978930856776170910649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9305241142368227880866417 6978930856776170910649813)
                ·
                  refine ⟨163568691955691505718355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6978930856776170910649813 163568691955691505718355)
                  ·
                    rfl

theorem cell22_1433470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1433470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433470 prefixEnd_1433470 := by exact prefixLift 1433470
  have htrace : WordTrace (prefixWord ++ tailWord_1433470) baseStart_1433470 baseEnd_1433470 := by
    simpa [prefixWord, tailWord_1433470, baseEnd_1433470] using wordTrace_append hprefix tailTrace_1433470
  have hstable : (prefixWord ++ tailWord_1433470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433470).length < 2 ^ (prefixWord ++ tailWord_1433470).sum := by decide
  have hdescent : baseEnd_1433470 < baseStart_1433470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433513 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_1433513 : Nat := 118140960795 + 1433513 * 2 ^ 59
def prefixEnd_1433513 : Nat := 4983230072969 + 3 ^ 40 * 1433513 * 2
def baseEnd_1433513 : Nat := 490720795645836738329933

theorem tailTrace_1433513 : CollatzResearch.WordTrace tailWord_1433513 prefixEnd_1433513 490720795645836738329933 := by
  unfold tailWord_1433513
  simp only [CollatzResearch.WordTrace]
  refine ⟨52284514455634700374033193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34856342970423133582688795 52284514455634700374033193)
  ·
    refine ⟨39213385841726025280524895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52284514455634700374033193 39213385841726025280524895)
    ·
      refine ⟨58820078762589037920787343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39213385841726025280524895 58820078762589037920787343)
      ·
        refine ⟨88230118143883556881181015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58820078762589037920787343 88230118143883556881181015)
        ·
          refine ⟨132345177215825335321771523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88230118143883556881181015 132345177215825335321771523)
          ·
            refine ⟨198517765823738002982657285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132345177215825335321771523 198517765823738002982657285)
            ·
              refine ⟨37222081091950875559248241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198517765823738002982657285 37222081091950875559248241)
              ·
                refine ⟨27916560818963156669436181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37222081091950875559248241 27916560818963156669436181)
                ·
                  refine ⟨1308588788388897968879821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27916560818963156669436181 1308588788388897968879821)
                  ·
                    refine ⟨490720795645836738329933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308588788388897968879821 490720795645836738329933)
                    ·
                      rfl

theorem cell22_1433513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_1433513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433513 prefixEnd_1433513 := by exact prefixLift 1433513
  have htrace : WordTrace (prefixWord ++ tailWord_1433513) baseStart_1433513 baseEnd_1433513 := by
    simpa [prefixWord, tailWord_1433513, baseEnd_1433513] using wordTrace_append hprefix tailTrace_1433513
  have hstable : (prefixWord ++ tailWord_1433513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433513).length < 2 ^ (prefixWord ++ tailWord_1433513).sum := by decide
  have hdescent : baseEnd_1433513 < baseStart_1433513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433592 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 1, 3]
def baseStart_1433592 : Nat := 118140960795 + 1433592 * 2 ^ 59
def prefixEnd_1433592 : Nat := 4983230072969 + 3 ^ 40 * 1433592 * 2
def baseEnd_1433592 : Nat := 490747838960306865604691

theorem tailTrace_1433592 : CollatzResearch.WordTrace tailWord_1433592 prefixEnd_1433592 490747838960306865604691 := by
  unfold tailWord_1433592
  simp only [CollatzResearch.WordTrace]
  refine ⟨26143697911174248433079515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34858263881565664577439353 26143697911174248433079515)
  ·
    refine ⟨39215546866761372649619273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26143697911174248433079515 39215546866761372649619273)
    ·
      refine ⟨29411660150071029487214455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39215546866761372649619273 29411660150071029487214455)
      ·
        refine ⟨44117490225106544230821683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411660150071029487214455 44117490225106544230821683)
        ·
          refine ⟨66176235337659816346232525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44117490225106544230821683 66176235337659816346232525)
          ·
            refine ⟨24816088251622431129837197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66176235337659816346232525 24816088251622431129837197)
            ·
              refine ⟨9306033094358411673688949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24816088251622431129837197 9306033094358411673688949)
              ·
                refine ⟨872440602596101094408339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9306033094358411673688949 872440602596101094408339)
                ·
                  refine ⟨1308660903894151641612509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872440602596101094408339 1308660903894151641612509)
                  ·
                    refine ⟨490747838960306865604691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308660903894151641612509 490747838960306865604691)
                    ·
                      rfl

theorem cell22_1433592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_1433592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433592 prefixEnd_1433592 := by exact prefixLift 1433592
  have htrace : WordTrace (prefixWord ++ tailWord_1433592) baseStart_1433592 baseEnd_1433592 := by
    simpa [prefixWord, tailWord_1433592, baseEnd_1433592] using wordTrace_append hprefix tailTrace_1433592
  have hstable : (prefixWord ++ tailWord_1433592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433592).length < 2 ^ (prefixWord ++ tailWord_1433592).sum := by decide
  have hdescent : baseEnd_1433592 < baseStart_1433592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433605 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 5]
def baseStart_1433605 : Nat := 118140960795 + 1433605 * 2 ^ 59
def prefixEnd_1433605 : Nat := 4983230072969 + 3 ^ 40 * 1433605 * 2
def baseEnd_1433605 : Nat := 163584096375326388343217

theorem tailTrace_1433605 : CollatzResearch.WordTrace tailWord_1433605 prefixEnd_1433605 163584096375326388343217 := by
  unfold tailWord_1433605
  simp only [CollatzResearch.WordTrace]
  refine ⟨52287869971301400086382269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34858579980867600057588179 52287869971301400086382269)
  ·
    refine ⟨19607951239238025032393351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52287869971301400086382269 19607951239238025032393351)
    ·
      refine ⟨29411926858857037548590027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19607951239238025032393351 29411926858857037548590027)
      ·
        refine ⟨44117890288285556322885041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411926858857037548590027 44117890288285556322885041)
        ·
          refine ⟨33088417716214167242163781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44117890288285556322885041 33088417716214167242163781)
          ·
            refine ⟨6204078321790156357905709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33088417716214167242163781 6204078321790156357905709)
            ·
              refine ⟨2326529370671308634214641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6204078321790156357905709 2326529370671308634214641)
              ·
                refine ⟨1744897028003481475660981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326529370671308634214641 1744897028003481475660981)
                ·
                  refine ⟨163584096375326388343217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1744897028003481475660981 163584096375326388343217)
                  ·
                    rfl

theorem cell22_1433605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_1433605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433605 prefixEnd_1433605 := by exact prefixLift 1433605
  have htrace : WordTrace (prefixWord ++ tailWord_1433605) baseStart_1433605 baseEnd_1433605 := by
    simpa [prefixWord, tailWord_1433605, baseEnd_1433605] using wordTrace_append hprefix tailTrace_1433605
  have hstable : (prefixWord ++ tailWord_1433605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433605).length < 2 ^ (prefixWord ++ tailWord_1433605).sum := by decide
  have hdescent : baseEnd_1433605 < baseStart_1433605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433686 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1433686 : Nat := 118140960795 + 1433686 * 2 ^ 59
def prefixEnd_1433686 : Nat := 4983230072969 + 3 ^ 40 * 1433686 * 2
def baseEnd_1433686 : Nat := 490780017081321953754403

theorem tailTrace_1433686 : CollatzResearch.WordTrace tailWord_1433686 prefixEnd_1433686 490780017081321953754403 := by
  unfold tailWord_1433686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268176517750496932505057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34860549522671967280053941 3268176517750496932505057)
  ·
    refine ⟨2451132388312872699378793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3268176517750496932505057 2451132388312872699378793)
    ·
      refine ⟨1838349291234654524534095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2451132388312872699378793 1838349291234654524534095)
      ·
        refine ⟨2757523936851981786801143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838349291234654524534095 2757523936851981786801143)
        ·
          refine ⟨4136285905277972680201715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757523936851981786801143 4136285905277972680201715)
          ·
            refine ⟨6204428857916959020302573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136285905277972680201715 6204428857916959020302573)
            ·
              refine ⟨2326660821718859632613465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6204428857916959020302573 2326660821718859632613465)
              ·
                refine ⟨1744995616289144724460099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326660821718859632613465 1744995616289144724460099)
                ·
                  refine ⟨2617493424433717086690149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744995616289144724460099 2617493424433717086690149)
                  ·
                    refine ⟨490780017081321953754403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2617493424433717086690149 490780017081321953754403)
                    ·
                      rfl

theorem cell22_1433686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1433686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433686 prefixEnd_1433686 := by exact prefixLift 1433686
  have htrace : WordTrace (prefixWord ++ tailWord_1433686) baseStart_1433686 baseEnd_1433686 := by
    simpa [prefixWord, tailWord_1433686, baseEnd_1433686] using wordTrace_append hprefix tailTrace_1433686
  have hstable : (prefixWord ++ tailWord_1433686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433686).length < 2 ^ (prefixWord ++ tailWord_1433686).sum := by decide
  have hdescent : baseEnd_1433686 < baseStart_1433686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433725 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1433725 : Nat := 118140960795 + 1433725 * 2 ^ 59
def prefixEnd_1433725 : Nat := 4983230072969 + 3 ^ 40 * 1433725 * 2
def baseEnd_1433725 : Nat := 490793367578338852029283

theorem tailTrace_1433725 : CollatzResearch.WordTrace tailWord_1433725 prefixEnd_1433725 490793367578338852029283 := by
  unfold tailWord_1433725
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292246730866660580750629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34861497820577773720500419 52292246730866660580750629)
  ·
    refine ⟨9804796262037498858890743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52292246730866660580750629 9804796262037498858890743)
    ·
      refine ⟨14707194393056248288336115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9804796262037498858890743 14707194393056248288336115)
      ·
        refine ⟨22060791589584372432504173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707194393056248288336115 22060791589584372432504173)
        ·
          refine ⟨8272796846094139662189065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22060791589584372432504173 8272796846094139662189065)
          ·
            refine ⟨6204597634570604746641799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8272796846094139662189065 6204597634570604746641799)
            ·
              refine ⟨9306896451855907119962699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204597634570604746641799 9306896451855907119962699)
              ·
                refine ⟨13960344677783860679944049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306896451855907119962699 13960344677783860679944049)
                ·
                  refine ⟨10470258508337895509958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13960344677783860679944049 10470258508337895509958037)
                  ·
                    refine ⟨490793367578338852029283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10470258508337895509958037 490793367578338852029283)
                    ·
                      rfl

theorem cell22_1433725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1433725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433725 prefixEnd_1433725 := by exact prefixLift 1433725
  have htrace : WordTrace (prefixWord ++ tailWord_1433725) baseStart_1433725 baseEnd_1433725 := by
    simpa [prefixWord, tailWord_1433725, baseEnd_1433725] using wordTrace_append hprefix tailTrace_1433725
  have hstable : (prefixWord ++ tailWord_1433725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433725).length < 2 ^ (prefixWord ++ tailWord_1433725).sum := by decide
  have hdescent : baseEnd_1433725 < baseStart_1433725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433729 : List Nat := [1, 2, 4, 2, 4, 1, 1, 7]
def baseStart_1433729 : Nat := 118140960795 + 1433729 * 2 ^ 59
def prefixEnd_1433729 : Nat := 4983230072969 + 3 ^ 40 * 1433729 * 2
def baseEnd_1433729 : Nat := 54532748540009352769919

theorem tailTrace_1433729 : CollatzResearch.WordTrace tailWord_1433729 prefixEnd_1433729 54532748540009352769919 := by
  unfold tailWord_1433729
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292392622852169263896241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34861595081901446175930827 52292392622852169263896241)
  ·
    refine ⟨39219294467139126947922181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52292392622852169263896241 39219294467139126947922181)
    ·
      refine ⟨7353617712588586302735409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39219294467139126947922181 7353617712588586302735409)
      ·
        refine ⟨5515213284441439727051557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7353617712588586302735409 5515213284441439727051557)
        ·
          refine ⟨1034102490832769948822167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5515213284441439727051557 1034102490832769948822167)
          ·
            refine ⟨1551153736249154923233251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034102490832769948822167 1551153736249154923233251)
            ·
              refine ⟨2326730604373732384849877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551153736249154923233251 2326730604373732384849877)
              ·
                refine ⟨54532748540009352769919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2326730604373732384849877 54532748540009352769919)
                ·
                  rfl

theorem cell22_1433729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 7].length) (baseStart_1433729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433729 prefixEnd_1433729 := by exact prefixLift 1433729
  have htrace : WordTrace (prefixWord ++ tailWord_1433729) baseStart_1433729 baseEnd_1433729 := by
    simpa [prefixWord, tailWord_1433729, baseEnd_1433729] using wordTrace_append hprefix tailTrace_1433729
  have hstable : (prefixWord ++ tailWord_1433729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433729).length < 2 ^ (prefixWord ++ tailWord_1433729).sum := by decide
  have hdescent : baseEnd_1433729 < baseStart_1433729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433748 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1433748 : Nat := 118140960795 + 1433748 * 2 ^ 59
def prefixEnd_1433748 : Nat := 4983230072969 + 3 ^ 40 * 1433748 * 2
def baseEnd_1433748 : Nat := 490801240948374458704213

theorem tailTrace_1433748 : CollatzResearch.WordTrace tailWord_1433748 prefixEnd_1433748 490801240948374458704213 := by
  unfold tailWord_1433748
  simp only [CollatzResearch.WordTrace]
  refine ⟨26146542804891667754418949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34862057073188890339225265 26146542804891667754418949)
  ·
    refine ⟨4902476775917187703953553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26146542804891667754418949 4902476775917187703953553)
    ·
      refine ⟨3676857581937890777965165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4902476775917187703953553 3676857581937890777965165)
      ·
        refine ⟨1378821593226709041736937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3676857581937890777965165 1378821593226709041736937)
        ·
          refine ⟨1034116194920031781302703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378821593226709041736937 1034116194920031781302703)
          ·
            refine ⟨1551174292380047671954055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034116194920031781302703 1551174292380047671954055)
            ·
              refine ⟨2326761438570071507931083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551174292380047671954055 2326761438570071507931083)
              ·
                refine ⟨3490142157855107261896625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326761438570071507931083 3490142157855107261896625)
                ·
                  refine ⟨2617606618391330446422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3490142157855107261896625 2617606618391330446422469)
                  ·
                    refine ⟨490801240948374458704213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2617606618391330446422469 490801240948374458704213)
                    ·
                      rfl

theorem cell22_1433748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1433748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433748 prefixEnd_1433748 := by exact prefixLift 1433748
  have htrace : WordTrace (prefixWord ++ tailWord_1433748) baseStart_1433748 baseEnd_1433748 := by
    simpa [prefixWord, tailWord_1433748, baseEnd_1433748] using wordTrace_append hprefix tailTrace_1433748
  have hstable : (prefixWord ++ tailWord_1433748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433748).length < 2 ^ (prefixWord ++ tailWord_1433748).sum := by decide
  have hdescent : baseEnd_1433748 < baseStart_1433748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433761 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1433761 : Nat := 118140960795 + 1433761 * 2 ^ 59
def prefixEnd_1433761 : Nat := 4983230072969 + 3 ^ 40 * 1433761 * 2
def baseEnd_1433761 : Nat := 490805691114046758129173

theorem tailTrace_1433761 : CollatzResearch.WordTrace tailWord_1433761 prefixEnd_1433761 490805691114046758129173 := by
  unfold tailWord_1433761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52293559758736238729061137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34862373172490825819374091 52293559758736238729061137)
  ·
    refine ⟨39220169819052179046795853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52293559758736238729061137 39220169819052179046795853)
    ·
      refine ⟨14707563682144567142548445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39220169819052179046795853 14707563682144567142548445)
      ·
        refine ⟨5515336380804212678455667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14707563682144567142548445 5515336380804212678455667)
        ·
          refine ⟨8273004571206319017683501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515336380804212678455667 8273004571206319017683501)
          ·
            refine ⟨3102376714202369631631313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8273004571206319017683501 3102376714202369631631313)
            ·
              refine ⟨2326782535651777223723485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102376714202369631631313 2326782535651777223723485)
              ·
                refine ⟨872543450869416458896307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326782535651777223723485 872543450869416458896307)
                ·
                  refine ⟨1308815176304124688344461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872543450869416458896307 1308815176304124688344461)
                  ·
                    refine ⟨490805691114046758129173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308815176304124688344461 490805691114046758129173)
                    ·
                      rfl

theorem cell22_1433761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1433761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433761 prefixEnd_1433761 := by exact prefixLift 1433761
  have htrace : WordTrace (prefixWord ++ tailWord_1433761) baseStart_1433761 baseEnd_1433761 := by
    simpa [prefixWord, tailWord_1433761, baseEnd_1433761] using wordTrace_append hprefix tailTrace_1433761
  have hstable : (prefixWord ++ tailWord_1433761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433761).length < 2 ^ (prefixWord ++ tailWord_1433761).sum := by decide
  have hdescent : baseEnd_1433761 < baseStart_1433761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433817 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_1433817 : Nat := 118140960795 + 1433817 * 2 ^ 59
def prefixEnd_1433817 : Nat := 4983230072969 + 3 ^ 40 * 1433817 * 2
def baseEnd_1433817 : Nat := 490824861058481278729001

theorem tailTrace_1433817 : CollatzResearch.WordTrace tailWord_1433817 prefixEnd_1433817 490824861058481278729001 := by
  unfold tailWord_1433817
  simp only [CollatzResearch.WordTrace]
  refine ⟨52295602246533360293099705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34863734831022240195399803 52295602246533360293099705)
  ·
    refine ⟨39221701684900020219824779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52295602246533360293099705 39221701684900020219824779)
    ·
      refine ⟨58832552527350030329737169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39221701684900020219824779 58832552527350030329737169)
      ·
        refine ⟨44124414395512522747302877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58832552527350030329737169 44124414395512522747302877)
        ·
          refine ⟨16546655398317196030238579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44124414395512522747302877 16546655398317196030238579)
          ·
            refine ⟨24819983097475794045357869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16546655398317196030238579 24819983097475794045357869)
            ·
              refine ⟨9307493661553422767009201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24819983097475794045357869 9307493661553422767009201)
              ·
                refine ⟨6980620246165067075256901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9307493661553422767009201 6980620246165067075256901)
                ·
                  refine ⟨1308866296155950076610669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6980620246165067075256901 1308866296155950076610669)
                  ·
                    refine ⟨490824861058481278729001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308866296155950076610669 490824861058481278729001)
                    ·
                      rfl

theorem cell22_1433817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_1433817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433817 prefixEnd_1433817 := by exact prefixLift 1433817
  have htrace : WordTrace (prefixWord ++ tailWord_1433817) baseStart_1433817 baseEnd_1433817 := by
    simpa [prefixWord, tailWord_1433817, baseEnd_1433817] using wordTrace_append hprefix tailTrace_1433817
  have hstable : (prefixWord ++ tailWord_1433817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433817).length < 2 ^ (prefixWord ++ tailWord_1433817).sum := by decide
  have hdescent : baseEnd_1433817 < baseStart_1433817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433832 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1433832 : Nat := 118140960795 + 1433832 * 2 ^ 59
def prefixEnd_1433832 : Nat := 4983230072969 + 3 ^ 40 * 1433832 * 2
def baseEnd_1433832 : Nat := 490829995865026239603955

theorem tailTrace_1433832 : CollatzResearch.WordTrace tailWord_1433832 prefixEnd_1433832 490829995865026239603955 := by
  unfold tailWord_1433832
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148074670739508927447875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34864099560986011903263833 26148074670739508927447875)
  ·
    refine ⟨39222112006109263391171813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26148074670739508927447875 39222112006109263391171813)
    ·
      refine ⟨7354146001145486885844715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39222112006109263391171813 7354146001145486885844715)
      ·
        refine ⟨11031219001718230328767073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7354146001145486885844715 11031219001718230328767073)
        ·
          refine ⟨8273414251288672746575305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11031219001718230328767073 8273414251288672746575305)
          ·
            refine ⟨6205060688466504559931479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8273414251288672746575305 6205060688466504559931479)
            ·
              refine ⟨9307591032699756839897219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205060688466504559931479 9307591032699756839897219)
              ·
                refine ⟨13961386549049635259845829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9307591032699756839897219 13961386549049635259845829)
                ·
                  refine ⟨2617759977946806611221093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13961386549049635259845829 2617759977946806611221093)
                  ·
                    refine ⟨490829995865026239603955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2617759977946806611221093 490829995865026239603955)
                    ·
                      rfl

theorem cell22_1433832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1433832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433832 prefixEnd_1433832 := by exact prefixLift 1433832
  have htrace : WordTrace (prefixWord ++ tailWord_1433832) baseStart_1433832 baseEnd_1433832 := by
    simpa [prefixWord, tailWord_1433832, baseEnd_1433832] using wordTrace_append hprefix tailTrace_1433832
  have hstable : (prefixWord ++ tailWord_1433832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433832).length < 2 ^ (prefixWord ++ tailWord_1433832).sum := by decide
  have hdescent : baseEnd_1433832 < baseStart_1433832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433834 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1433834 : Nat := 118140960795 + 1433834 * 2 ^ 59
def prefixEnd_1433834 : Nat := 4983230072969 + 3 ^ 40 * 1433834 * 2
def baseEnd_1433834 : Nat := 490830680505898901053949

theorem tailTrace_1433834 : CollatzResearch.WordTrace tailWord_1433834 prefixEnd_1433834 490830680505898901053949 := by
  unfold tailWord_1433834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13074055571867943049117139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34864148191647848130979037 13074055571867943049117139)
  ·
    refine ⟨19611083357801914573675709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13074055571867943049117139 19611083357801914573675709)
    ·
      refine ⟨7354156259175717965128391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19611083357801914573675709 7354156259175717965128391)
      ·
        refine ⟨11031234388763576947692587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7354156259175717965128391 11031234388763576947692587)
        ·
          refine ⟨16546851583145365421538881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11031234388763576947692587 16546851583145365421538881)
          ·
            refine ⟨12410138687359024066154161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16546851583145365421538881 12410138687359024066154161)
            ·
              refine ⟨9307604015519268049615621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12410138687359024066154161 9307604015519268049615621)
              ·
                refine ⟨1745175752909862759302929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9307604015519268049615621 1745175752909862759302929)
                ·
                  refine ⟨1308881814682397069477197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1745175752909862759302929 1308881814682397069477197)
                  ·
                    refine ⟨490830680505898901053949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1308881814682397069477197 490830680505898901053949)
                    ·
                      rfl

theorem cell22_1433834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1433834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433834 prefixEnd_1433834 := by exact prefixLift 1433834
  have htrace : WordTrace (prefixWord ++ tailWord_1433834) baseStart_1433834 baseEnd_1433834 := by
    simpa [prefixWord, tailWord_1433834, baseEnd_1433834] using wordTrace_append hprefix tailTrace_1433834
  have hstable : (prefixWord ++ tailWord_1433834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433834).length < 2 ^ (prefixWord ++ tailWord_1433834).sum := by decide
  have hdescent : baseEnd_1433834 < baseStart_1433834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433875 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 9]
def baseStart_1433875 : Nat := 118140960795 + 1433875 * 2 ^ 59
def prefixEnd_1433875 : Nat := 4983230072969 + 3 ^ 40 * 1433875 * 2
def baseEnd_1433875 : Nat := 163614905214596153592941

theorem tailTrace_1433875 : CollatzResearch.WordTrace tailWord_1433875 prefixEnd_1433875 163614905214596153592941 := by
  unfold tailWord_1433875
  simp only [CollatzResearch.WordTrace]
  refine ⟨52297717680323236198711079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34865145120215490799140719 52297717680323236198711079)
  ·
    refine ⟨78446576520484854298066619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52297717680323236198711079 78446576520484854298066619)
    ·
      refine ⟨117669864780727281447099929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78446576520484854298066619 117669864780727281447099929)
      ·
        refine ⟨88252398585545461085324947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117669864780727281447099929 88252398585545461085324947)
        ·
          refine ⟨132378597878318191627987421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88252398585545461085324947 132378597878318191627987421)
          ·
            refine ⟨49641974204369321860495283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132378597878318191627987421 49641974204369321860495283)
            ·
              refine ⟨74462961306553982790742925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49641974204369321860495283 74462961306553982790742925)
              ·
                refine ⟨27923610489957743546528597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74462961306553982790742925 27923610489957743546528597)
                ·
                  refine ⟨163614905214596153592941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27923610489957743546528597 163614905214596153592941)
                  ·
                    rfl

theorem cell22_1433875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_1433875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433875 prefixEnd_1433875 := by exact prefixLift 1433875
  have htrace : WordTrace (prefixWord ++ tailWord_1433875) baseStart_1433875 baseEnd_1433875 := by
    simpa [prefixWord, tailWord_1433875, baseEnd_1433875] using wordTrace_append hprefix tailTrace_1433875
  have hstable : (prefixWord ++ tailWord_1433875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433875).length < 2 ^ (prefixWord ++ tailWord_1433875).sum := by decide
  have hdescent : baseEnd_1433875 < baseStart_1433875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433907 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_1433907 : Nat := 118140960795 + 1433907 * 2 ^ 59
def prefixEnd_1433907 : Nat := 4983230072969 + 3 ^ 40 * 1433907 * 2
def baseEnd_1433907 : Nat := 490855669897751043978725

theorem tailTrace_1433907 : CollatzResearch.WordTrace tailWord_1433907 prefixEnd_1433907 490855669897751043978725 := by
  unfold tailWord_1433907
  simp only [CollatzResearch.WordTrace]
  refine ⟨52298884816207305663875975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34865923210804870442583983 52298884816207305663875975)
  ·
    refine ⟨78448327224310958495813963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52298884816207305663875975 78448327224310958495813963)
    ·
      refine ⟨117672490836466437743720945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78448327224310958495813963 117672490836466437743720945)
      ·
        refine ⟨88254368127349828307790709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117672490836466437743720945 88254368127349828307790709)
        ·
          refine ⟨8273847011939046403855379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88254368127349828307790709 8273847011939046403855379)
          ·
            refine ⟨12410770517908569605783069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273847011939046403855379 12410770517908569605783069)
            ·
              refine ⟨4654038944215713602168651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12410770517908569605783069 4654038944215713602168651)
              ·
                refine ⟨6981058416323570403252977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654038944215713602168651 6981058416323570403252977)
                ·
                  refine ⟨5235793812242677802439733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981058416323570403252977 5235793812242677802439733)
                  ·
                    refine ⟨490855669897751043978725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5235793812242677802439733 490855669897751043978725)
                    ·
                      rfl

theorem cell22_1433907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_1433907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433907 prefixEnd_1433907 := by exact prefixLift 1433907
  have htrace : WordTrace (prefixWord ++ tailWord_1433907) baseStart_1433907 baseEnd_1433907 := by
    simpa [prefixWord, tailWord_1433907, baseEnd_1433907] using wordTrace_append hprefix tailTrace_1433907
  have hstable : (prefixWord ++ tailWord_1433907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433907).length < 2 ^ (prefixWord ++ tailWord_1433907).sum := by decide
  have hdescent : baseEnd_1433907 < baseStart_1433907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433954 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1433954 : Nat := 118140960795 + 1433954 * 2 ^ 59
def prefixEnd_1433954 : Nat := 4983230072969 + 3 ^ 40 * 1433954 * 2
def baseEnd_1433954 : Nat := 163623919652752862684527

theorem tailTrace_1433954 : CollatzResearch.WordTrace tailWord_1433954 prefixEnd_1433954 163623919652752862684527 := by
  unfold tailWord_1433954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075149761759258172709229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34867066031358021793891277 13075149761759258172709229)
  ·
    refine ⟨4903181160659721814765961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13075149761759258172709229 4903181160659721814765961)
    ·
      refine ⟨3677385870494791361074471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903181160659721814765961 3677385870494791361074471)
      ·
        refine ⟨5516078805742187041611707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677385870494791361074471 5516078805742187041611707)
        ·
          refine ⟨8274118208613280562417561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516078805742187041611707 8274118208613280562417561)
          ·
            refine ⟨6205588656459960421813171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8274118208613280562417561 6205588656459960421813171)
            ·
              refine ⟨9308382984689940632719757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205588656459960421813171 9308382984689940632719757)
              ·
                refine ⟨3490643619258727737269909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9308382984689940632719757 3490643619258727737269909)
                ·
                  refine ⟨163623919652752862684527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3490643619258727737269909 163623919652752862684527)
                  ·
                    rfl

theorem cell22_1433954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1433954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433954 prefixEnd_1433954 := by exact prefixLift 1433954
  have htrace : WordTrace (prefixWord ++ tailWord_1433954) baseStart_1433954 baseEnd_1433954 := by
    simpa [prefixWord, tailWord_1433954, baseEnd_1433954] using wordTrace_append hprefix tailTrace_1433954
  have hstable : (prefixWord ++ tailWord_1433954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433954).length < 2 ^ (prefixWord ++ tailWord_1433954).sum := by decide
  have hdescent : baseEnd_1433954 < baseStart_1433954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433967 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_1433967 : Nat := 118140960795 + 1433967 * 2 ^ 59
def prefixEnd_1433967 : Nat := 4983230072969 + 3 ^ 40 * 1433967 * 2
def baseEnd_1433967 : Nat := 490876209123930887478541

theorem tailTrace_1433967 : CollatzResearch.WordTrace tailWord_1433967 prefixEnd_1433967 490876209123930887478541 := by
  unfold tailWord_1433967
  simp only [CollatzResearch.WordTrace]
  refine ⟨52301073195989935911060155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34867382130659957274040103 52301073195989935911060155)
  ·
    refine ⟨78451609793984903866590233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52301073195989935911060155 78451609793984903866590233)
    ·
      refine ⟨58838707345488677899942675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78451609793984903866590233 58838707345488677899942675)
      ·
        refine ⟨88258061018233016849914013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58838707345488677899942675 88258061018233016849914013)
        ·
          refine ⟨33096772881837381318717755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88258061018233016849914013 33096772881837381318717755)
          ·
            refine ⟨49645159322756071978076633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33096772881837381318717755 49645159322756071978076633)
            ·
              refine ⟨37233869492067053983557475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49645159322756071978076633 37233869492067053983557475)
              ·
                refine ⟨55850804238100580975336213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37233869492067053983557475 55850804238100580975336213)
                ·
                  refine ⟨2618006448660964733218885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55850804238100580975336213 2618006448660964733218885)
                  ·
                    refine ⟨490876209123930887478541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618006448660964733218885 490876209123930887478541)
                    ·
                      rfl

theorem cell22_1433967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_1433967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1433967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1433967 prefixEnd_1433967 := by exact prefixLift 1433967
  have htrace : WordTrace (prefixWord ++ tailWord_1433967) baseStart_1433967 baseEnd_1433967 := by
    simpa [prefixWord, tailWord_1433967, baseEnd_1433967] using wordTrace_append hprefix tailTrace_1433967
  have hstable : (prefixWord ++ tailWord_1433967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433967).length < 2 ^ (prefixWord ++ tailWord_1433967).sum := by decide
  have hdescent : baseEnd_1433967 < baseStart_1433967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434074 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_1434074 : Nat := 118140960795 + 1434074 * 2 ^ 59
def prefixEnd_1434074 : Nat := 4983230072969 + 3 ^ 40 * 1434074 * 2
def baseEnd_1434074 : Nat := 490912837410618275053213

theorem tailTrace_1434074 : CollatzResearch.WordTrace tailWord_1434074 prefixEnd_1434074 490912837410618275053213 := by
  unfold tailWord_1434074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076243951650573296301319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34869983871068195456803517 13076243951650573296301319)
  ·
    refine ⟨19614365927475859944451979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13076243951650573296301319 19614365927475859944451979)
    ·
      refine ⟨29421548891213789916677969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19614365927475859944451979 29421548891213789916677969)
      ·
        refine ⟨22066161668410342437508477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29421548891213789916677969 22066161668410342437508477)
        ·
          refine ⟨8274810625653878414065679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22066161668410342437508477 8274810625653878414065679)
          ·
            refine ⟨12412215938480817621098519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274810625653878414065679 12412215938480817621098519)
            ·
              refine ⟨18618323907721226431647779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12412215938480817621098519 18618323907721226431647779)
              ·
                refine ⟨27927485861581839647471669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18618323907721226431647779 27927485861581839647471669)
                ·
                  refine ⟨2618201799523297466950469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27927485861581839647471669 2618201799523297466950469)
                  ·
                    refine ⟨490912837410618275053213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618201799523297466950469 490912837410618275053213)
                    ·
                      rfl

theorem cell22_1434074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_1434074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434074 prefixEnd_1434074 := by exact prefixLift 1434074
  have htrace : WordTrace (prefixWord ++ tailWord_1434074) baseStart_1434074 baseEnd_1434074 := by
    simpa [prefixWord, tailWord_1434074, baseEnd_1434074] using wordTrace_append hprefix tailTrace_1434074
  have hstable : (prefixWord ++ tailWord_1434074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434074).length < 2 ^ (prefixWord ++ tailWord_1434074).sum := by decide
  have hdescent : baseEnd_1434074 < baseStart_1434074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434104 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1434104 : Nat := 118140960795 + 1434104 * 2 ^ 59
def prefixEnd_1434104 : Nat := 4983230072969 + 3 ^ 40 * 1434104 * 2
def baseEnd_1434104 : Nat := 490923107023708196803121

theorem tailTrace_1434104 : CollatzResearch.WordTrace tailWord_1434104 prefixEnd_1434104 490923107023708196803121 := by
  unfold tailWord_1434104
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153034998246804154398683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34870713330995738872531577 26153034998246804154398683)
  ·
    refine ⟨39229552497370206231598025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26153034998246804154398683 39229552497370206231598025)
    ·
      refine ⟨29422164373027654673698519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39229552497370206231598025 29422164373027654673698519)
      ·
        refine ⟨44133246559541482010547779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29422164373027654673698519 44133246559541482010547779)
        ·
          refine ⟨66199869839312223015821669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44133246559541482010547779 66199869839312223015821669)
          ·
            refine ⟨12412475594871041815466563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66199869839312223015821669 12412475594871041815466563)
            ·
              refine ⟨18618713392306562723199845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12412475594871041815466563 18618713392306562723199845)
              ·
                refine ⟨3491008761057480510599971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18618713392306562723199845 3491008761057480510599971)
                ·
                  refine ⟨5236513141586220765899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491008761057480510599971 5236513141586220765899957)
                  ·
                    refine ⟨490923107023708196803121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5236513141586220765899957 490923107023708196803121)
                    ·
                      rfl

theorem cell22_1434104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1434104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434104 prefixEnd_1434104 := by exact prefixLift 1434104
  have htrace : WordTrace (prefixWord ++ tailWord_1434104) baseStart_1434104 baseEnd_1434104 := by
    simpa [prefixWord, tailWord_1434104, baseEnd_1434104] using wordTrace_append hprefix tailTrace_1434104
  have hstable : (prefixWord ++ tailWord_1434104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434104).length < 2 ^ (prefixWord ++ tailWord_1434104).sum := by decide
  have hdescent : baseEnd_1434104 < baseStart_1434104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434121 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_1434121 : Nat := 118140960795 + 1434121 * 2 ^ 59
def prefixEnd_1434121 : Nat := 4983230072969 + 3 ^ 40 * 1434121 * 2
def baseEnd_1434121 : Nat := 490928926471125819128069

theorem tailTrace_1434121 : CollatzResearch.WordTrace tailWord_1434121 prefixEnd_1434121 490928926471125819128069 := by
  unfold tailWord_1434121
  simp only [CollatzResearch.WordTrace]
  refine ⟨52306690037432020212166217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34871126691621346808110811 52306690037432020212166217)
  ·
    refine ⟨39230017528074015159124663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52306690037432020212166217 39230017528074015159124663)
    ·
      refine ⟨58845026292111022738686995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39230017528074015159124663 58845026292111022738686995)
      ·
        refine ⟨88267539438166534108030493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58845026292111022738686995 88267539438166534108030493)
        ·
          refine ⟨33100327289312450290511435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88267539438166534108030493 33100327289312450290511435)
          ·
            refine ⟨49650490933968675435767153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33100327289312450290511435 49650490933968675435767153)
            ·
              refine ⟨37237868200476506576825365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49650490933968675435767153 37237868200476506576825365)
              ·
                refine ⟨1745525071897336245788689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37237868200476506576825365 1745525071897336245788689)
                ·
                  refine ⟨1309143803923002184341517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1745525071897336245788689 1309143803923002184341517)
                  ·
                    refine ⟨490928926471125819128069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309143803923002184341517 490928926471125819128069)
                    ·
                      rfl

theorem cell22_1434121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_1434121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434121 prefixEnd_1434121 := by exact prefixLift 1434121
  have htrace : WordTrace (prefixWord ++ tailWord_1434121) baseStart_1434121 baseEnd_1434121 := by
    simpa [prefixWord, tailWord_1434121, baseEnd_1434121] using wordTrace_append hprefix tailTrace_1434121
  have hstable : (prefixWord ++ tailWord_1434121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434121).length < 2 ^ (prefixWord ++ tailWord_1434121).sum := by decide
  have hdescent : baseEnd_1434121 < baseStart_1434121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434183 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1434183 : Nat := 118140960795 + 1434183 * 2 ^ 59
def prefixEnd_1434183 : Nat := 4983230072969 + 3 ^ 40 * 1434183 * 2
def baseEnd_1434183 : Nat := 490950150338178324077879

theorem tailTrace_1434183 : CollatzResearch.WordTrace tailWord_1434183 prefixEnd_1434183 490950150338178324077879 := by
  unfold tailWord_1434183
  simp only [CollatzResearch.WordTrace]
  refine ⟨52308951363207404800923203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34872634242138269867282135 52308951363207404800923203)
  ·
    refine ⟨78463427044811107201384805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52308951363207404800923203 78463427044811107201384805)
    ·
      refine ⟨14711892570902082600259651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78463427044811107201384805 14711892570902082600259651)
      ·
        refine ⟨22067838856353123900389477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14711892570902082600259651 22067838856353123900389477)
        ·
          refine ⟨4137719785566210731323027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22067838856353123900389477 4137719785566210731323027)
          ·
            refine ⟨6206579678349316096984541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137719785566210731323027 6206579678349316096984541)
            ·
              refine ⟨2327467379380993536369203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6206579678349316096984541 2327467379380993536369203)
              ·
                refine ⟨3491201069071490304553805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327467379380993536369203 3491201069071490304553805)
                ·
                  refine ⟨1309200400901808864207677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3491201069071490304553805 1309200400901808864207677)
                  ·
                    refine ⟨490950150338178324077879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309200400901808864207677 490950150338178324077879)
                    ·
                      rfl

theorem cell22_1434183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1434183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434183 prefixEnd_1434183 := by exact prefixLift 1434183
  have htrace : WordTrace (prefixWord ++ tailWord_1434183) baseStart_1434183 baseEnd_1434183 := by
    simpa [prefixWord, tailWord_1434183, baseEnd_1434183] using wordTrace_append hprefix tailTrace_1434183
  have hstable : (prefixWord ++ tailWord_1434183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434183).length < 2 ^ (prefixWord ++ tailWord_1434183).sum := by decide
  have hdescent : baseEnd_1434183 < baseStart_1434183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434230 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1434230 : Nat := 118140960795 + 1434230 * 2 ^ 59
def prefixEnd_1434230 : Nat := 4983230072969 + 3 ^ 40 * 1434230 * 2
def baseEnd_1434230 : Nat := 163655413132895289384245

theorem tailTrace_1434230 : CollatzResearch.WordTrace tailWord_1434230 prefixEnd_1434230 163655413132895289384245 := by
  unfold tailWord_1434230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269416599627320739242759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34873777062691421218589429 3269416599627320739242759)
  ·
    refine ⟨4904124899440981108864139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269416599627320739242759 4904124899440981108864139)
    ·
      refine ⟨7356187349161471663296209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4904124899440981108864139 7356187349161471663296209)
      ·
        refine ⟨5517140511871103747472157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7356187349161471663296209 5517140511871103747472157)
        ·
          refine ⟨2068927691951663905302059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5517140511871103747472157 2068927691951663905302059)
          ·
            refine ⟨3103391537927495857953089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068927691951663905302059 3103391537927495857953089)
            ·
              refine ⟨2327543653445621893464817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3103391537927495857953089 2327543653445621893464817)
              ·
                refine ⟨1745657740084216420098613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327543653445621893464817 1745657740084216420098613)
                ·
                  refine ⟨163655413132895289384245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1745657740084216420098613 163655413132895289384245)
                  ·
                    rfl

theorem cell22_1434230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1434230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434230 prefixEnd_1434230 := by exact prefixLift 1434230
  have htrace : WordTrace (prefixWord ++ tailWord_1434230) baseStart_1434230 baseEnd_1434230 := by
    simpa [prefixWord, tailWord_1434230, baseEnd_1434230] using wordTrace_append hprefix tailTrace_1434230
  have hstable : (prefixWord ++ tailWord_1434230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434230).length < 2 ^ (prefixWord ++ tailWord_1434230).sum := by decide
  have hdescent : baseEnd_1434230 < baseStart_1434230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434241 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 6]
def baseStart_1434241 : Nat := 118140960795 + 1434241 * 2 ^ 59
def prefixEnd_1434241 : Nat := 4983230072969 + 3 ^ 40 * 1434241 * 2
def baseEnd_1434241 : Nat := 163656668307828502042567

theorem tailTrace_1434241 : CollatzResearch.WordTrace tailWord_1434241 prefixEnd_1434241 163656668307828502042567 := by
  unfold tailWord_1434241
  simp only [CollatzResearch.WordTrace]
  refine ⟨52311066796997280706534577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34874044531331520471023051 52311066796997280706534577)
  ·
    refine ⟨39233300097747960529900933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52311066796997280706534577 39233300097747960529900933)
    ·
      refine ⟨7356243768327742599356425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39233300097747960529900933 7356243768327742599356425)
      ·
        refine ⟨5517182826245806949517319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7356243768327742599356425 5517182826245806949517319)
        ·
          refine ⟨8275774239368710424275979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517182826245806949517319 8275774239368710424275979)
          ·
            refine ⟨12413661359053065636413969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275774239368710424275979 12413661359053065636413969)
            ·
              refine ⟨9310246019289799227310477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12413661359053065636413969 9310246019289799227310477)
              ·
                refine ⟨3491342257233674710241429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9310246019289799227310477 3491342257233674710241429)
                ·
                  refine ⟨163656668307828502042567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3491342257233674710241429 163656668307828502042567)
                  ·
                    rfl

theorem cell22_1434241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_1434241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434241 prefixEnd_1434241 := by exact prefixLift 1434241
  have htrace : WordTrace (prefixWord ++ tailWord_1434241) baseStart_1434241 baseEnd_1434241 := by
    simpa [prefixWord, tailWord_1434241, baseEnd_1434241] using wordTrace_append hprefix tailTrace_1434241
  have hstable : (prefixWord ++ tailWord_1434241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434241).length < 2 ^ (prefixWord ++ tailWord_1434241).sum := by decide
  have hdescent : baseEnd_1434241 < baseStart_1434241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434256 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_1434256 : Nat := 118140960795 + 1434256 * 2 ^ 59
def prefixEnd_1434256 : Nat := 4983230072969 + 3 ^ 40 * 1434256 * 2
def baseEnd_1434256 : Nat := 490975139730030467002655

theorem tailTrace_1434256 : CollatzResearch.WordTrace tailWord_1434256 prefixEnd_1434256 490975139730030467002655 := by
  unfold tailWord_1434256
  simp only [CollatzResearch.WordTrace]
  refine ⟨26155806945971469134165311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34874409261295292178887081 26155806945971469134165311)
  ·
    refine ⟨39233710418957203701247967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26155806945971469134165311 39233710418957203701247967)
    ·
      refine ⟨58850565628435805551871951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39233710418957203701247967 58850565628435805551871951)
      ·
        refine ⟨88275848442653708327807927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58850565628435805551871951 88275848442653708327807927)
        ·
          refine ⟨132413772663980562491711891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88275848442653708327807927 132413772663980562491711891)
          ·
            refine ⟨198620658995970843737567837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132413772663980562491711891 198620658995970843737567837)
            ·
              refine ⟨74482747123489066401587939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198620658995970843737567837 74482747123489066401587939)
              ·
                refine ⟨111724120685233599602381909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74482747123489066401587939 111724120685233599602381909)
                ·
                  refine ⟨1309267039280081245340413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 111724120685233599602381909 1309267039280081245340413)
                  ·
                    refine ⟨490975139730030467002655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309267039280081245340413 490975139730030467002655)
                    ·
                      rfl

theorem cell22_1434256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_1434256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434256 prefixEnd_1434256 := by exact prefixLift 1434256
  have htrace : WordTrace (prefixWord ++ tailWord_1434256) baseStart_1434256 baseEnd_1434256 := by
    simpa [prefixWord, tailWord_1434256, baseEnd_1434256] using wordTrace_append hprefix tailTrace_1434256
  have hstable : (prefixWord ++ tailWord_1434256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434256).length < 2 ^ (prefixWord ++ tailWord_1434256).sum := by decide
  have hdescent : baseEnd_1434256 < baseStart_1434256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434258 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_1434258 : Nat := 118140960795 + 1434258 * 2 ^ 59
def prefixEnd_1434258 : Nat := 4983230072969 + 3 ^ 40 * 1434258 * 2
def baseEnd_1434258 : Nat := 163658608123634376150883

theorem tailTrace_1434258 : CollatzResearch.WordTrace tailWord_1434258 prefixEnd_1434258 163658608123634376150883 := by
  unfold tailWord_1434258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13077921709483923152475857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34874457891957128406602285 13077921709483923152475857)
  ·
    refine ⟨9808441282112942364356893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13077921709483923152475857 9808441282112942364356893)
    ·
      refine ⟨3678165480792353386633835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9808441282112942364356893 3678165480792353386633835)
      ·
        refine ⟨5517248221188530079950753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678165480792353386633835 5517248221188530079950753)
        ·
          refine ⟨4137936165891397559963065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5517248221188530079950753 4137936165891397559963065)
          ·
            refine ⟨3103452124418548169972299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4137936165891397559963065 3103452124418548169972299)
            ·
              refine ⟨4655178186627822254958449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103452124418548169972299 4655178186627822254958449)
              ·
                refine ⟨3491383639970866691218837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655178186627822254958449 3491383639970866691218837)
                ·
                  refine ⟨163658608123634376150883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3491383639970866691218837 163658608123634376150883)
                  ·
                    rfl

theorem cell22_1434258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_1434258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434258 prefixEnd_1434258 := by exact prefixLift 1434258
  have htrace : WordTrace (prefixWord ++ tailWord_1434258) baseStart_1434258 baseEnd_1434258 := by
    simpa [prefixWord, tailWord_1434258, baseEnd_1434258] using wordTrace_append hprefix tailTrace_1434258
  have hstable : (prefixWord ++ tailWord_1434258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434258).length < 2 ^ (prefixWord ++ tailWord_1434258).sum := by decide
  have hdescent : baseEnd_1434258 < baseStart_1434258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434352 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 1, 3]
def baseStart_1434352 : Nat := 118140960795 + 1434352 * 2 ^ 59
def prefixEnd_1434352 : Nat := 4983230072969 + 3 ^ 40 * 1434352 * 2
def baseEnd_1434352 : Nat := 491008002491918216602361

theorem tailTrace_1434352 : CollatzResearch.WordTrace tailWord_1434352 prefixEnd_1434352 491008002491918216602361 := by
  unfold tailWord_1434352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26157557649797573331912655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34876743533063431109216873 26157557649797573331912655)
  ·
    refine ⟨39236336474696359997868983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26157557649797573331912655 39236336474696359997868983)
    ·
      refine ⟨58854504712044539996803475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39236336474696359997868983 58854504712044539996803475)
      ·
        refine ⟨88281757068066809995205213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58854504712044539996803475 88281757068066809995205213)
        ·
          refine ⟨33105658900525053748201955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88281757068066809995205213 33105658900525053748201955)
          ·
            refine ⟨49658488350787580622302933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33105658900525053748201955 49658488350787580622302933)
            ·
              refine ⟨1163870820721583920835225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49658488350787580622302933 1163870820721583920835225)
              ·
                refine ⟨872903115541187940626419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163870820721583920835225 872903115541187940626419)
                ·
                  refine ⟨1309354673311781910939629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872903115541187940626419 1309354673311781910939629)
                  ·
                    refine ⟨491008002491918216602361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309354673311781910939629 491008002491918216602361)
                    ·
                      rfl

theorem cell22_1434352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_1434352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434352 prefixEnd_1434352 := by exact prefixLift 1434352
  have htrace : WordTrace (prefixWord ++ tailWord_1434352) baseStart_1434352 baseEnd_1434352 := by
    simpa [prefixWord, tailWord_1434352, baseEnd_1434352] using wordTrace_append hprefix tailTrace_1434352
  have hstable : (prefixWord ++ tailWord_1434352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434352).length < 2 ^ (prefixWord ++ tailWord_1434352).sum := by decide
  have hdescent : baseEnd_1434352 < baseStart_1434352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434378 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1434378 : Nat := 118140960795 + 1434378 * 2 ^ 59
def prefixEnd_1434378 : Nat := 4983230072969 + 3 ^ 40 * 1434378 * 2
def baseEnd_1434378 : Nat := 491016902823262815452281

theorem tailTrace_1434378 : CollatzResearch.WordTrace tailWord_1434378 prefixEnd_1434378 491016902823262815452281 := by
  unfold tailWord_1434378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13079015899375238276067947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34877375731667302069514525 13079015899375238276067947)
  ·
    refine ⟨19618523849062857414101921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13079015899375238276067947 19618523849062857414101921)
    ·
      refine ⟨14713892886797143060576441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19618523849062857414101921 14713892886797143060576441)
      ·
        refine ⟨11035419665097857295432331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14713892886797143060576441 11035419665097857295432331)
        ·
          refine ⟨16553129497646785943148497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11035419665097857295432331 16553129497646785943148497)
          ·
            refine ⟨12414847123235089457361373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16553129497646785943148497 12414847123235089457361373)
            ·
              refine ⟨4655567671213158546510515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12414847123235089457361373 4655567671213158546510515)
              ·
                refine ⟨6983351506819737819765773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655567671213158546510515 6983351506819737819765773)
                ·
                  refine ⟨2618756815057401682412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6983351506819737819765773 2618756815057401682412165)
                  ·
                    refine ⟨491016902823262815452281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618756815057401682412165 491016902823262815452281)
                    ·
                      rfl

theorem cell22_1434378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1434378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434378 prefixEnd_1434378 := by exact prefixLift 1434378
  have htrace : WordTrace (prefixWord ++ tailWord_1434378) baseStart_1434378 baseEnd_1434378 := by
    simpa [prefixWord, tailWord_1434378, baseEnd_1434378] using wordTrace_append hprefix tailTrace_1434378
  have hstable : (prefixWord ++ tailWord_1434378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434378).length < 2 ^ (prefixWord ++ tailWord_1434378).sum := by decide
  have hdescent : baseEnd_1434378 < baseStart_1434378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434408 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1434408 : Nat := 118140960795 + 1434408 * 2 ^ 59
def prefixEnd_1434408 : Nat := 4983230072969 + 3 ^ 40 * 1434408 * 2
def baseEnd_1434408 : Nat := 491027172436352737202189

theorem tailTrace_1434408 : CollatzResearch.WordTrace tailWord_1434408 prefixEnd_1434408 491027172436352737202189 := by
  unfold tailWord_1434408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158578893696134113931939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34878105191594845485242585 26158578893696134113931939)
  ·
    refine ⟨39237868340544201170897909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26158578893696134113931939 39237868340544201170897909)
    ·
      refine ⟨3678550156926018859771679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39237868340544201170897909 3678550156926018859771679)
      ·
        refine ⟨5517825235389028289657519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678550156926018859771679 5517825235389028289657519)
        ·
          refine ⟨8276737853083542434486279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517825235389028289657519 8276737853083542434486279)
          ·
            refine ⟨12415106779625313651729419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8276737853083542434486279 12415106779625313651729419)
            ·
              refine ⟨18622660169437970477594129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415106779625313651729419 18622660169437970477594129)
              ·
                refine ⟨13966995127078477858195597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18622660169437970477594129 13966995127078477858195597)
                ·
                  refine ⟨5237623172654429196823349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13966995127078477858195597 5237623172654429196823349)
                  ·
                    refine ⟨491027172436352737202189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5237623172654429196823349 491027172436352737202189)
                    ·
                      rfl

theorem cell22_1434408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1434408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434408 prefixEnd_1434408 := by exact prefixLift 1434408
  have htrace : WordTrace (prefixWord ++ tailWord_1434408) baseStart_1434408 baseEnd_1434408 := by
    simpa [prefixWord, tailWord_1434408, baseEnd_1434408] using wordTrace_append hprefix tailTrace_1434408
  have hstable : (prefixWord ++ tailWord_1434408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434408).length < 2 ^ (prefixWord ++ tailWord_1434408).sum := by decide
  have hdescent : baseEnd_1434408 < baseStart_1434408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434483 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 5]
def baseStart_1434483 : Nat := 118140960795 + 1434483 * 2 ^ 59
def prefixEnd_1434483 : Nat := 4983230072969 + 3 ^ 40 * 1434483 * 2
def baseEnd_1434483 : Nat := 163684282156359180525653

theorem tailTrace_1434483 : CollatzResearch.WordTrace tailWord_1434483 prefixEnd_1434483 163684282156359180525653 := by
  unfold tailWord_1434483
  simp only [CollatzResearch.WordTrace]
  refine ⟨52319893262120556036844103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34879928841413704024562735 52319893262120556036844103)
  ·
    refine ⟨78479839893180834055266155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52319893262120556036844103 78479839893180834055266155)
    ·
      refine ⟨117719759839771251082899233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78479839893180834055266155 117719759839771251082899233)
      ·
        refine ⟨88289819879828438312174425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117719759839771251082899233 88289819879828438312174425)
        ·
          refine ⟨66217364909871328734130819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88289819879828438312174425 66217364909871328734130819)
          ·
            refine ⟨99326047364806993101196229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66217364909871328734130819 99326047364806993101196229)
            ·
              refine ⟨18623633880901311206474293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99326047364806993101196229 18623633880901311206474293)
              ·
                refine ⟨1745965676334497925606965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18623633880901311206474293 1745965676334497925606965)
                ·
                  refine ⟨163684282156359180525653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1745965676334497925606965 163684282156359180525653)
                  ·
                    rfl

theorem cell22_1434483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 5].length) (baseStart_1434483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434483 prefixEnd_1434483 := by exact prefixLift 1434483
  have htrace : WordTrace (prefixWord ++ tailWord_1434483) baseStart_1434483 baseEnd_1434483 := by
    simpa [prefixWord, tailWord_1434483, baseEnd_1434483] using wordTrace_append hprefix tailTrace_1434483
  have hstable : (prefixWord ++ tailWord_1434483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434483).length < 2 ^ (prefixWord ++ tailWord_1434483).sum := by decide
  have hdescent : baseEnd_1434483 < baseStart_1434483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434504 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 1, 3]
def baseStart_1434504 : Nat := 118140960795 + 1434504 * 2 ^ 59
def prefixEnd_1434504 : Nat := 4983230072969 + 3 ^ 40 * 1434504 * 2
def baseEnd_1434504 : Nat := 491060035198240486801895

theorem tailTrace_1434504 : CollatzResearch.WordTrace tailWord_1434504 prefixEnd_1434504 491060035198240486801895 := by
  unfold tailWord_1434504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26160329597522238311679283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34880439463362984415572377 26160329597522238311679283)
  ·
    refine ⟨39240494396283357467518925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26160329597522238311679283 39240494396283357467518925)
    ·
      refine ⟨14715185398606259050319597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39240494396283357467518925 14715185398606259050319597)
      ·
        refine ⟨5518194524477347143869849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14715185398606259050319597 5518194524477347143869849)
        ·
          refine ⟨4138645893358010357902387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5518194524477347143869849 4138645893358010357902387)
          ·
            refine ⟨6207968840037015536853581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138645893358010357902387 6207968840037015536853581)
            ·
              refine ⟨2327988315013880826320093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6207968840037015536853581 2327988315013880826320093)
              ·
                refine ⟨872995618130205309870035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2327988315013880826320093 872995618130205309870035)
                ·
                  refine ⟨1309493427195307964805053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872995618130205309870035 1309493427195307964805053)
                  ·
                    refine ⟨491060035198240486801895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309493427195307964805053 491060035198240486801895)
                    ·
                      rfl

theorem cell22_1434504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_1434504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434504 prefixEnd_1434504 := by exact prefixLift 1434504
  have htrace : WordTrace (prefixWord ++ tailWord_1434504) baseStart_1434504 baseEnd_1434504 := by
    simpa [prefixWord, tailWord_1434504, baseEnd_1434504] using wordTrace_append hprefix tailTrace_1434504
  have hstable : (prefixWord ++ tailWord_1434504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434504).length < 2 ^ (prefixWord ++ tailWord_1434504).sum := by decide
  have hdescent : baseEnd_1434504 < baseStart_1434504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_1434513 : Nat := 118140960795 + 1434513 * 2 ^ 59
def prefixEnd_1434513 : Nat := 4983230072969 + 3 ^ 40 * 1434513 * 2
def baseEnd_1434513 : Nat := 491063116082167463326867

theorem tailTrace_1434513 : CollatzResearch.WordTrace tailWord_1434513 prefixEnd_1434513 491063116082167463326867 := by
  unfold tailWord_1434513
  simp only [CollatzResearch.WordTrace]
  refine ⟨52320987452011871160436193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34880658301341247440290795 52320987452011871160436193)
  ·
    refine ⟨39240740589008903370327145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52320987452011871160436193 39240740589008903370327145)
    ·
      refine ⟨29430555441756677527745359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39240740589008903370327145 29430555441756677527745359)
      ·
        refine ⟨44145833162635016291618039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29430555441756677527745359 44145833162635016291618039)
        ·
          refine ⟨66218749743952524437427059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44145833162635016291618039 66218749743952524437427059)
          ·
            refine ⟨99328124615928786656140589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66218749743952524437427059 99328124615928786656140589)
            ·
              refine ⟨37248046730973294996052721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99328124615928786656140589 37248046730973294996052721)
              ·
                refine ⟨27936035048229971247039541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37248046730973294996052721 27936035048229971247039541)
                ·
                  refine ⟨2619003285771559804409957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27936035048229971247039541 2619003285771559804409957)
                  ·
                    refine ⟨491063116082167463326867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619003285771559804409957 491063116082167463326867)
                    ·
                      rfl

theorem cell22_1434513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_1434513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434513 prefixEnd_1434513 := by exact prefixLift 1434513
  have htrace : WordTrace (prefixWord ++ tailWord_1434513) baseStart_1434513 baseEnd_1434513 := by
    simpa [prefixWord, tailWord_1434513, baseEnd_1434513] using wordTrace_append hprefix tailTrace_1434513
  have hstable : (prefixWord ++ tailWord_1434513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434513).length < 2 ^ (prefixWord ++ tailWord_1434513).sum := by decide
  have hdescent : baseEnd_1434513 < baseStart_1434513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434560 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_1434560 : Nat := 118140960795 + 1434560 * 2 ^ 59
def prefixEnd_1434560 : Nat := 4983230072969 + 3 ^ 40 * 1434560 * 2
def baseEnd_1434560 : Nat := 491079205142675007401723

theorem tailTrace_1434560 : CollatzResearch.WordTrace tailWord_1434560 prefixEnd_1434560 491079205142675007401723 := by
  unfold tailWord_1434560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26161350841420799093698567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34881801121894398791598089 26161350841420799093698567)
  ·
    refine ⟨39242026262131198640547851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26161350841420799093698567 39242026262131198640547851)
    ·
      refine ⟨58863039393196797960821777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39242026262131198640547851 58863039393196797960821777)
      ·
        refine ⟨44147279544897598470616333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58863039393196797960821777 44147279544897598470616333)
        ·
          refine ⟨16555229829336599426481125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44147279544897598470616333 16555229829336599426481125)
          ·
            refine ⟨3104105593000612392465211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16555229829336599426481125 3104105593000612392465211)
            ·
              refine ⟨4656158389500918588697817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104105593000612392465211 4656158389500918588697817)
              ·
                refine ⟨3492118792125688941523363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4656158389500918588697817 3492118792125688941523363)
                ·
                  refine ⟨5238178188188533412285045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492118792125688941523363 5238178188188533412285045)
                  ·
                    refine ⟨491079205142675007401723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5238178188188533412285045 491079205142675007401723)
                    ·
                      rfl

theorem cell22_1434560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_1434560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434560 prefixEnd_1434560 := by exact prefixLift 1434560
  have htrace : WordTrace (prefixWord ++ tailWord_1434560) baseStart_1434560 baseEnd_1434560 := by
    simpa [prefixWord, tailWord_1434560, baseEnd_1434560] using wordTrace_append hprefix tailTrace_1434560
  have hstable : (prefixWord ++ tailWord_1434560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434560).length < 2 ^ (prefixWord ++ tailWord_1434560).sum := by decide
  have hdescent : baseEnd_1434560 < baseStart_1434560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434575 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_1434575 : Nat := 118140960795 + 1434575 * 2 ^ 59
def prefixEnd_1434575 : Nat := 4983230072969 + 3 ^ 40 * 1434575 * 2
def baseEnd_1434575 : Nat := 491084339949219968276677

theorem tailTrace_1434575 : CollatzResearch.WordTrace tailWord_1434575 prefixEnd_1434575 491084339949219968276677 := by
  unfold tailWord_1434575
  simp only [CollatzResearch.WordTrace]
  refine ⟨52323248777787255749193179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34882165851858170499462119 52323248777787255749193179)
  ·
    refine ⟨78484873166680883623789769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52323248777787255749193179 78484873166680883623789769)
    ·
      refine ⟨58863654875010662717842327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78484873166680883623789769 58863654875010662717842327)
      ·
        refine ⟨88295482312515994076763491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58863654875010662717842327 88295482312515994076763491)
        ·
          refine ⟨132443223468773991115145237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88295482312515994076763491 132443223468773991115145237)
          ·
            refine ⟨6208276100098780833522433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132443223468773991115145237 6208276100098780833522433)
            ·
              refine ⟨4656207075074085625141825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6208276100098780833522433 4656207075074085625141825)
              ·
                refine ⟨3492155306305564218856369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4656207075074085625141825 3492155306305564218856369)
                ·
                  refine ⟨2619116479729173164142277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492155306305564218856369 2619116479729173164142277)
                  ·
                    refine ⟨491084339949219968276677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619116479729173164142277 491084339949219968276677)
                    ·
                      rfl

theorem cell22_1434575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_1434575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434575 prefixEnd_1434575 := by exact prefixLift 1434575
  have htrace : WordTrace (prefixWord ++ tailWord_1434575) baseStart_1434575 baseEnd_1434575 := by
    simpa [prefixWord, tailWord_1434575, baseEnd_1434575] using wordTrace_append hprefix tailTrace_1434575
  have hstable : (prefixWord ++ tailWord_1434575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434575).length < 2 ^ (prefixWord ++ tailWord_1434575).sum := by decide
  have hdescent : baseEnd_1434575 < baseStart_1434575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434577 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_1434577 : Nat := 118140960795 + 1434577 * 2 ^ 59
def prefixEnd_1434577 : Nat := 4983230072969 + 3 ^ 40 * 1434577 * 2
def baseEnd_1434577 : Nat := 491085024590092629726671

theorem tailTrace_1434577 : CollatzResearch.WordTrace tailWord_1434577 prefixEnd_1434577 491085024590092629726671 := by
  unfold tailWord_1434577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52323321723780010090765985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34882214482520006727177323 52323321723780010090765985)
  ·
    refine ⟨39242491292835007568074489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52323321723780010090765985 39242491292835007568074489)
    ·
      refine ⟨29431868469626255676055867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39242491292835007568074489 29431868469626255676055867)
      ·
        refine ⟨44147802704439383514083801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29431868469626255676055867 44147802704439383514083801)
        ·
          refine ⟨33110852028329537635562851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44147802704439383514083801 33110852028329537635562851)
          ·
            refine ⟨49666278042494306453344277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33110852028329537635562851 49666278042494306453344277)
            ·
              refine ⟨2328106783241920615000513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49666278042494306453344277 2328106783241920615000513)
              ·
                refine ⟨1746080087431440461250385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328106783241920615000513 1746080087431440461250385)
                ·
                  refine ⟨1309560065573580345937789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746080087431440461250385 1309560065573580345937789)
                  ·
                    refine ⟨491085024590092629726671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309560065573580345937789 491085024590092629726671)
                    ·
                      rfl

theorem cell22_1434577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_1434577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434577 prefixEnd_1434577 := by exact prefixLift 1434577
  have htrace : WordTrace (prefixWord ++ tailWord_1434577) baseStart_1434577 baseEnd_1434577 := by
    simpa [prefixWord, tailWord_1434577, baseEnd_1434577] using wordTrace_append hprefix tailTrace_1434577
  have hstable : (prefixWord ++ tailWord_1434577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434577).length < 2 ^ (prefixWord ++ tailWord_1434577).sum := by decide
  have hdescent : baseEnd_1434577 < baseStart_1434577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434594 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1434594 : Nat := 118140960795 + 1434594 * 2 ^ 59
def prefixEnd_1434594 : Nat := 4983230072969 + 3 ^ 40 * 1434594 * 2
def baseEnd_1434594 : Nat := 491090844037510252051619

theorem tailTrace_1434594 : CollatzResearch.WordTrace tailWord_1434594 prefixEnd_1434594 491090844037510252051619 := by
  unfold tailWord_1434594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13080985441179605498533709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34882627843145614662756557 13080985441179605498533709)
  ·
    refine ⟨4905369540442352061950141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13080985441179605498533709 4905369540442352061950141)
    ·
      refine ⟨1839513577665882023231303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4905369540442352061950141 1839513577665882023231303)
      ·
        refine ⟨2759270366498823034846955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839513577665882023231303 2759270366498823034846955)
        ·
          refine ⟨4138905549748234552270433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759270366498823034846955 4138905549748234552270433)
          ·
            refine ⟨3104179162311175914202825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4138905549748234552270433 3104179162311175914202825)
            ·
              refine ⟨2328134371733381935652119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104179162311175914202825 2328134371733381935652119)
              ·
                refine ⟨3492201557600072903478179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328134371733381935652119 3492201557600072903478179)
                ·
                  refine ⟨5238302336400109355217269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492201557600072903478179 5238302336400109355217269)
                  ·
                    refine ⟨491090844037510252051619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5238302336400109355217269 491090844037510252051619)
                    ·
                      rfl

theorem cell22_1434594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1434594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434594 prefixEnd_1434594 := by exact prefixLift 1434594
  have htrace : WordTrace (prefixWord ++ tailWord_1434594) baseStart_1434594 baseEnd_1434594 := by
    simpa [prefixWord, tailWord_1434594, baseEnd_1434594] using wordTrace_append hprefix tailTrace_1434594
  have hstable : (prefixWord ++ tailWord_1434594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434594).length < 2 ^ (prefixWord ++ tailWord_1434594).sum := by decide
  have hdescent : baseEnd_1434594 < baseStart_1434594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434635 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 7]
def baseStart_1434635 : Nat := 118140960795 + 1434635 * 2 ^ 59
def prefixEnd_1434635 : Nat := 4983230072969 + 3 ^ 40 * 1434635 * 2
def baseEnd_1434635 : Nat := 163701626391799937258831

theorem tailTrace_1434635 : CollatzResearch.WordTrace tailWord_1434635 prefixEnd_1434635 163701626391799937258831 := by
  unfold tailWord_1434635
  simp only [CollatzResearch.WordTrace]
  refine ⟨52325437157569885996377359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34883624771713257330918239 52325437157569885996377359)
  ·
    refine ⟨78488155736354828994566039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52325437157569885996377359 78488155736354828994566039)
    ·
      refine ⟨117732233604532243491849059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78488155736354828994566039 117732233604532243491849059)
      ·
        refine ⟨176598350406798365237773589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117732233604532243491849059 176598350406798365237773589)
        ·
          refine ⟨8278047675318673370520637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176598350406798365237773589 8278047675318673370520637)
          ·
            refine ⟨3104267878244502513945239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8278047675318673370520637 3104267878244502513945239)
            ·
              refine ⟨4656401817366753770917859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104267878244502513945239 4656401817366753770917859)
              ·
                refine ⟨6984602726050130656376789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656401817366753770917859 6984602726050130656376789)
                ·
                  refine ⟨163701626391799937258831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6984602726050130656376789 163701626391799937258831)
                  ·
                    rfl

theorem cell22_1434635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_1434635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434635 prefixEnd_1434635 := by exact prefixLift 1434635
  have htrace : WordTrace (prefixWord ++ tailWord_1434635) baseStart_1434635 baseEnd_1434635 := by
    simpa [prefixWord, tailWord_1434635, baseEnd_1434635] using wordTrace_append hprefix tailTrace_1434635
  have hstable : (prefixWord ++ tailWord_1434635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434635).length < 2 ^ (prefixWord ++ tailWord_1434635).sum := by decide
  have hdescent : baseEnd_1434635 < baseStart_1434635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434650 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_1434650 : Nat := 118140960795 + 1434650 * 2 ^ 59
def prefixEnd_1434650 : Nat := 4983230072969 + 3 ^ 40 * 1434650 * 2
def baseEnd_1434650 : Nat := 491110013981944772651447

theorem tailTrace_1434650 : CollatzResearch.WordTrace tailWord_1434650 prefixEnd_1434650 491110013981944772651447 := by
  unfold tailWord_1434650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081496063128885889543351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34883989501677029038782269 13081496063128885889543351)
  ·
    refine ⟨19622244094693328834315027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081496063128885889543351 19622244094693328834315027)
    ·
      refine ⟨29433366142039993251472541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622244094693328834315027 29433366142039993251472541)
      ·
        refine ⟨11037512303264997469302203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29433366142039993251472541 11037512303264997469302203)
        ·
          refine ⟨16556268454897496203953305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11037512303264997469302203 16556268454897496203953305)
          ·
            refine ⟨12417201341173122152964979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16556268454897496203953305 12417201341173122152964979)
            ·
              refine ⟨18625802011759683229447469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417201341173122152964979 18625802011759683229447469)
              ·
                refine ⟨6984675754409881211042801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18625802011759683229447469 6984675754409881211042801)
                ·
                  refine ⟨5238506815807410908282101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6984675754409881211042801 5238506815807410908282101)
                  ·
                    refine ⟨491110013981944772651447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5238506815807410908282101 491110013981944772651447)
                    ·
                      rfl

theorem cell22_1434650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_1434650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434650 prefixEnd_1434650 := by exact prefixLift 1434650
  have htrace : WordTrace (prefixWord ++ tailWord_1434650) baseStart_1434650 baseEnd_1434650 := by
    simpa [prefixWord, tailWord_1434650, baseEnd_1434650] using wordTrace_append hprefix tailTrace_1434650
  have hstable : (prefixWord ++ tailWord_1434650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434650).length < 2 ^ (prefixWord ++ tailWord_1434650).sum := by decide
  have hdescent : baseEnd_1434650 < baseStart_1434650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434682 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_1434682 : Nat := 118140960795 + 1434682 * 2 ^ 59
def prefixEnd_1434682 : Nat := 4983230072969 + 3 ^ 40 * 1434682 * 2
def baseEnd_1434682 : Nat := 491120968235907355851349

theorem tailTrace_1434682 : CollatzResearch.WordTrace tailWord_1434682 prefixEnd_1434682 491120968235907355851349 := by
  unfold tailWord_1434682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081787847099903255834575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34884767592266408682225533 13081787847099903255834575)
  ·
    refine ⟨19622681770649854883751863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081787847099903255834575 19622681770649854883751863)
    ·
      refine ⟨29434022655974782325627795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622681770649854883751863 29434022655974782325627795)
      ·
        refine ⟨44151033983962173488441693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29434022655974782325627795 44151033983962173488441693)
        ·
          refine ⟨16556637743985815058165635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44151033983962173488441693 16556637743985815058165635)
          ·
            refine ⟨24834956615978722587248453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16556637743985815058165635 24834956615978722587248453)
            ·
              refine ⟨4656554365496010485109085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24834956615978722587248453 4656554365496010485109085)
              ·
                refine ⟨1746207887061003931915907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4656554365496010485109085 1746207887061003931915907)
                ·
                  refine ⟨2619311830591505897873861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746207887061003931915907 2619311830591505897873861)
                  ·
                    refine ⟨491120968235907355851349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619311830591505897873861 491120968235907355851349)
                    ·
                      rfl

theorem cell22_1434682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_1434682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434682 prefixEnd_1434682 := by exact prefixLift 1434682
  have htrace : WordTrace (prefixWord ++ tailWord_1434682) baseStart_1434682 baseEnd_1434682 := by
    simpa [prefixWord, tailWord_1434682, baseEnd_1434682] using wordTrace_append hprefix tailTrace_1434682
  have hstable : (prefixWord ++ tailWord_1434682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434682).length < 2 ^ (prefixWord ++ tailWord_1434682).sum := by decide
  have hdescent : baseEnd_1434682 < baseStart_1434682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434725 : List Nat := [1, 3, 1, 3, 2, 1, 1, 10]
def baseStart_1434725 : Nat := 118140960795 + 1434725 * 2 ^ 59
def prefixEnd_1434725 : Nat := 4983230072969 + 3 ^ 40 * 1434725 * 2
def baseEnd_1434725 : Nat := 54570632001629953002913

theorem tailTrace_1434725 : CollatzResearch.WordTrace tailWord_1434725 prefixEnd_1434725 54570632001629953002913 := by
  unfold tailWord_1434725
  simp only [CollatzResearch.WordTrace]
  refine ⟨52328719727243831367153629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34885813151495887578102419 52328719727243831367153629)
  ·
    refine ⟨19623269897716436762682611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52328719727243831367153629 19623269897716436762682611)
    ·
      refine ⟨29434904846574655144023917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19623269897716436762682611 29434904846574655144023917)
      ·
        refine ⟨11038089317465495679008969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29434904846574655144023917 11038089317465495679008969)
        ·
          refine ⟨8278566988099121759256727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11038089317465495679008969 8278566988099121759256727)
          ·
            refine ⟨12417850482148682638885091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278566988099121759256727 12417850482148682638885091)
            ·
              refine ⟨18626775723223023958327637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417850482148682638885091 18626775723223023958327637)
              ·
                refine ⟨54570632001629953002913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18626775723223023958327637 54570632001629953002913)
                ·
                  rfl

theorem cell22_1434725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 10].length) (baseStart_1434725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434725 prefixEnd_1434725 := by exact prefixLift 1434725
  have htrace : WordTrace (prefixWord ++ tailWord_1434725) baseStart_1434725 baseEnd_1434725 := by
    simpa [prefixWord, tailWord_1434725, baseEnd_1434725] using wordTrace_append hprefix tailTrace_1434725
  have hstable : (prefixWord ++ tailWord_1434725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434725).length < 2 ^ (prefixWord ++ tailWord_1434725).sum := by decide
  have hdescent : baseEnd_1434725 < baseStart_1434725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434727 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1434727 : Nat := 118140960795 + 1434727 * 2 ^ 59
def prefixEnd_1434727 : Nat := 4983230072969 + 3 ^ 40 * 1434727 * 2
def baseEnd_1434727 : Nat := 491136372655542238476211

theorem tailTrace_1434727 : CollatzResearch.WordTrace tailWord_1434727 prefixEnd_1434727 491136372655542238476211 := by
  unfold tailWord_1434727
  simp only [CollatzResearch.WordTrace]
  refine ⟨52328792673236585708726435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34885861782157723805817623 52328792673236585708726435)
  ·
    refine ⟨78493189009854878563089653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52328792673236585708726435 78493189009854878563089653)
    ·
      refine ⟨7358736469673894865289655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78493189009854878563089653 7358736469673894865289655)
      ·
        refine ⟨11038104704510842297934483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7358736469673894865289655 11038104704510842297934483)
        ·
          refine ⟨16557157056766263446901725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11038104704510842297934483 16557157056766263446901725)
          ·
            refine ⟨6208933896287348792588147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16557157056766263446901725 6208933896287348792588147)
            ·
              refine ⟨9313400844431023188882221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208933896287348792588147 9313400844431023188882221)
              ·
                refine ⟨3492525316661633695830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9313400844431023188882221 3492525316661633695830833)
                ·
                  refine ⟨2619393987496225271873125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492525316661633695830833 2619393987496225271873125)
                  ·
                    refine ⟨491136372655542238476211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619393987496225271873125 491136372655542238476211)
                    ·
                      rfl

theorem cell22_1434727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1434727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434727 prefixEnd_1434727 := by exact prefixLift 1434727
  have htrace : WordTrace (prefixWord ++ tailWord_1434727) baseStart_1434727 baseEnd_1434727 := by
    simpa [prefixWord, tailWord_1434727, baseEnd_1434727] using wordTrace_append hprefix tailTrace_1434727
  have hstable : (prefixWord ++ tailWord_1434727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434727).length < 2 ^ (prefixWord ++ tailWord_1434727).sum := by decide
  have hdescent : baseEnd_1434727 < baseStart_1434727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434755 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_1434755 : Nat := 118140960795 + 1434755 * 2 ^ 59
def prefixEnd_1434755 : Nat := 4983230072969 + 3 ^ 40 * 1434755 * 2
def baseEnd_1434755 : Nat := 491145957627759498776125

theorem tailTrace_1434755 : CollatzResearch.WordTrace tailWord_1434755 prefixEnd_1434755 491145957627759498776125 := by
  unfold tailWord_1434755
  simp only [CollatzResearch.WordTrace]
  refine ⟨52329813917135146490745719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34886542611423430993830479 52329813917135146490745719)
  ·
    refine ⟨78494720875702719736118579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52329813917135146490745719 78494720875702719736118579)
    ·
      refine ⟨117742081313554079604177869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78494720875702719736118579 117742081313554079604177869)
      ·
        refine ⟨44153280492582779851566701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117742081313554079604177869 44153280492582779851566701)
        ·
          refine ⟨16557480184718542444337513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44153280492582779851566701 16557480184718542444337513)
          ·
            refine ⟨12418110138538906833253135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16557480184718542444337513 12418110138538906833253135)
            ·
              refine ⟨18627165207808360249879703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418110138538906833253135 18627165207808360249879703)
              ·
                refine ⟨27940747811712540374819555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18627165207808360249879703 27940747811712540374819555)
                ·
                  refine ⟨41911121717568810562229333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27940747811712540374819555 41911121717568810562229333)
                  ·
                    refine ⟨491145957627759498776125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41911121717568810562229333 491145957627759498776125)
                    ·
                      rfl

theorem cell22_1434755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_1434755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434755 prefixEnd_1434755 := by exact prefixLift 1434755
  have htrace : WordTrace (prefixWord ++ tailWord_1434755) baseStart_1434755 baseEnd_1434755 := by
    simpa [prefixWord, tailWord_1434755, baseEnd_1434755] using wordTrace_append hprefix tailTrace_1434755
  have hstable : (prefixWord ++ tailWord_1434755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434755).length < 2 ^ (prefixWord ++ tailWord_1434755).sum := by decide
  have hdescent : baseEnd_1434755 < baseStart_1434755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434802 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1434802 : Nat := 118140960795 + 1434802 * 2 ^ 59
def prefixEnd_1434802 : Nat := 4983230072969 + 3 ^ 40 * 1434802 * 2
def baseEnd_1434802 : Nat := 491162046688267042850981

theorem tailTrace_1434802 : CollatzResearch.WordTrace tailWord_1434802 prefixEnd_1434802 491162046688267042850981 := by
  unfold tailWord_1434802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13082882036991218379426665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34887685431976582345137773 13082882036991218379426665)
  ·
    refine ⟨9812161527743413784569999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13082882036991218379426665 9812161527743413784569999)
    ·
      refine ⟨14718242291615120676854999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9812161527743413784569999 14718242291615120676854999)
      ·
        refine ⟨22077363437422681015282499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14718242291615120676854999 22077363437422681015282499)
        ·
          refine ⟨33116045156134021522923749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22077363437422681015282499 33116045156134021522923749)
          ·
            refine ⟨6209258466775129035548203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33116045156134021522923749 6209258466775129035548203)
            ·
              refine ⟨9313887700162693553322305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209258466775129035548203 9313887700162693553322305)
              ·
                refine ⟨6985415775122020164991729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9313887700162693553322305 6985415775122020164991729)
                ·
                  refine ⟨5239061831341515123743797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6985415775122020164991729 5239061831341515123743797)
                  ·
                    refine ⟨491162046688267042850981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5239061831341515123743797 491162046688267042850981)
                    ·
                      rfl

theorem cell22_1434802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1434802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434802 prefixEnd_1434802 := by exact prefixLift 1434802
  have htrace : WordTrace (prefixWord ++ tailWord_1434802) baseStart_1434802 baseEnd_1434802 := by
    simpa [prefixWord, tailWord_1434802, baseEnd_1434802] using wordTrace_append hprefix tailTrace_1434802
  have hstable : (prefixWord ++ tailWord_1434802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434802).length < 2 ^ (prefixWord ++ tailWord_1434802).sum := by decide
  have hdescent : baseEnd_1434802 < baseStart_1434802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434847 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_1434847 : Nat := 118140960795 + 1434847 * 2 ^ 59
def prefixEnd_1434847 : Nat := 4983230072969 + 3 ^ 40 * 1434847 * 2
def baseEnd_1434847 : Nat := 491177451107901925475843

theorem tailTrace_1434847 : CollatzResearch.WordTrace tailWord_1434847 prefixEnd_1434847 491177451107901925475843 := by
  unfold tailWord_1434847
  simp only [CollatzResearch.WordTrace]
  refine ⟨52333169432801846203094795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34888779621867897468729863 52333169432801846203094795)
  ·
    refine ⟨78499754149202769304642193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52333169432801846203094795 78499754149202769304642193)
    ·
      refine ⟨58874815611902076978481645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78499754149202769304642193 58874815611902076978481645)
      ·
        refine ⟨22078055854463278866930617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58874815611902076978481645 22078055854463278866930617)
        ·
          refine ⟨16558541890847459150197963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22078055854463278866930617 16558541890847459150197963)
          ·
            refine ⟨24837812836271188725296945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16558541890847459150197963 24837812836271188725296945)
            ·
              refine ⟨18628359627203391543972709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24837812836271188725296945 18628359627203391543972709)
              ·
                refine ⟨3492817430100635914494883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18628359627203391543972709 3492817430100635914494883)
                ·
                  refine ⟨5239226145150953871742325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492817430100635914494883 5239226145150953871742325)
                  ·
                    refine ⟨491177451107901925475843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5239226145150953871742325 491177451107901925475843)
                    ·
                      rfl

theorem cell22_1434847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_1434847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434847 prefixEnd_1434847 := by exact prefixLift 1434847
  have htrace : WordTrace (prefixWord ++ tailWord_1434847) baseStart_1434847 baseEnd_1434847 := by
    simpa [prefixWord, tailWord_1434847, baseEnd_1434847] using wordTrace_append hprefix tailTrace_1434847
  have hstable : (prefixWord ++ tailWord_1434847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434847).length < 2 ^ (prefixWord ++ tailWord_1434847).sum := by decide
  have hdescent : baseEnd_1434847 < baseStart_1434847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434866 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_1434866 : Nat := 118140960795 + 1434866 * 2 ^ 59
def prefixEnd_1434866 : Nat := 4983230072969 + 3 ^ 40 * 1434866 * 2
def baseEnd_1434866 : Nat := 163727985065397403083595

theorem tailTrace_1434866 : CollatzResearch.WordTrace tailWord_1434866 prefixEnd_1434866 163727985065397403083595 := by
  unfold tailWord_1434866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083465604933253112009113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34889241613155341632024301 13083465604933253112009113)
  ·
    refine ⟨9812599203699939834006835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13083465604933253112009113 9812599203699939834006835)
    ·
      refine ⟨14718898805549909751010253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9812599203699939834006835 14718898805549909751010253)
      ·
        refine ⟨5519587052081216156628845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14718898805549909751010253 5519587052081216156628845)
        ·
          refine ⟨2069845144530456058735817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5519587052081216156628845 2069845144530456058735817)
          ·
            refine ⟨1552383858397842044051863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069845144530456058735817 1552383858397842044051863)
            ·
              refine ⟨2328575787596763066077795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552383858397842044051863 2328575787596763066077795)
              ·
                refine ⟨3492863681395144599116693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328575787596763066077795 3492863681395144599116693)
                ·
                  refine ⟨163727985065397403083595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3492863681395144599116693 163727985065397403083595)
                  ·
                    rfl

theorem cell22_1434866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_1434866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434866 prefixEnd_1434866 := by exact prefixLift 1434866
  have htrace : WordTrace (prefixWord ++ tailWord_1434866) baseStart_1434866 baseEnd_1434866 := by
    simpa [prefixWord, tailWord_1434866, baseEnd_1434866] using wordTrace_append hprefix tailTrace_1434866
  have hstable : (prefixWord ++ tailWord_1434866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434866).length < 2 ^ (prefixWord ++ tailWord_1434866).sum := by decide
  have hdescent : baseEnd_1434866 < baseStart_1434866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434881 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1434881 : Nat := 118140960795 + 1434881 * 2 ^ 59
def prefixEnd_1434881 : Nat := 4983230072969 + 3 ^ 40 * 1434881 * 2
def baseEnd_1434881 : Nat := 491189090002737170125739

theorem tailTrace_1434881 : CollatzResearch.WordTrace tailWord_1434881 prefixEnd_1434881 491189090002737170125739 := by
  unfold tailWord_1434881
  simp only [CollatzResearch.WordTrace]
  refine ⟨52334409514678670009832497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34889606343119113339888331 52334409514678670009832497)
  ·
    refine ⟨39250807136009002507374373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52334409514678670009832497 39250807136009002507374373)
    ·
      refine ⟨7359526338001687970132695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39250807136009002507374373 7359526338001687970132695)
      ·
        refine ⟨11039289507002531955199043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359526338001687970132695 11039289507002531955199043)
        ·
          refine ⟨16558934260503797932798565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039289507002531955199043 16558934260503797932798565)
          ·
            refine ⟨3104800173844462112399731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16558934260503797932798565 3104800173844462112399731)
            ·
              refine ⟨4657200260766693168599597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104800173844462112399731 4657200260766693168599597)
              ·
                refine ⟨1746450097787509938224849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4657200260766693168599597 1746450097787509938224849)
                ·
                  refine ⟨1309837573340632453668637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746450097787509938224849 1309837573340632453668637)
                  ·
                    refine ⟨491189090002737170125739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309837573340632453668637 491189090002737170125739)
                    ·
                      rfl

theorem cell22_1434881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1434881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434881 prefixEnd_1434881 := by exact prefixLift 1434881
  have htrace : WordTrace (prefixWord ++ tailWord_1434881) baseStart_1434881 baseEnd_1434881 := by
    simpa [prefixWord, tailWord_1434881, baseEnd_1434881] using wordTrace_append hprefix tailTrace_1434881
  have hstable : (prefixWord ++ tailWord_1434881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434881).length < 2 ^ (prefixWord ++ tailWord_1434881).sum := by decide
  have hdescent : baseEnd_1434881 < baseStart_1434881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434898 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1434898 : Nat := 118140960795 + 1434898 * 2 ^ 59
def prefixEnd_1434898 : Nat := 4983230072969 + 3 ^ 40 * 1434898 * 2
def baseEnd_1434898 : Nat := 491194909450154792450687

theorem tailTrace_1434898 : CollatzResearch.WordTrace tailWord_1434898 prefixEnd_1434898 491194909450154792450687 := by
  unfold tailWord_1434898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083757388904270478300337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34890019703744721275467565 13083757388904270478300337)
  ·
    refine ⟨9812818041678202858725253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13083757388904270478300337 9812818041678202858725253)
    ·
      refine ⟨1839903382814663036010985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9812818041678202858725253 1839903382814663036010985)
      ·
        refine ⟨1379927537110997277008239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1839903382814663036010985 1379927537110997277008239)
        ·
          refine ⟨2069891305666495915512359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379927537110997277008239 2069891305666495915512359)
          ·
            refine ⟨3104836958499743873268539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069891305666495915512359 3104836958499743873268539)
            ·
              refine ⟨4657255437749615809902809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104836958499743873268539 4657255437749615809902809)
              ·
                refine ⟨3492941578312211857427107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657255437749615809902809 3492941578312211857427107)
                ·
                  refine ⟨5239412367468317786140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492941578312211857427107 5239412367468317786140661)
                  ·
                    refine ⟨491194909450154792450687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5239412367468317786140661 491194909450154792450687)
                    ·
                      rfl

theorem cell22_1434898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1434898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434898 prefixEnd_1434898 := by exact prefixLift 1434898
  have htrace : WordTrace (prefixWord ++ tailWord_1434898) baseStart_1434898 baseEnd_1434898 := by
    simpa [prefixWord, tailWord_1434898, baseEnd_1434898] using wordTrace_append hprefix tailTrace_1434898
  have hstable : (prefixWord ++ tailWord_1434898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434898).length < 2 ^ (prefixWord ++ tailWord_1434898).sum := by decide
  have hdescent : baseEnd_1434898 < baseStart_1434898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434966 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1434966 : Nat := 118140960795 + 1434966 * 2 ^ 59
def prefixEnd_1434966 : Nat := 4983230072969 + 3 ^ 40 * 1434966 * 2
def baseEnd_1434966 : Nat := 491218187239825281750479

theorem tailTrace_1434966 : CollatzResearch.WordTrace tailWord_1434966 prefixEnd_1434966 491218187239825281750479 := by
  unfold tailWord_1434966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3271094357460670595417297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34891673146247153017784501 3271094357460670595417297)
  ·
    refine ⟨2453320768095502946562973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3271094357460670595417297 2453320768095502946562973)
    ·
      refine ⟨919995288035813604961115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2453320768095502946562973 919995288035813604961115)
      ·
        refine ⟨1379992932053720407441673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919995288035813604961115 1379992932053720407441673)
        ·
          refine ⟨1034994699040290305581255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379992932053720407441673 1034994699040290305581255)
          ·
            refine ⟨1552492048560435458371883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034994699040290305581255 1552492048560435458371883)
            ·
              refine ⟨2328738072840653187557825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552492048560435458371883 2328738072840653187557825)
              ·
                refine ⟨1746553554630489890668369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328738072840653187557825 1746553554630489890668369)
                ·
                  refine ⟨1309915165972867418001277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746553554630489890668369 1309915165972867418001277)
                  ·
                    refine ⟨491218187239825281750479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309915165972867418001277 491218187239825281750479)
                    ·
                      rfl

theorem cell22_1434966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1434966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434966 prefixEnd_1434966 := by exact prefixLift 1434966
  have htrace : WordTrace (prefixWord ++ tailWord_1434966) baseStart_1434966 baseEnd_1434966 := by
    simpa [prefixWord, tailWord_1434966, baseEnd_1434966] using wordTrace_append hprefix tailTrace_1434966
  have hstable : (prefixWord ++ tailWord_1434966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434966).length < 2 ^ (prefixWord ++ tailWord_1434966).sum := by decide
  have hdescent : baseEnd_1434966 < baseStart_1434966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434990 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_1434990 : Nat := 118140960795 + 1434990 * 2 ^ 59
def prefixEnd_1434990 : Nat := 4983230072969 + 3 ^ 40 * 1434990 * 2
def baseEnd_1434990 : Nat := 163742134310099073050135

theorem tailTrace_1434990 : CollatzResearch.WordTrace tailWord_1434990 prefixEnd_1434990 163742134310099073050135 := by
  unfold tailWord_1434990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542298133910472703193803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34892256714189187750366949 6542298133910472703193803)
  ·
    refine ⟨9813447200865709054790705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6542298133910472703193803 9813447200865709054790705)
    ·
      refine ⟨7360085400649281791093029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9813447200865709054790705 7360085400649281791093029)
      ·
        refine ⟨1380016012621740335829943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7360085400649281791093029 1380016012621740335829943)
        ·
          refine ⟨2070024018932610503744915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380016012621740335829943 2070024018932610503744915)
          ·
            refine ⟨3105036028398915755617373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070024018932610503744915 3105036028398915755617373)
            ·
              refine ⟨1164388510649593408356515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3105036028398915755617373 1164388510649593408356515)
              ·
                refine ⟨1746582765974390112534773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164388510649593408356515 1746582765974390112534773)
                ·
                  refine ⟨163742134310099073050135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1746582765974390112534773 163742134310099073050135)
                  ·
                    rfl

theorem cell22_1434990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_1434990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1434990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1434990 prefixEnd_1434990 := by exact prefixLift 1434990
  have htrace : WordTrace (prefixWord ++ tailWord_1434990) baseStart_1434990 baseEnd_1434990 := by
    simpa [prefixWord, tailWord_1434990, baseEnd_1434990] using wordTrace_append hprefix tailTrace_1434990
  have hstable : (prefixWord ++ tailWord_1434990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434990).length < 2 ^ (prefixWord ++ tailWord_1434990).sum := by decide
  have hdescent : baseEnd_1434990 < baseStart_1434990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435016 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1435016 : Nat := 118140960795 + 1435016 * 2 ^ 59
def prefixEnd_1435016 : Nat := 4983230072969 + 3 ^ 40 * 1435016 * 2
def baseEnd_1435016 : Nat := 491235303261641818000325

theorem tailTrace_1435016 : CollatzResearch.WordTrace tailWord_1435016 prefixEnd_1435016 491235303261641818000325 := by
  unfold tailWord_1435016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26169666684594794032998451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34892888912793058710664601 26169666684594794032998451)
  ·
    refine ⟨39254500026892191049497677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26169666684594794032998451 39254500026892191049497677)
    ·
      refine ⟨14720437510084571643561629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39254500026892191049497677 14720437510084571643561629)
      ·
        refine ⟨5520164066281714366335611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14720437510084571643561629 5520164066281714366335611)
        ·
          refine ⟨8280246099422571549503417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520164066281714366335611 8280246099422571549503417)
          ·
            refine ⟨6210184574566928662127563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8280246099422571549503417 6210184574566928662127563)
            ·
              refine ⟨9315276861850392993191345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210184574566928662127563 9315276861850392993191345)
              ·
                refine ⟨6986457646387794744893509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9315276861850392993191345 6986457646387794744893509)
                ·
                  refine ⟨1309960808697711514667533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6986457646387794744893509 1309960808697711514667533)
                  ·
                    refine ⟨491235303261641818000325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1309960808697711514667533 491235303261641818000325)
                    ·
                      rfl

theorem cell22_1435016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1435016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435016 prefixEnd_1435016 := by exact prefixLift 1435016
  have htrace : WordTrace (prefixWord ++ tailWord_1435016) baseStart_1435016 baseEnd_1435016 := by
    simpa [prefixWord, tailWord_1435016, baseEnd_1435016] using wordTrace_append hprefix tailTrace_1435016
  have hstable : (prefixWord ++ tailWord_1435016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435016).length < 2 ^ (prefixWord ++ tailWord_1435016).sum := by decide
  have hdescent : baseEnd_1435016 < baseStart_1435016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435119 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 8]
def baseStart_1435119 : Nat := 118140960795 + 1435119 * 2 ^ 59
def prefixEnd_1435119 : Nat := 4983230072969 + 3 ^ 40 * 1435119 * 2
def baseEnd_1435119 : Nat := 163756854088861294225003

theorem tailTrace_1435119 : CollatzResearch.WordTrace tailWord_1435119 prefixEnd_1435119 163756854088861294225003 := by
  unfold tailWord_1435119
  simp only [CollatzResearch.WordTrace]
  refine ⟨52343090087816436656996411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34895393391877624437997607 52343090087816436656996411)
  ·
    refine ⟨78514635131724654985494617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52343090087816436656996411 78514635131724654985494617)
    ·
      refine ⟨58885976348793491239120963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78514635131724654985494617 58885976348793491239120963)
      ·
        refine ⟨88328964523190236858681445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58885976348793491239120963 88328964523190236858681445)
        ·
          refine ⟨16561680848098169411002771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88328964523190236858681445 16561680848098169411002771)
          ·
            refine ⟨24842521272147254116504157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16561680848098169411002771 24842521272147254116504157)
            ·
              refine ⟨9315945477055220293689059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24842521272147254116504157 9315945477055220293689059)
              ·
                refine ⟨13973918215582830440533589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315945477055220293689059 13973918215582830440533589)
                ·
                  refine ⟨163756854088861294225003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13973918215582830440533589 163756854088861294225003)
                  ·
                    rfl

theorem cell22_1435119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_1435119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435119 prefixEnd_1435119 := by exact prefixLift 1435119
  have htrace : WordTrace (prefixWord ++ tailWord_1435119) baseStart_1435119 baseEnd_1435119 := by
    simpa [prefixWord, tailWord_1435119, baseEnd_1435119] using wordTrace_append hprefix tailTrace_1435119
  have hstable : (prefixWord ++ tailWord_1435119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435119).length < 2 ^ (prefixWord ++ tailWord_1435119).sum := by decide
  have hdescent : baseEnd_1435119 < baseStart_1435119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435121 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_1435121 : Nat := 118140960795 + 1435121 * 2 ^ 59
def prefixEnd_1435121 : Nat := 4983230072969 + 3 ^ 40 * 1435121 * 2
def baseEnd_1435121 : Nat := 491271246907456544125003

theorem tailTrace_1435121 : CollatzResearch.WordTrace tailWord_1435121 prefixEnd_1435121 491271246907456544125003 := by
  unfold tailWord_1435121
  simp only [CollatzResearch.WordTrace]
  refine ⟨52343163033809190998569217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34895442022539460665712811 52343163033809190998569217)
  ·
    refine ⟨39257372275356893248926913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52343163033809190998569217 39257372275356893248926913)
    ·
      refine ⟨29443029206517669936695185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39257372275356893248926913 29443029206517669936695185)
      ·
        refine ⟨22082271904888252452521389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29443029206517669936695185 22082271904888252452521389)
        ·
          refine ⟨8280851964333094669695521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22082271904888252452521389 8280851964333094669695521)
          ·
            refine ⟨6210638973249821002271641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8280851964333094669695521 6210638973249821002271641)
            ·
              refine ⟨4657979229937365751703731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210638973249821002271641 4657979229937365751703731)
              ·
                refine ⟨6986968844906048627555597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657979229937365751703731 6986968844906048627555597)
                ·
                  refine ⟨2620113316839768235333349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6986968844906048627555597 2620113316839768235333349)
                  ·
                    refine ⟨491271246907456544125003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2620113316839768235333349 491271246907456544125003)
                    ·
                      rfl

theorem cell22_1435121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_1435121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435121 prefixEnd_1435121 := by exact prefixLift 1435121
  have htrace : WordTrace (prefixWord ++ tailWord_1435121) baseStart_1435121 baseEnd_1435121 := by
    simpa [prefixWord, tailWord_1435121, baseEnd_1435121] using wordTrace_append hprefix tailTrace_1435121
  have hstable : (prefixWord ++ tailWord_1435121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435121).length < 2 ^ (prefixWord ++ tailWord_1435121).sum := by decide
  have hdescent : baseEnd_1435121 < baseStart_1435121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435142 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1435142 : Nat := 118140960795 + 1435142 * 2 ^ 59
def prefixEnd_1435142 : Nat := 4983230072969 + 3 ^ 40 * 1435142 * 2
def baseEnd_1435142 : Nat := 163759478545539829783313

theorem tailTrace_1435142 : CollatzResearch.WordTrace tailWord_1435142 prefixEnd_1435142 163759478545539829783313 := by
  unfold tailWord_1435142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635747780210409737033865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34895952644488741056722453 1635747780210409737033865)
  ·
    refine ⟨1226810835157807302775399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1635747780210409737033865 1226810835157807302775399)
    ·
      refine ⟨1840216252736710954163099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226810835157807302775399 1840216252736710954163099)
      ·
        refine ⟨2760324379105066431244649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840216252736710954163099 2760324379105066431244649)
        ·
          refine ⟨2070243284328799823433487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2760324379105066431244649 2070243284328799823433487)
          ·
            refine ⟨3105364926493199735150231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070243284328799823433487 3105364926493199735150231)
            ·
              refine ⟨4658047389739799602725347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3105364926493199735150231 4658047389739799602725347)
              ·
                refine ⟨6987071084609699404088021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658047389739799602725347 6987071084609699404088021)
                ·
                  refine ⟨163759478545539829783313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6987071084609699404088021 163759478545539829783313)
                  ·
                    rfl

theorem cell22_1435142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1435142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435142 prefixEnd_1435142 := by exact prefixLift 1435142
  have htrace : WordTrace (prefixWord ++ tailWord_1435142) baseStart_1435142 baseEnd_1435142 := by
    simpa [prefixWord, tailWord_1435142, baseEnd_1435142] using wordTrace_append hprefix tailTrace_1435142
  have hstable : (prefixWord ++ tailWord_1435142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435142).length < 2 ^ (prefixWord ++ tailWord_1435142).sum := by decide
  have hdescent : baseEnd_1435142 < baseStart_1435142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435168 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_1435168 : Nat := 118140960795 + 1435168 * 2 ^ 59
def prefixEnd_1435168 : Nat := 4983230072969 + 3 ^ 40 * 1435168 * 2
def baseEnd_1435168 : Nat := 491287335967964088199859

theorem tailTrace_1435168 : CollatzResearch.WordTrace tailWord_1435168 prefixEnd_1435168 491287335967964088199859 := by
  unfold tailWord_1435168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26172438632319459012765079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34896584843092612017020105 26172438632319459012765079)
  ·
    refine ⟨39258657948479188519147619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26172438632319459012765079 39258657948479188519147619)
    ·
      refine ⟨58887986922718782778721429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39258657948479188519147619 58887986922718782778721429)
      ·
        refine ⟨2760374387002442942752567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58887986922718782778721429 2760374387002442942752567)
        ·
          refine ⟨4140561580503664414128851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760374387002442942752567 4140561580503664414128851)
          ·
            refine ⟨6210842370755496621193277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140561580503664414128851 6210842370755496621193277)
            ·
              refine ⟨2329065889033311232947479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6210842370755496621193277 2329065889033311232947479)
              ·
                refine ⟨3493598833549966849421219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329065889033311232947479 3493598833549966849421219)
                ·
                  refine ⟨5240398250324950274131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493598833549966849421219 5240398250324950274131829)
                  ·
                    refine ⟨491287335967964088199859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5240398250324950274131829 491287335967964088199859)
                    ·
                      rfl

theorem cell22_1435168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_1435168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435168 prefixEnd_1435168 := by exact prefixLift 1435168
  have htrace : WordTrace (prefixWord ++ tailWord_1435168) baseStart_1435168 baseEnd_1435168 := by
    simpa [prefixWord, tailWord_1435168, baseEnd_1435168] using wordTrace_append hprefix tailTrace_1435168
  have hstable : (prefixWord ++ tailWord_1435168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435168).length < 2 ^ (prefixWord ++ tailWord_1435168).sum := by decide
  have hdescent : baseEnd_1435168 < baseStart_1435168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435256 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1435256 : Nat := 118140960795 + 1435256 * 2 ^ 59
def prefixEnd_1435256 : Nat := 4983230072969 + 3 ^ 40 * 1435256 * 2
def baseEnd_1435256 : Nat := 491317460166361191999589

theorem tailTrace_1435256 : CollatzResearch.WordTrace tailWord_1435256 prefixEnd_1435256 491317460166361191999589 := by
  unfold tailWord_1435256
  simp only [CollatzResearch.WordTrace]
  refine ⟨26174043444160054527366811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34898724592213406036489081 26174043444160054527366811)
  ·
    refine ⟨39261065166240081791050217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26174043444160054527366811 39261065166240081791050217)
    ·
      refine ⟨29445798874680061343287663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39261065166240081791050217 29445798874680061343287663)
      ·
        refine ⟨44168698312020092014931495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29445798874680061343287663 44168698312020092014931495)
        ·
          refine ⟨66253047468030138022397243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44168698312020092014931495 66253047468030138022397243)
          ·
            refine ⟨99379571202045207033595865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66253047468030138022397243 99379571202045207033595865)
            ·
              refine ⟨74534678401533905275196899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99379571202045207033595865 74534678401533905275196899)
              ·
                refine ⟨111802017602300857912795349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74534678401533905275196899 111802017602300857912795349)
                ·
                  refine ⟨2620359787553926357331141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 111802017602300857912795349 2620359787553926357331141)
                  ·
                    refine ⟨491317460166361191999589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2620359787553926357331141 491317460166361191999589)
                    ·
                      rfl

theorem cell22_1435256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1435256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435256 prefixEnd_1435256 := by exact prefixLift 1435256
  have htrace : WordTrace (prefixWord ++ tailWord_1435256) baseStart_1435256 baseEnd_1435256 := by
    simpa [prefixWord, tailWord_1435256, baseEnd_1435256] using wordTrace_append hprefix tailTrace_1435256
  have hstable : (prefixWord ++ tailWord_1435256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435256).length < 2 ^ (prefixWord ++ tailWord_1435256).sum := by decide
  have hdescent : baseEnd_1435256 < baseStart_1435256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435288 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_1435288 : Nat := 118140960795 + 1435288 * 2 ^ 59
def prefixEnd_1435288 : Nat := 4983230072969 + 3 ^ 40 * 1435288 * 2
def baseEnd_1435288 : Nat := 163776138140107925066497

theorem tailTrace_1435288 : CollatzResearch.WordTrace tailWord_1435288 prefixEnd_1435288 163776138140107925066497 := by
  unfold tailWord_1435288
  simp only [CollatzResearch.WordTrace]
  refine ⟨26174627012102089259949259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34899502682802785679932345 26174627012102089259949259)
  ·
    refine ⟨39261940518153133889923889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26174627012102089259949259 39261940518153133889923889)
    ·
      refine ⟨29446455388614850417442917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39261940518153133889923889 29446455388614850417442917)
      ·
        refine ⟨5521210385365284453270547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29446455388614850417442917 5521210385365284453270547)
        ·
          refine ⟨8281815578047926679905821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521210385365284453270547 8281815578047926679905821)
          ·
            refine ⟨3105680841767972504964683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8281815578047926679905821 3105680841767972504964683)
            ·
              refine ⟨4658521262651958757447025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3105680841767972504964683 4658521262651958757447025)
              ·
                refine ⟨3493890946988969068085269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4658521262651958757447025 3493890946988969068085269)
                ·
                  refine ⟨163776138140107925066497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3493890946988969068085269 163776138140107925066497)
                  ·
                    rfl

theorem cell22_1435288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_1435288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435288 prefixEnd_1435288 := by exact prefixLift 1435288
  have htrace : WordTrace (prefixWord ++ tailWord_1435288) baseStart_1435288 baseEnd_1435288 := by
    simpa [prefixWord, tailWord_1435288, baseEnd_1435288] using wordTrace_append hprefix tailTrace_1435288
  have hstable : (prefixWord ++ tailWord_1435288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435288).length < 2 ^ (prefixWord ++ tailWord_1435288).sum := by decide
  have hdescent : baseEnd_1435288 < baseStart_1435288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435356 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_1435356 : Nat := 118140960795 + 1435356 * 2 ^ 59
def prefixEnd_1435356 : Nat := 4983230072969 + 3 ^ 40 * 1435356 * 2
def baseEnd_1435356 : Nat := 163783897403331421499761

theorem tailTrace_1435356 : CollatzResearch.WordTrace tailWord_1435356 prefixEnd_1435356 163783897403331421499761 := by
  unfold tailWord_1435356
  simp only [CollatzResearch.WordTrace]
  refine ⟨26175867093978913066686961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34901156125305217422249281 26175867093978913066686961)
  ·
    refine ⟨19631900320484184800015221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26175867093978913066686961 19631900320484184800015221)
    ·
      refine ⟨1840490655045392325001427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19631900320484184800015221 1840490655045392325001427)
      ·
        refine ⟨2760735982568088487502141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840490655045392325001427 2760735982568088487502141)
        ·
          refine ⟨1035275993463033182813303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2760735982568088487502141 1035275993463033182813303)
          ·
            refine ⟨1552913990194549774219955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035275993463033182813303 1552913990194549774219955)
            ·
              refine ⟨2329370985291824661329933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552913990194549774219955 2329370985291824661329933)
              ·
                refine ⟨873514119484434247998725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2329370985291824661329933 873514119484434247998725)
                ·
                  refine ⟨163783897403331421499761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873514119484434247998725 163783897403331421499761)
                  ·
                    rfl

theorem cell22_1435356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_1435356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435356 prefixEnd_1435356 := by exact prefixLift 1435356
  have htrace : WordTrace (prefixWord ++ tailWord_1435356) baseStart_1435356 baseEnd_1435356 := by
    simpa [prefixWord, tailWord_1435356, baseEnd_1435356] using wordTrace_append hprefix tailTrace_1435356
  have hstable : (prefixWord ++ tailWord_1435356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435356).length < 2 ^ (prefixWord ++ tailWord_1435356).sum := by decide
  have hdescent : baseEnd_1435356 < baseStart_1435356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435367 : List Nat := [1, 1, 5, 4, 2, 1, 8]
def baseStart_1435367 : Nat := 118140960795 + 1435367 * 2 ^ 59
def prefixEnd_1435367 : Nat := 4983230072969 + 3 ^ 40 * 1435367 * 2
def baseEnd_1435367 : Nat := 18198350286473848239787

theorem tailTrace_1435367 : CollatzResearch.WordTrace tailWord_1435367 prefixEnd_1435367 18198350286473848239787 := by
  unfold tailWord_1435367
  simp only [CollatzResearch.WordTrace]
  refine ⟨52352135390917975012024355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34901423593945316674682903 52352135390917975012024355)
  ·
    refine ⟨78528203086376962518036533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52352135390917975012024355 78528203086376962518036533)
    ·
      refine ⟨7362019039347840236065925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78528203086376962518036533 7362019039347840236065925)
      ·
        refine ⟨1380378569877720044262361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7362019039347840236065925 1380378569877720044262361)
        ·
          refine ⟨1035283927408290033196771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380378569877720044262361 1035283927408290033196771)
          ·
            refine ⟨1552925891112435049795157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035283927408290033196771 1552925891112435049795157)
            ·
              refine ⟨18198350286473848239787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1552925891112435049795157 18198350286473848239787)
              ·
                rfl

theorem cell22_1435367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 8].length) (baseStart_1435367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435367 prefixEnd_1435367 := by exact prefixLift 1435367
  have htrace : WordTrace (prefixWord ++ tailWord_1435367) baseStart_1435367 baseEnd_1435367 := by
    simpa [prefixWord, tailWord_1435367, baseEnd_1435367] using wordTrace_append hprefix tailTrace_1435367
  have hstable : (prefixWord ++ tailWord_1435367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435367).length < 2 ^ (prefixWord ++ tailWord_1435367).sum := by decide
  have hdescent : baseEnd_1435367 < baseStart_1435367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435378 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1435378 : Nat := 118140960795 + 1435378 * 2 ^ 59
def prefixEnd_1435378 : Nat := 4983230072969 + 3 ^ 40 * 1435378 * 2
def baseEnd_1435378 : Nat := 163786407753197846816405

theorem tailTrace_1435378 : CollatzResearch.WordTrace tailWord_1435378 prefixEnd_1435378 163786407753197846816405 := by
  unfold tailWord_1435378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13088134148469530972668697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34901691062585415927116525 13088134148469530972668697)
  ·
    refine ⟨9816100611352148229501523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13088134148469530972668697 9816100611352148229501523)
    ·
      refine ⟨14724150917028222344252285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9816100611352148229501523 14724150917028222344252285)
      ·
        refine ⟨5521556593885583379094607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14724150917028222344252285 5521556593885583379094607)
        ·
          refine ⟨8282334890828375068641911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521556593885583379094607 8282334890828375068641911)
          ·
            refine ⟨12423502336242562602962867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282334890828375068641911 12423502336242562602962867)
            ·
              refine ⟨18635253504363843904444301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12423502336242562602962867 18635253504363843904444301)
              ·
                refine ⟨6988220064136441464166613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18635253504363843904444301 6988220064136441464166613)
                ·
                  refine ⟨163786407753197846816405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6988220064136441464166613 163786407753197846816405)
                  ·
                    rfl

theorem cell22_1435378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1435378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435378 prefixEnd_1435378 := by exact prefixLift 1435378
  have htrace : WordTrace (prefixWord ++ tailWord_1435378) baseStart_1435378 baseEnd_1435378 := by
    simpa [prefixWord, tailWord_1435378, baseEnd_1435378] using wordTrace_append hprefix tailTrace_1435378
  have hstable : (prefixWord ++ tailWord_1435378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435378).length < 2 ^ (prefixWord ++ tailWord_1435378).sum := by decide
  have hdescent : baseEnd_1435378 < baseStart_1435378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435382 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1435382 : Nat := 118140960795 + 1435382 * 2 ^ 59
def prefixEnd_1435382 : Nat := 4983230072969 + 3 ^ 40 * 1435382 * 2
def baseEnd_1435382 : Nat := 491360592541338863349203

theorem tailTrace_1435382 : CollatzResearch.WordTrace tailWord_1435382 prefixEnd_1435382 491360592541338863349203 := by
  unfold tailWord_1435382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272042655366477035863775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34901788323909088382546933 3272042655366477035863775)
  ·
    refine ⟨4908063983049715553795663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3272042655366477035863775 4908063983049715553795663)
    ·
      refine ⟨7362095974574573330693495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4908063983049715553795663 7362095974574573330693495)
      ·
        refine ⟨11043143961861859996040243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7362095974574573330693495 11043143961861859996040243)
        ·
          refine ⟨16564715942792789994060365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11043143961861859996040243 16564715942792789994060365)
          ·
            refine ⟨6211768478547296247772637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16564715942792789994060365 6211768478547296247772637)
            ·
              refine ⟨2329413179455236092914739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6211768478547296247772637 2329413179455236092914739)
              ·
                refine ⟨3494119769182854139372109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329413179455236092914739 3494119769182854139372109)
                ·
                  refine ⟨1310294913443570302264541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3494119769182854139372109 1310294913443570302264541)
                  ·
                    refine ⟨491360592541338863349203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310294913443570302264541 491360592541338863349203)
                    ·
                      rfl

theorem cell22_1435382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1435382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435382 prefixEnd_1435382 := by exact prefixLift 1435382
  have htrace : WordTrace (prefixWord ++ tailWord_1435382) baseStart_1435382 baseEnd_1435382 := by
    simpa [prefixWord, tailWord_1435382, baseEnd_1435382] using wordTrace_append hprefix tailTrace_1435382
  have hstable : (prefixWord ++ tailWord_1435382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435382).length < 2 ^ (prefixWord ++ tailWord_1435382).sum := by decide
  have hdescent : baseEnd_1435382 < baseStart_1435382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435393 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1435393 : Nat := 118140960795 + 1435393 * 2 ^ 59
def prefixEnd_1435393 : Nat := 4983230072969 + 3 ^ 40 * 1435393 * 2
def baseEnd_1435393 : Nat := 491364358066138501324169

theorem tailTrace_1435393 : CollatzResearch.WordTrace tailWord_1435393 prefixEnd_1435393 491364358066138501324169 := by
  unfold tailWord_1435393
  simp only [CollatzResearch.WordTrace]
  refine ⟨52353083688823781452470833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34902055792549187634980555 52353083688823781452470833)
  ·
    refine ⟨39264812766617836089353125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52353083688823781452470833 39264812766617836089353125)
    ·
      refine ⟨7362152393740844266753711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39264812766617836089353125 7362152393740844266753711)
      ·
        refine ⟨11043228590611266400130567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7362152393740844266753711 11043228590611266400130567)
        ·
          refine ⟨16564842885916899600195851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11043228590611266400130567 16564842885916899600195851)
          ·
            refine ⟨24847264328875349400293777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16564842885916899600195851 24847264328875349400293777)
            ·
              refine ⟨18635448246656512050220333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24847264328875349400293777 18635448246656512050220333)
              ·
                refine ⟨6988293092496192018832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18635448246656512050220333 6988293092496192018832625)
                ·
                  refine ⟨5241219819372144014124469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6988293092496192018832625 5241219819372144014124469)
                  ·
                    refine ⟨491364358066138501324169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5241219819372144014124469 491364358066138501324169)
                    ·
                      rfl

theorem cell22_1435393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1435393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435393 prefixEnd_1435393 := by exact prefixLift 1435393
  have htrace : WordTrace (prefixWord ++ tailWord_1435393) baseStart_1435393 baseEnd_1435393 := by
    simpa [prefixWord, tailWord_1435393, baseEnd_1435393] using wordTrace_append hprefix tailTrace_1435393
  have hstable : (prefixWord ++ tailWord_1435393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435393).length < 2 ^ (prefixWord ++ tailWord_1435393).sum := by decide
  have hdescent : baseEnd_1435393 < baseStart_1435393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435395 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 5]
def baseStart_1435395 : Nat := 118140960795 + 1435395 * 2 ^ 59
def prefixEnd_1435395 : Nat := 4983230072969 + 3 ^ 40 * 1435395 * 2
def baseEnd_1435395 : Nat := 163788347569003720924721

theorem tailTrace_1435395 : CollatzResearch.WordTrace tailWord_1435395 prefixEnd_1435395 163788347569003720924721 := by
  unfold tailWord_1435395
  simp only [CollatzResearch.WordTrace]
  refine ⟨52353156634816535794043639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34902104423211023862695759 52353156634816535794043639)
  ·
    refine ⟨78529734952224803691065459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52353156634816535794043639 78529734952224803691065459)
    ·
      refine ⟨117794602428337205536598189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78529734952224803691065459 117794602428337205536598189)
      ·
        refine ⟨44172975910626452076224321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117794602428337205536598189 44172975910626452076224321)
        ·
          refine ⟨33129731932969839057168241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44172975910626452076224321 33129731932969839057168241)
          ·
            refine ⟨24847298949727379292876181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33129731932969839057168241 24847298949727379292876181)
            ·
              refine ⟨1164717138268470904353571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24847298949727379292876181 1164717138268470904353571)
              ·
                refine ⟨1747075707402706356530357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164717138268470904353571 1747075707402706356530357)
                ·
                  refine ⟨163788347569003720924721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747075707402706356530357 163788347569003720924721)
                  ·
                    rfl

theorem cell22_1435395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 5].length) (baseStart_1435395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435395 prefixEnd_1435395 := by exact prefixLift 1435395
  have htrace : WordTrace (prefixWord ++ tailWord_1435395) baseStart_1435395 baseEnd_1435395 := by
    simpa [prefixWord, tailWord_1435395, baseEnd_1435395] using wordTrace_append hprefix tailTrace_1435395
  have hstable : (prefixWord ++ tailWord_1435395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435395).length < 2 ^ (prefixWord ++ tailWord_1435395).sum := by decide
  have hdescent : baseEnd_1435395 < baseStart_1435395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435551 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 3, 3]
def baseStart_1435551 : Nat := 118140960795 + 1435551 * 2 ^ 59
def prefixEnd_1435551 : Nat := 4983230072969 + 3 ^ 40 * 1435551 * 2
def baseEnd_1435551 : Nat := 491418444695078755873685

theorem tailTrace_1435551 : CollatzResearch.WordTrace tailWord_1435551 prefixEnd_1435551 491418444695078755873685 := by
  unfold tailWord_1435551
  simp only [CollatzResearch.WordTrace]
  refine ⟨52358846422251374436722507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34905897614834249624481671 52358846422251374436722507)
  ·
    refine ⟨78538269633377061655083761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52358846422251374436722507 78538269633377061655083761)
    ·
      refine ⟨58903702225032796241312821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78538269633377061655083761 58903702225032796241312821)
      ·
        refine ⟨5522222083596824647623077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58903702225032796241312821 5522222083596824647623077)
        ·
          refine ⟨1035416640674404621429327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5522222083596824647623077 1035416640674404621429327)
          ·
            refine ⟨1553124961011606932143991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035416640674404621429327 1553124961011606932143991)
            ·
              refine ⟨2329687441517410398215987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553124961011606932143991 2329687441517410398215987)
              ·
                refine ⟨3494531162276115597323981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329687441517410398215987 3494531162276115597323981)
                ·
                  refine ⟨1310449185853543348996493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3494531162276115597323981 1310449185853543348996493)
                  ·
                    refine ⟨491418444695078755873685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310449185853543348996493 491418444695078755873685)
                    ·
                      rfl

theorem cell22_1435551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_1435551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435551 prefixEnd_1435551 := by exact prefixLift 1435551
  have htrace : WordTrace (prefixWord ++ tailWord_1435551) baseStart_1435551 baseEnd_1435551 := by
    simpa [prefixWord, tailWord_1435551, baseEnd_1435551] using wordTrace_append hprefix tailTrace_1435551
  have hstable : (prefixWord ++ tailWord_1435551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435551).length < 2 ^ (prefixWord ++ tailWord_1435551).sum := by decide
  have hdescent : baseEnd_1435551 < baseStart_1435551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435609 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 4]
def baseStart_1435609 : Nat := 118140960795 + 1435609 * 2 ^ 59
def prefixEnd_1435609 : Nat := 4983230072969 + 3 ^ 40 * 1435609 * 2
def baseEnd_1435609 : Nat := 163812766426795312641169

theorem tailTrace_1435609 : CollatzResearch.WordTrace tailWord_1435609 prefixEnd_1435609 163812766426795312641169 := by
  unfold tailWord_1435609
  simp only [CollatzResearch.WordTrace]
  refine ⟨52360961856041250342333881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34907307904027500228222587 52360961856041250342333881)
  ·
    refine ⟨39270721392030937756750411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52360961856041250342333881 39270721392030937756750411)
    ·
      refine ⟨58906082088046406635125617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39270721392030937756750411 58906082088046406635125617)
      ·
        refine ⟨44179561566034804976344213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58906082088046406635125617 44179561566034804976344213)
        ·
          refine ⟨2070916948407881483266135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44179561566034804976344213 2070916948407881483266135)
          ·
            refine ⟨3106375422611822224899203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070916948407881483266135 3106375422611822224899203)
            ·
              refine ⟨4659563133917733337348805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106375422611822224899203 4659563133917733337348805)
              ·
                refine ⟨873668087609575000752901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4659563133917733337348805 873668087609575000752901)
                ·
                  refine ⟨163812766426795312641169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873668087609575000752901 163812766426795312641169)
                  ·
                    rfl

theorem cell22_1435609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_1435609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435609 prefixEnd_1435609 := by exact prefixLift 1435609
  have htrace : WordTrace (prefixWord ++ tailWord_1435609) baseStart_1435609 baseEnd_1435609 := by
    simpa [prefixWord, tailWord_1435609, baseEnd_1435609] using wordTrace_append hprefix tailTrace_1435609
  have hstable : (prefixWord ++ tailWord_1435609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435609).length < 2 ^ (prefixWord ++ tailWord_1435609).sum := by decide
  have hdescent : baseEnd_1435609 < baseStart_1435609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435658 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_1435658 : Nat := 118140960795 + 1435658 * 2 ^ 59
def prefixEnd_1435658 : Nat := 4983230072969 + 3 ^ 40 * 1435658 * 2
def baseEnd_1435658 : Nat := 491455072981766143448357

theorem tailTrace_1435658 : CollatzResearch.WordTrace tailWord_1435658 prefixEnd_1435658 491455072981766143448357 := by
  unfold tailWord_1435658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13090687258215932927716907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34908499355242487807245085 13090687258215932927716907)
  ·
    refine ⟨19636030887323899391575361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13090687258215932927716907 19636030887323899391575361)
    ·
      refine ⟨14727023165492924543681521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19636030887323899391575361 14727023165492924543681521)
      ·
        refine ⟨11045267374119693407761141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14727023165492924543681521 11045267374119693407761141)
        ·
          refine ⟨1035493816323721256977607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11045267374119693407761141 1035493816323721256977607)
          ·
            refine ⟨1553240724485581885466411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035493816323721256977607 1553240724485581885466411)
            ·
              refine ⟨2329861086728372828199617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553240724485581885466411 2329861086728372828199617)
              ·
                refine ⟨1747395815046279621149713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329861086728372828199617 1747395815046279621149713)
                ·
                  refine ⟨1310546861284709715862285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1747395815046279621149713 1310546861284709715862285)
                  ·
                    refine ⟨491455072981766143448357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310546861284709715862285 491455072981766143448357)
                    ·
                      rfl

theorem cell22_1435658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_1435658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435658 prefixEnd_1435658 := by exact prefixLift 1435658
  have htrace : WordTrace (prefixWord ++ tailWord_1435658) baseStart_1435658 baseEnd_1435658 := by
    simpa [prefixWord, tailWord_1435658, baseEnd_1435658] using wordTrace_append hprefix tailTrace_1435658
  have hstable : (prefixWord ++ tailWord_1435658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435658).length < 2 ^ (prefixWord ++ tailWord_1435658).sum := by decide
  have hdescent : baseEnd_1435658 < baseStart_1435658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435688 : List Nat := [2, 1, 5, 3, 2, 1, 2, 6]
def baseStart_1435688 : Nat := 118140960795 + 1435688 * 2 ^ 59
def prefixEnd_1435688 : Nat := 4983230072969 + 3 ^ 40 * 1435688 * 2
def baseEnd_1435688 : Nat := 54607260288317340577585

theorem tailTrace_1435688 : CollatzResearch.WordTrace tailWord_1435688 prefixEnd_1435688 54607260288317340577585 := by
  unfold tailWord_1435688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26181921611377523417229859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34909228815170031222973145 26181921611377523417229859)
  ·
    refine ⟨39272882417066285125844789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26181921611377523417229859 39272882417066285125844789)
    ·
      refine ⟨3681832726599964230547949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39272882417066285125844789 3681832726599964230547949)
      ·
        refine ⟨1380687272474986586455481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3681832726599964230547949 1380687272474986586455481)
        ·
          refine ⟨1035515454356239939841611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380687272474986586455481 1035515454356239939841611)
          ·
            refine ⟨1553273181534359909762417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035515454356239939841611 1553273181534359909762417)
            ·
              refine ⟨1164954886150769932321813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553273181534359909762417 1164954886150769932321813)
              ·
                refine ⟨54607260288317340577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1164954886150769932321813 54607260288317340577585)
                ·
                  rfl

theorem cell22_1435688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_1435688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435688 prefixEnd_1435688 := by exact prefixLift 1435688
  have htrace : WordTrace (prefixWord ++ tailWord_1435688) baseStart_1435688 baseEnd_1435688 := by
    simpa [prefixWord, tailWord_1435688, baseEnd_1435688] using wordTrace_append hprefix tailTrace_1435688
  have hstable : (prefixWord ++ tailWord_1435688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435688).length < 2 ^ (prefixWord ++ tailWord_1435688).sum := by decide
  have hdescent : baseEnd_1435688 < baseStart_1435688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435746 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1435746 : Nat := 118140960795 + 1435746 * 2 ^ 59
def prefixEnd_1435746 : Nat := 4983230072969 + 3 ^ 40 * 1435746 * 2
def baseEnd_1435746 : Nat := 491485197180163247248087

theorem tailTrace_1435746 : CollatzResearch.WordTrace tailWord_1435746 prefixEnd_1435746 491485197180163247248087 := by
  unfold tailWord_1435746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13091489664136230685017773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34910639104363281826714061 13091489664136230685017773)
  ·
    refine ⟨4909308624051086506881665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13091489664136230685017773 4909308624051086506881665)
    ·
      refine ⟨3681981468038314880161249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4909308624051086506881665 3681981468038314880161249)
      ·
        refine ⟨2761486101028736160120937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3681981468038314880161249 2761486101028736160120937)
        ·
          refine ⟨2071114575771552120090703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761486101028736160120937 2071114575771552120090703)
          ·
            refine ⟨3106671863657328180136055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071114575771552120090703 3106671863657328180136055)
            ·
              refine ⟨4660007795485992270204083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106671863657328180136055 4660007795485992270204083)
              ·
                refine ⟨6990011693228988405306125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660007795485992270204083 6990011693228988405306125)
                ·
                  refine ⟨2621254384960870651989797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6990011693228988405306125 2621254384960870651989797)
                  ·
                    refine ⟨491485197180163247248087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621254384960870651989797 491485197180163247248087)
                    ·
                      rfl

theorem cell22_1435746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1435746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435746 prefixEnd_1435746 := by exact prefixLift 1435746
  have htrace : WordTrace (prefixWord ++ tailWord_1435746) baseStart_1435746 baseEnd_1435746 := by
    simpa [prefixWord, tailWord_1435746, baseEnd_1435746] using wordTrace_append hprefix tailTrace_1435746
  have hstable : (prefixWord ++ tailWord_1435746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435746).length < 2 ^ (prefixWord ++ tailWord_1435746).sum := by decide
  have hdescent : baseEnd_1435746 < baseStart_1435746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435832 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1435832 : Nat := 118140960795 + 1435832 * 2 ^ 59
def prefixEnd_1435832 : Nat := 4983230072969 + 3 ^ 40 * 1435832 * 2
def baseEnd_1435832 : Nat := 491514636737687689597823

theorem tailTrace_1435832 : CollatzResearch.WordTrace tailWord_1435832 prefixEnd_1435832 491514636737687689597823 := by
  unfold tailWord_1435832
  simp only [CollatzResearch.WordTrace]
  refine ⟨26184547667116679713850875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34912730222822239618467833 26184547667116679713850875)
  ·
    refine ⟨39276821500675019570776313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26184547667116679713850875 39276821500675019570776313)
    ·
      refine ⟨29457616125506264678082235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39276821500675019570776313 29457616125506264678082235)
      ·
        refine ⟨44186424188259397017123353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29457616125506264678082235 44186424188259397017123353)
        ·
          refine ⟨33139818141194547762842515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44186424188259397017123353 33139818141194547762842515)
          ·
            refine ⟨49709727211791821644263773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33139818141194547762842515 49709727211791821644263773)
            ·
              refine ⟨18641147704421933116598915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49709727211791821644263773 18641147704421933116598915)
              ·
                refine ⟨27961721556632899674898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641147704421933116598915 27961721556632899674898373)
                ·
                  refine ⟨5242822791868668689043445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27961721556632899674898373 5242822791868668689043445)
                  ·
                    refine ⟨491514636737687689597823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5242822791868668689043445 491514636737687689597823)
                    ·
                      rfl

theorem cell22_1435832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1435832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435832 prefixEnd_1435832 := by exact prefixLift 1435832
  have htrace : WordTrace (prefixWord ++ tailWord_1435832) baseStart_1435832 baseEnd_1435832 := by
    simpa [prefixWord, tailWord_1435832, baseEnd_1435832] using wordTrace_append hprefix tailTrace_1435832
  have hstable : (prefixWord ++ tailWord_1435832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435832).length < 2 ^ (prefixWord ++ tailWord_1435832).sum := by decide
  have hdescent : baseEnd_1435832 < baseStart_1435832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435834 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_1435834 : Nat := 118140960795 + 1435834 * 2 ^ 59
def prefixEnd_1435834 : Nat := 4983230072969 + 3 ^ 40 * 1435834 * 2
def baseEnd_1435834 : Nat := 163838440459520117015939

theorem tailTrace_1435834 : CollatzResearch.WordTrace tailWord_1435834 prefixEnd_1435834 163838440459520117015939 := by
  unfold tailWord_1435834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092292070056528442318639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34912778853484075846183037 13092292070056528442318639)
  ·
    refine ⟨19638438105084792663477959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13092292070056528442318639 19638438105084792663477959)
    ·
      refine ⟨29457657157627188995216939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19638438105084792663477959 29457657157627188995216939)
      ·
        refine ⟨44186485736440783492825409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29457657157627188995216939 44186485736440783492825409)
        ·
          refine ⟨33139864302330587619619057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44186485736440783492825409 33139864302330587619619057)
          ·
            refine ⟨24854898226747940714714293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33139864302330587619619057 24854898226747940714714293)
            ·
              refine ⟨2330146708757619442004465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24854898226747940714714293 2330146708757619442004465)
              ·
                refine ⟨1747610031568214581503349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330146708757619442004465 1747610031568214581503349)
                ·
                  refine ⟨163838440459520117015939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747610031568214581503349 163838440459520117015939)
                  ·
                    rfl

theorem cell22_1435834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_1435834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435834 prefixEnd_1435834 := by exact prefixLift 1435834
  have htrace : WordTrace (prefixWord ++ tailWord_1435834) baseStart_1435834 baseEnd_1435834 := by
    simpa [prefixWord, tailWord_1435834, baseEnd_1435834] using wordTrace_append hprefix tailTrace_1435834
  have hstable : (prefixWord ++ tailWord_1435834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435834).length < 2 ^ (prefixWord ++ tailWord_1435834).sum := by decide
  have hdescent : baseEnd_1435834 < baseStart_1435834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435838 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1435838 : Nat := 118140960795 + 1435838 * 2 ^ 59
def prefixEnd_1435838 : Nat := 4983230072969 + 3 ^ 40 * 1435838 * 2
def baseEnd_1435838 : Nat := 491516690660305673947805

theorem tailTrace_1435838 : CollatzResearch.WordTrace tailWord_1435838 prefixEnd_1435838 491516690660305673947805 := by
  unfold tailWord_1435838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546164271526452806552521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34912876114807748301613445 6546164271526452806552521)
  ·
    refine ⟨4909623203644839604914391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6546164271526452806552521 4909623203644839604914391)
    ·
      refine ⟨7364434805467259407371587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909623203644839604914391 7364434805467259407371587)
      ·
        refine ⟨11046652208200889111057381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364434805467259407371587 11046652208200889111057381)
        ·
          refine ⟨2071247289037666708323259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11046652208200889111057381 2071247289037666708323259)
          ·
            refine ⟨3106870933556500062484889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071247289037666708323259 3106870933556500062484889)
            ·
              refine ⟨2330153200167375046863667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106870933556500062484889 2330153200167375046863667)
              ·
                refine ⟨3495229800251062570295501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330153200167375046863667 3495229800251062570295501)
                ·
                  refine ⟨1310711175094148463860813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3495229800251062570295501 1310711175094148463860813)
                  ·
                    refine ⟨491516690660305673947805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310711175094148463860813 491516690660305673947805)
                    ·
                      rfl

theorem cell22_1435838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1435838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1435838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1435838 prefixEnd_1435838 := by exact prefixLift 1435838
  have htrace : WordTrace (prefixWord ++ tailWord_1435838) baseStart_1435838 baseEnd_1435838 := by
    simpa [prefixWord, tailWord_1435838, baseEnd_1435838] using wordTrace_append hprefix tailTrace_1435838
  have hstable : (prefixWord ++ tailWord_1435838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435838).length < 2 ^ (prefixWord ++ tailWord_1435838).sum := by decide
  have hdescent : baseEnd_1435838 < baseStart_1435838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436033 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1436033 : Nat := 118140960795 + 1436033 * 2 ^ 59
def prefixEnd_1436033 : Nat := 4983230072969 + 3 ^ 40 * 1436033 * 2
def baseEnd_1436033 : Nat := 491583443145390165322207

theorem tailTrace_1436033 : CollatzResearch.WordTrace tailWord_1436033 prefixEnd_1436033 491583443145390165322207 := by
  unfold tailWord_1436033
  simp only [CollatzResearch.WordTrace]
  refine ⟨52376426406505170755768753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34917617604336780503845835 52376426406505170755768753)
  ·
    refine ⟨39282319804878878066826565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52376426406505170755768753 39282319804878878066826565)
    ·
      refine ⟨7365434963414789637529981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39282319804878878066826565 7365434963414789637529981)
      ·
        refine ⟨2762038111280546114073743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7365434963414789637529981 2762038111280546114073743)
        ·
          refine ⟨4143057166920819171110615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762038111280546114073743 4143057166920819171110615)
          ·
            refine ⟨6214585750381228756665923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143057166920819171110615 6214585750381228756665923)
            ·
              refine ⟨9321878625571843134998885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214585750381228756665923 9321878625571843134998885)
              ·
                refine ⟨1747852242294720587812291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9321878625571843134998885 1747852242294720587812291)
                ·
                  refine ⟨2621778363442080881718437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747852242294720587812291 2621778363442080881718437)
                  ·
                    refine ⟨491583443145390165322207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621778363442080881718437 491583443145390165322207)
                    ·
                      rfl

theorem cell22_1436033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1436033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436033 prefixEnd_1436033 := by exact prefixLift 1436033
  have htrace : WordTrace (prefixWord ++ tailWord_1436033) baseStart_1436033 baseEnd_1436033 := by
    simpa [prefixWord, tailWord_1436033, baseEnd_1436033] using wordTrace_append hprefix tailTrace_1436033
  have hstable : (prefixWord ++ tailWord_1436033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436033).length < 2 ^ (prefixWord ++ tailWord_1436033).sum := by decide
  have hdescent : baseEnd_1436033 < baseStart_1436033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436063 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 2, 3]
def baseStart_1436063 : Nat := 118140960795 + 1436063 * 2 ^ 59
def prefixEnd_1436063 : Nat := 4983230072969 + 3 ^ 40 * 1436063 * 2
def baseEnd_1436063 : Nat := 491593712758480087072115

theorem tailTrace_1436063 : CollatzResearch.WordTrace tailWord_1436063 prefixEnd_1436063 491593712758480087072115 := by
  unfold tailWord_1436063
  simp only [CollatzResearch.WordTrace]
  refine ⟨52377520596396485879360843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34918347064264323919573895 52377520596396485879360843)
  ·
    refine ⟨78566280894594728819041265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52377520596396485879360843 78566280894594728819041265)
    ·
      refine ⟨58924710670946046614280949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78566280894594728819041265 58924710670946046614280949)
      ·
        refine ⟨5524191625401191870088839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58924710670946046614280949 5524191625401191870088839)
        ·
          refine ⟨8286287438101787805133259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524191625401191870088839 8286287438101787805133259)
          ·
            refine ⟨12429431157152681707699889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8286287438101787805133259 12429431157152681707699889)
            ·
              refine ⟨9322073367864511280774917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12429431157152681707699889 9322073367864511280774917)
              ·
                refine ⟨1747888756474595865145297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9322073367864511280774917 1747888756474595865145297)
                ·
                  refine ⟨1310916567355946898858973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1747888756474595865145297 1310916567355946898858973)
                  ·
                    refine ⟨491593712758480087072115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1310916567355946898858973 491593712758480087072115)
                    ·
                      rfl

theorem cell22_1436063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_1436063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436063 prefixEnd_1436063 := by exact prefixLift 1436063
  have htrace : WordTrace (prefixWord ++ tailWord_1436063) baseStart_1436063 baseEnd_1436063 := by
    simpa [prefixWord, tailWord_1436063, baseEnd_1436063] using wordTrace_append hprefix tailTrace_1436063
  have hstable : (prefixWord ++ tailWord_1436063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436063).length < 2 ^ (prefixWord ++ tailWord_1436063).sum := by decide
  have hdescent : baseEnd_1436063 < baseStart_1436063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436065 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 6]
def baseStart_1436065 : Nat := 118140960795 + 1436065 * 2 ^ 59
def prefixEnd_1436065 : Nat := 4983230072969 + 3 ^ 40 * 1436065 * 2
def baseEnd_1436065 : Nat := 163864799133117582840703

theorem tailTrace_1436065 : CollatzResearch.WordTrace tailWord_1436065 prefixEnd_1436065 163864799133117582840703 := by
  unfold tailWord_1436065
  simp only [CollatzResearch.WordTrace]
  refine ⟨52377593542389240220933649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34918395694926160147289099 52377593542389240220933649)
  ·
    refine ⟨39283195156791930165700237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52377593542389240220933649 39283195156791930165700237)
    ·
      refine ⟨14731198183796973812137589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39283195156791930165700237 14731198183796973812137589)
      ·
        refine ⟨1381049829730966294887899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14731198183796973812137589 1381049829730966294887899)
        ·
          refine ⟨2071574744596449442331849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381049829730966294887899 2071574744596449442331849)
          ·
            refine ⟨1553681058447337081748887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071574744596449442331849 1553681058447337081748887)
            ·
              refine ⟨2330521587671005622623331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553681058447337081748887 2330521587671005622623331)
              ·
                refine ⟨3495782381506508433934997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330521587671005622623331 3495782381506508433934997)
                ·
                  refine ⟨163864799133117582840703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3495782381506508433934997 163864799133117582840703)
                  ·
                    rfl

theorem cell22_1436065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_1436065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436065 prefixEnd_1436065 := by exact prefixLift 1436065
  have htrace : WordTrace (prefixWord ++ tailWord_1436065) baseStart_1436065 baseEnd_1436065 := by
    simpa [prefixWord, tailWord_1436065, baseEnd_1436065] using wordTrace_append hprefix tailTrace_1436065
  have hstable : (prefixWord ++ tailWord_1436065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436065).length < 2 ^ (prefixWord ++ tailWord_1436065).sum := by decide
  have hdescent : baseEnd_1436065 < baseStart_1436065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436084 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1436084 : Nat := 118140960795 + 1436084 * 2 ^ 59
def prefixEnd_1436084 : Nat := 4983230072969 + 3 ^ 40 * 1436084 * 2
def baseEnd_1436084 : Nat := 491600901487643032297051

theorem tailTrace_1436084 : CollatzResearch.WordTrace tailWord_1436084 prefixEnd_1436084 491600901487643032297051 := by
  unfold tailWord_1436084
  simp only [CollatzResearch.WordTrace]
  refine ⟨26189143264660203232937653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34918857686213604310583537 26189143264660203232937653)
  ·
    refine ⟨2455232181061894053087905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26189143264660203232937653 2455232181061894053087905)
    ·
      refine ⟨1841424135796420539815929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2455232181061894053087905 1841424135796420539815929)
      ·
        refine ⟨1381068101847315404861947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1841424135796420539815929 1381068101847315404861947)
        ·
          refine ⟨2071602152770973107292921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381068101847315404861947 2071602152770973107292921)
          ·
            refine ⟨1553701614578229830469691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071602152770973107292921 1553701614578229830469691)
            ·
              refine ⟨2330552421867344745704537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553701614578229830469691 2330552421867344745704537)
              ·
                refine ⟨1747914316400508559278403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330552421867344745704537 1747914316400508559278403)
                ·
                  refine ⟨2621871474600762838917605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747914316400508559278403 2621871474600762838917605)
                  ·
                    refine ⟨491600901487643032297051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621871474600762838917605 491600901487643032297051)
                    ·
                      rfl

theorem cell22_1436084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1436084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436084 prefixEnd_1436084 := by exact prefixLift 1436084
  have htrace : WordTrace (prefixWord ++ tailWord_1436084) baseStart_1436084 baseEnd_1436084 := by
    simpa [prefixWord, tailWord_1436084, baseEnd_1436084] using wordTrace_append hprefix tailTrace_1436084
  have hstable : (prefixWord ++ tailWord_1436084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436084).length < 2 ^ (prefixWord ++ tailWord_1436084).sum := by decide
  have hdescent : baseEnd_1436084 < baseStart_1436084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436097 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1436097 : Nat := 118140960795 + 1436097 * 2 ^ 59
def prefixEnd_1436097 : Nat := 4983230072969 + 3 ^ 40 * 1436097 * 2
def baseEnd_1436097 : Nat := 491605351653315331722011

theorem tailTrace_1436097 : CollatzResearch.WordTrace tailWord_1436097 prefixEnd_1436097 491605351653315331722011 := by
  unfold tailWord_1436097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52378760678273309686098545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34919173785515539790732363 52378760678273309686098545)
  ·
    refine ⟨39284070508704982264573909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52378760678273309686098545 39284070508704982264573909)
    ·
      refine ⟨920720402547773021825951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39284070508704982264573909 920720402547773021825951)
      ·
        refine ⟨1381080603821659532738927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920720402547773021825951 1381080603821659532738927)
        ·
          refine ⟨2071620905732489299108391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381080603821659532738927 2071620905732489299108391)
          ·
            refine ⟨3107431358598733948662587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071620905732489299108391 3107431358598733948662587)
            ·
              refine ⟨4661147037898100922993881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107431358598733948662587 4661147037898100922993881)
              ·
                refine ⟨3495860278423575692245411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661147037898100922993881 3495860278423575692245411)
                ·
                  refine ⟨5243790417635363538368117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495860278423575692245411 5243790417635363538368117)
                  ·
                    refine ⟨491605351653315331722011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5243790417635363538368117 491605351653315331722011)
                    ·
                      rfl

theorem cell22_1436097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1436097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436097 prefixEnd_1436097 := by exact prefixLift 1436097
  have htrace : WordTrace (prefixWord ++ tailWord_1436097) baseStart_1436097 baseEnd_1436097 := by
    simpa [prefixWord, tailWord_1436097, baseEnd_1436097] using wordTrace_append hprefix tailTrace_1436097
  have hstable : (prefixWord ++ tailWord_1436097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436097).length < 2 ^ (prefixWord ++ tailWord_1436097).sum := by decide
  have hdescent : baseEnd_1436097 < baseStart_1436097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436136 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1436136 : Nat := 118140960795 + 1436136 * 2 ^ 59
def prefixEnd_1436136 : Nat := 4983230072969 + 3 ^ 40 * 1436136 * 2
def baseEnd_1436136 : Nat := 491618702150332229996891

theorem tailTrace_1436136 : CollatzResearch.WordTrace tailWord_1436136 prefixEnd_1436136 491618702150332229996891 := by
  unfold tailWord_1436136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26190091562566009673384131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34920122083421346231178841 26190091562566009673384131)
  ·
    refine ⟨39285137343849014510076197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26190091562566009673384131 39285137343849014510076197)
    ·
      refine ⟨7365963251971690220639287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39285137343849014510076197 7365963251971690220639287)
      ·
        refine ⟨11048944877957535330958931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365963251971690220639287 11048944877957535330958931)
        ·
          refine ⟨16573417316936302996438397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11048944877957535330958931 16573417316936302996438397)
          ·
            refine ⟨6215031493851113623664399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16573417316936302996438397 6215031493851113623664399)
            ·
              refine ⟨9322547240776670435496599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215031493851113623664399 9322547240776670435496599)
              ·
                refine ⟨13983820861165005653244899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322547240776670435496599 13983820861165005653244899)
                ·
                  refine ⟨20975731291747508479867349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13983820861165005653244899 20975731291747508479867349)
                  ·
                    refine ⟨491618702150332229996891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20975731291747508479867349 491618702150332229996891)
                    ·
                      rfl

theorem cell22_1436136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1436136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436136 prefixEnd_1436136 := by exact prefixLift 1436136
  have htrace : WordTrace (prefixWord ++ tailWord_1436136) baseStart_1436136 baseEnd_1436136 := by
    simpa [prefixWord, tailWord_1436136, baseEnd_1436136] using wordTrace_append hprefix tailTrace_1436136
  have hstable : (prefixWord ++ tailWord_1436136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436136).length < 2 ^ (prefixWord ++ tailWord_1436136).sum := by decide
  have hdescent : baseEnd_1436136 < baseStart_1436136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436138 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_1436138 : Nat := 118140960795 + 1436138 * 2 ^ 59
def prefixEnd_1436138 : Nat := 4983230072969 + 3 ^ 40 * 1436138 * 2
def baseEnd_1436138 : Nat := 163873128930401630482295

theorem tailTrace_1436138 : CollatzResearch.WordTrace tailWord_1436138 prefixEnd_1436138 163873128930401630482295 := by
  unfold tailWord_1436138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13095064017781193422085267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34920170714083182458894045 13095064017781193422085267)
  ·
    refine ⟨19642596026671790133127901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13095064017781193422085267 19642596026671790133127901)
    ·
      refine ⟨7365973510001921299922963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19642596026671790133127901 7365973510001921299922963)
      ·
        refine ⟨11048960265002881949884445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365973510001921299922963 11048960265002881949884445)
        ·
          refine ⟨4143360099376080731206667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11048960265002881949884445 4143360099376080731206667)
          ·
            refine ⟨6215040149064121096810001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143360099376080731206667 6215040149064121096810001)
            ·
              refine ⟨4661280111798090822607501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215040149064121096810001 4661280111798090822607501)
              ·
                refine ⟨1747980041924284058477813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4661280111798090822607501 1747980041924284058477813)
                ·
                  refine ⟨163873128930401630482295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747980041924284058477813 163873128930401630482295)
                  ·
                    rfl

theorem cell22_1436138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_1436138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436138 prefixEnd_1436138 := by exact prefixLift 1436138
  have htrace : WordTrace (prefixWord ++ tailWord_1436138) baseStart_1436138 baseEnd_1436138 := by
    simpa [prefixWord, tailWord_1436138, baseEnd_1436138] using wordTrace_append hprefix tailTrace_1436138
  have hstable : (prefixWord ++ tailWord_1436138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436138).length < 2 ^ (prefixWord ++ tailWord_1436138).sum := by decide
  have hdescent : baseEnd_1436138 < baseStart_1436138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436211 : List Nat := [1, 1, 1, 2, 4, 2, 3, 8]
def baseStart_1436211 : Nat := 118140960795 + 1436211 * 2 ^ 59
def prefixEnd_1436211 : Nat := 4983230072969 + 3 ^ 40 * 1436211 * 2
def baseEnd_1436211 : Nat := 54627152909228559374629

theorem tailTrace_1436211 : CollatzResearch.WordTrace tailWord_1436211 prefixEnd_1436211 54627152909228559374629 := by
  unfold tailWord_1436211
  simp only [CollatzResearch.WordTrace]
  refine ⟨52382918599860307155748487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34921945733240204770498991 52382918599860307155748487)
  ·
    refine ⟨78574377899790460733622731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52382918599860307155748487 78574377899790460733622731)
    ·
      refine ⟨117861566849685691100434097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78574377899790460733622731 117861566849685691100434097)
      ·
        refine ⟨88396175137264268325325573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117861566849685691100434097 88396175137264268325325573)
        ·
          refine ⟨16574282838237050310998545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88396175137264268325325573 16574282838237050310998545)
          ·
            refine ⟨12430712128677787733248909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16574282838237050310998545 12430712128677787733248909)
            ·
              refine ⟨4661517048254170399968341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12430712128677787733248909 4661517048254170399968341)
              ·
                refine ⟨54627152909228559374629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4661517048254170399968341 54627152909228559374629)
                ·
                  rfl

theorem cell22_1436211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 8].length) (baseStart_1436211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436211 prefixEnd_1436211 := by exact prefixLift 1436211
  have htrace : WordTrace (prefixWord ++ tailWord_1436211) baseStart_1436211 baseEnd_1436211 := by
    simpa [prefixWord, tailWord_1436211, baseEnd_1436211] using wordTrace_append hprefix tailTrace_1436211
  have hstable : (prefixWord ++ tailWord_1436211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436211).length < 2 ^ (prefixWord ++ tailWord_1436211).sum := by decide
  have hdescent : baseEnd_1436211 < baseStart_1436211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436213 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1436213 : Nat := 118140960795 + 1436213 * 2 ^ 59
def prefixEnd_1436213 : Nat := 4983230072969 + 3 ^ 40 * 1436213 * 2
def baseEnd_1436213 : Nat := 491645060823929695821655

theorem tailTrace_1436213 : CollatzResearch.WordTrace tailWord_1436213 prefixEnd_1436213 491645060823929695821655 := by
  unfold tailWord_1436213
  simp only [CollatzResearch.WordTrace]
  refine ⟨52382991545853061497321293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34921994363902040998214195 52382991545853061497321293)
  ·
    refine ⟨19643621829694898061495485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52382991545853061497321293 19643621829694898061495485)
    ·
      refine ⟨7366358186135586773060807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19643621829694898061495485 7366358186135586773060807)
      ·
        refine ⟨11049537279203380159591211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7366358186135586773060807 11049537279203380159591211)
        ·
          refine ⟨16574305918805070239386817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11049537279203380159591211 16574305918805070239386817)
          ·
            refine ⟨12430729439103802679540113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16574305918805070239386817 12430729439103802679540113)
            ·
              refine ⟨9323047079327852009655085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12430729439103802679540113 9323047079327852009655085)
              ·
                refine ⟨3496142654747944503620657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9323047079327852009655085 3496142654747944503620657)
                ·
                  refine ⟨2622106991060958377715493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3496142654747944503620657 2622106991060958377715493)
                  ·
                    refine ⟨491645060823929695821655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622106991060958377715493 491645060823929695821655)
                    ·
                      rfl

theorem cell22_1436213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1436213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436213 prefixEnd_1436213 := by exact prefixLift 1436213
  have htrace : WordTrace (prefixWord ++ tailWord_1436213) baseStart_1436213 baseEnd_1436213 := by
    simpa [prefixWord, tailWord_1436213, baseEnd_1436213] using wordTrace_append hprefix tailTrace_1436213
  have hstable : (prefixWord ++ tailWord_1436213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436213).length < 2 ^ (prefixWord ++ tailWord_1436213).sum := by decide
  have hdescent : baseEnd_1436213 < baseStart_1436213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436335 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 4]
def baseStart_1436335 : Nat := 118140960795 + 1436335 * 2 ^ 59
def prefixEnd_1436335 : Nat := 4983230072969 + 3 ^ 40 * 1436335 * 2
def baseEnd_1436335 : Nat := 163895607972387348090427

theorem tailTrace_1436335 : CollatzResearch.WordTrace tailWord_1436335 prefixEnd_1436335 163895607972387348090427 := by
  unfold tailWord_1436335
  simp only [CollatzResearch.WordTrace]
  refine ⟨52387441251411076333262459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34924960834274050888841639 52387441251411076333262459)
  ·
    refine ⟨78581161877116614499893689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52387441251411076333262459 78581161877116614499893689)
    ·
      refine ⟨58935871407837460874920267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78581161877116614499893689 58935871407837460874920267)
      ·
        refine ⟨88403807111756191312380401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58935871407837460874920267 88403807111756191312380401)
        ·
          refine ⟨66302855333817143484285301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88403807111756191312380401 66302855333817143484285301)
          ·
            refine ⟨6215892687545357201651747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66302855333817143484285301 6215892687545357201651747)
            ·
              refine ⟨9323839031318035802477621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215892687545357201651747 9323839031318035802477621)
              ·
                refine ⟨874109909186065856482277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9323839031318035802477621 874109909186065856482277)
                ·
                  refine ⟨163895607972387348090427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874109909186065856482277 163895607972387348090427)
                  ·
                    rfl

theorem cell22_1436335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 4].length) (baseStart_1436335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436335 prefixEnd_1436335 := by exact prefixLift 1436335
  have htrace : WordTrace (prefixWord ++ tailWord_1436335) baseStart_1436335 baseEnd_1436335 := by
    simpa [prefixWord, tailWord_1436335, baseEnd_1436335] using wordTrace_append hprefix tailTrace_1436335
  have hstable : (prefixWord ++ tailWord_1436335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436335).length < 2 ^ (prefixWord ++ tailWord_1436335).sum := by decide
  have hdescent : baseEnd_1436335 < baseStart_1436335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436378 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_1436378 : Nat := 118140960795 + 1436378 * 2 ^ 59
def prefixEnd_1436378 : Nat := 4983230072969 + 3 ^ 40 * 1436378 * 2
def baseEnd_1436378 : Nat := 491701543695924265446149

theorem tailTrace_1436378 : CollatzResearch.WordTrace tailWord_1436378 prefixEnd_1436378 491701543695924265446149 := by
  unfold tailWord_1436378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097252397563823669269447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34926006393503529784718525 13097252397563823669269447)
  ·
    refine ⟨19645878596345735503904171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13097252397563823669269447 19645878596345735503904171)
    ·
      refine ⟨29468817894518603255856257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19645878596345735503904171 29468817894518603255856257)
      ·
        refine ⟨22101613420888952441892193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29468817894518603255856257 22101613420888952441892193)
        ·
          refine ⟨16576210065666714331419145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22101613420888952441892193 16576210065666714331419145)
          ·
            refine ⟨12432157549250035748564359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16576210065666714331419145 12432157549250035748564359)
            ·
              refine ⟨18648236323875053622846539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12432157549250035748564359 18648236323875053622846539)
              ·
                refine ⟨27972354485812580434269809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18648236323875053622846539 27972354485812580434269809)
                ·
                  refine ⟨20979265864359435325702357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27972354485812580434269809 20979265864359435325702357)
                  ·
                    refine ⟨491701543695924265446149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20979265864359435325702357 491701543695924265446149)
                    ·
                      rfl

theorem cell22_1436378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_1436378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436378 prefixEnd_1436378 := by exact prefixLift 1436378
  have htrace : WordTrace (prefixWord ++ tailWord_1436378) baseStart_1436378 baseEnd_1436378 := by
    simpa [prefixWord, tailWord_1436378, baseEnd_1436378] using wordTrace_append hprefix tailTrace_1436378
  have hstable : (prefixWord ++ tailWord_1436378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436378).length < 2 ^ (prefixWord ++ tailWord_1436378).sum := by decide
  have hdescent : baseEnd_1436378 < baseStart_1436378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436408 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_1436408 : Nat := 118140960795 + 1436408 * 2 ^ 59
def prefixEnd_1436408 : Nat := 4983230072969 + 3 ^ 40 * 1436408 * 2
def baseEnd_1436408 : Nat := 163903937769671395732019

theorem tailTrace_1436408 : CollatzResearch.WordTrace tailWord_1436408 prefixEnd_1436408 163903937769671395732019 := by
  unfold tailWord_1436408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26195051890073304900334939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34926735853431073200446585 26195051890073304900334939)
  ·
    refine ⟨39292577835109957350502409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26195051890073304900334939 39292577835109957350502409)
    ·
      refine ⟨29469433376332468012876807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39292577835109957350502409 29469433376332468012876807)
      ·
        refine ⟨44204150064498702019315211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29469433376332468012876807 44204150064498702019315211)
        ·
          refine ⟨66306225096748053028972817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44204150064498702019315211 66306225096748053028972817)
          ·
            refine ⟨49729668822561039771729613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66306225096748053028972817 49729668822561039771729613)
            ·
              refine ⟨18648625808460389914398605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49729668822561039771729613 18648625808460389914398605)
              ·
                refine ⟨6993234678172646217899477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18648625808460389914398605 6993234678172646217899477)
                ·
                  refine ⟨163903937769671395732019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6993234678172646217899477 163903937769671395732019)
                  ·
                    rfl

theorem cell22_1436408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_1436408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436408 prefixEnd_1436408 := by exact prefixLift 1436408
  have htrace : WordTrace (prefixWord ++ tailWord_1436408) baseStart_1436408 baseEnd_1436408 := by
    simpa [prefixWord, tailWord_1436408, baseEnd_1436408] using wordTrace_append hprefix tailTrace_1436408
  have hstable : (prefixWord ++ tailWord_1436408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436408).length < 2 ^ (prefixWord ++ tailWord_1436408).sum := by decide
  have hdescent : baseEnd_1436408 < baseStart_1436408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436412 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1436412 : Nat := 118140960795 + 1436412 * 2 ^ 59
def prefixEnd_1436412 : Nat := 4983230072969 + 3 ^ 40 * 1436412 * 2
def baseEnd_1436412 : Nat := 491713182590759510096045

theorem tailTrace_1436412 : CollatzResearch.WordTrace tailWord_1436412 prefixEnd_1436412 491713182590759510096045 := by
  unfold tailWord_1436412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26195124836066059241907745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34926833114754745655876993 26195124836066059241907745)
  ·
    refine ⟨19646343627049544431430809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26195124836066059241907745 19646343627049544431430809)
    ·
      refine ⟨14734757720287158323573107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19646343627049544431430809 14734757720287158323573107)
      ·
        refine ⟨22102136580430737485359661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14734757720287158323573107 22102136580430737485359661)
        ·
          refine ⟨8288301217661526557009873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22102136580430737485359661 8288301217661526557009873)
          ·
            refine ⟨6216225913246144917757405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8288301217661526557009873 6216225913246144917757405)
            ·
              refine ⟨2331084717467304344159027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6216225913246144917757405 2331084717467304344159027)
              ·
                refine ⟨3496627076200956516238541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331084717467304344159027 3496627076200956516238541)
                ·
                  refine ⟨1311235153575358693589453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496627076200956516238541 1311235153575358693589453)
                  ·
                    refine ⟨491713182590759510096045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1311235153575358693589453 491713182590759510096045)
                    ·
                      rfl

theorem cell22_1436412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1436412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436412 prefixEnd_1436412 := by exact prefixLift 1436412
  have htrace : WordTrace (prefixWord ++ tailWord_1436412) baseStart_1436412 baseEnd_1436412 := by
    simpa [prefixWord, tailWord_1436412, baseEnd_1436412] using wordTrace_append hprefix tailTrace_1436412
  have hstable : (prefixWord ++ tailWord_1436412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436412).length < 2 ^ (prefixWord ++ tailWord_1436412).sum := by decide
  have hdescent : baseEnd_1436412 < baseStart_1436412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436515 : List Nat := [1, 1, 1, 5, 3, 2, 9]
def baseStart_1436515 : Nat := 118140960795 + 1436515 * 2 ^ 59
def prefixEnd_1436515 : Nat := 4983230072969 + 3 ^ 40 * 1436515 * 2
def baseEnd_1436515 : Nat := 18212905244285243510027

theorem tailTrace_1436515 : CollatzResearch.WordTrace tailWord_1436515 prefixEnd_1436515 18212905244285243510027 := by
  unfold tailWord_1436515
  simp only [CollatzResearch.WordTrace]
  refine ⟨52394006390758967074814999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34929337593839311383209999 52394006390758967074814999)
  ·
    refine ⟨78591009586138450612222499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52394006390758967074814999 78591009586138450612222499)
    ·
      refine ⟨117886514379207675918333749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78591009586138450612222499 117886514379207675918333749)
      ·
        refine ⟨11051860723050719617343789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117886514379207675918333749 11051860723050719617343789)
        ·
          refine ⟨4144447771144019856503921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11051860723050719617343789 4144447771144019856503921)
          ·
            refine ⟨3108335828358014892377941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144447771144019856503921 3108335828358014892377941)
            ·
              refine ⟨18212905244285243510027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3108335828358014892377941 18212905244285243510027)
              ·
                rfl

theorem cell22_1436515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 9].length) (baseStart_1436515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436515 prefixEnd_1436515 := by exact prefixLift 1436515
  have htrace : WordTrace (prefixWord ++ tailWord_1436515) baseStart_1436515 baseEnd_1436515 := by
    simpa [prefixWord, tailWord_1436515, baseEnd_1436515] using wordTrace_append hprefix tailTrace_1436515
  have hstable : (prefixWord ++ tailWord_1436515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436515).length < 2 ^ (prefixWord ++ tailWord_1436515).sum := by decide
  have hdescent : baseEnd_1436515 < baseStart_1436515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436519 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1436519 : Nat := 118140960795 + 1436519 * 2 ^ 59
def prefixEnd_1436519 : Nat := 4983230072969 + 3 ^ 40 * 1436519 * 2
def baseEnd_1436519 : Nat := 491749810877446897670717

theorem tailTrace_1436519 : CollatzResearch.WordTrace tailWord_1436519 prefixEnd_1436519 491749810877446897670717 := by
  unfold tailWord_1436519
  simp only [CollatzResearch.WordTrace]
  refine ⟨52394152282744475757960611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34929434855162983838640407 52394152282744475757960611)
  ·
    refine ⟨78591228424116713636940917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52394152282744475757960611 78591228424116713636940917)
    ·
      refine ⟨7367927664760941903463211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78591228424116713636940917 7367927664760941903463211)
      ·
        refine ⟨11051891497141412855194817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367927664760941903463211 11051891497141412855194817)
        ·
          refine ⟨8288918622856059641396113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11051891497141412855194817 8288918622856059641396113)
          ·
            refine ⟨6216688967142044731047085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8288918622856059641396113 6216688967142044731047085)
            ·
              refine ⟨2331258362678266774142657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6216688967142044731047085 2331258362678266774142657)
              ·
                refine ⟨1748443772008700080606993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331258362678266774142657 1748443772008700080606993)
                ·
                  refine ⟨1311332829006525060455245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748443772008700080606993 1311332829006525060455245)
                  ·
                    refine ⟨491749810877446897670717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1311332829006525060455245 491749810877446897670717)
                    ·
                      rfl

theorem cell22_1436519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1436519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436519 prefixEnd_1436519 := by exact prefixLift 1436519
  have htrace : WordTrace (prefixWord ++ tailWord_1436519) baseStart_1436519 baseEnd_1436519 := by
    simpa [prefixWord, tailWord_1436519, baseEnd_1436519] using wordTrace_append hprefix tailTrace_1436519
  have hstable : (prefixWord ++ tailWord_1436519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436519).length < 2 ^ (prefixWord ++ tailWord_1436519).sum := by decide
  have hdescent : baseEnd_1436519 < baseStart_1436519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436547 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 3, 3]
def baseStart_1436547 : Nat := 118140960795 + 1436547 * 2 ^ 59
def prefixEnd_1436547 : Nat := 4983230072969 + 3 ^ 40 * 1436547 * 2
def baseEnd_1436547 : Nat := 491759395849664157970631

theorem tailTrace_1436547 : CollatzResearch.WordTrace tailWord_1436547 prefixEnd_1436547 491759395849664157970631 := by
  unfold tailWord_1436547
  simp only [CollatzResearch.WordTrace]
  refine ⟨52395173526643036539979895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34930115684428691026653263 52395173526643036539979895)
  ·
    refine ⟨78592760289964554809969843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52395173526643036539979895 78592760289964554809969843)
    ·
      refine ⟨117889140434946832214954765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78592760289964554809969843 117889140434946832214954765)
      ·
        refine ⟨44208427663105062080608037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117889140434946832214954765 44208427663105062080608037)
        ·
          refine ⟨8289080186832199140114007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44208427663105062080608037 8289080186832199140114007)
          ·
            refine ⟨12433620280248298710171011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289080186832199140114007 12433620280248298710171011)
            ·
              refine ⟨18650430420372448065256517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12433620280248298710171011 18650430420372448065256517)
              ·
                refine ⟨3496955703819834012235597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18650430420372448065256517 3496955703819834012235597)
                ·
                  refine ⟨1311358388932437754588349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496955703819834012235597 1311358388932437754588349)
                  ·
                    refine ⟨491759395849664157970631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1311358388932437754588349 491759395849664157970631)
                    ·
                      rfl

theorem cell22_1436547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3].length) (baseStart_1436547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436547 prefixEnd_1436547 := by exact prefixLift 1436547
  have htrace : WordTrace (prefixWord ++ tailWord_1436547) baseStart_1436547 baseEnd_1436547 := by
    simpa [prefixWord, tailWord_1436547, baseEnd_1436547] using wordTrace_append hprefix tailTrace_1436547
  have hstable : (prefixWord ++ tailWord_1436547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436547).length < 2 ^ (prefixWord ++ tailWord_1436547).sum := by decide
  have hdescent : baseEnd_1436547 < baseStart_1436547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436566 : List Nat := [5, 3, 1, 1, 1, 3, 8]
def baseStart_1436566 : Nat := 118140960795 + 1436566 * 2 ^ 59
def prefixEnd_1436566 : Nat := 4983230072969 + 3 ^ 40 * 1436566 * 2
def baseEnd_1436566 : Nat := 18213551849553868212799

theorem tailTrace_1436566 : CollatzResearch.WordTrace tailWord_1436566 prefixEnd_1436566 18213551849553868212799 := by
  unfold tailWord_1436566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274741657098387674057597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34930577675716135189947701 3274741657098387674057597)
  ·
    refine ⟨1228028121411895377771599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3274741657098387674057597 1228028121411895377771599)
    ·
      refine ⟨1842042182117843066657399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228028121411895377771599 1842042182117843066657399)
      ·
        refine ⟨2763063273176764599986099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842042182117843066657399 2763063273176764599986099)
        ·
          refine ⟨4144594909765146899979149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763063273176764599986099 4144594909765146899979149)
          ·
            refine ⟨1554223091161930087492181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4144594909765146899979149 1554223091161930087492181)
            ·
              refine ⟨18213551849553868212799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1554223091161930087492181 18213551849553868212799)
              ·
                rfl

theorem cell22_1436566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 8].length) (baseStart_1436566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436566 prefixEnd_1436566 := by exact prefixLift 1436566
  have htrace : WordTrace (prefixWord ++ tailWord_1436566) baseStart_1436566 baseEnd_1436566 := by
    simpa [prefixWord, tailWord_1436566, baseEnd_1436566] using wordTrace_append hprefix tailTrace_1436566
  have hstable : (prefixWord ++ tailWord_1436566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436566).length < 2 ^ (prefixWord ++ tailWord_1436566).sum := by decide
  have hdescent : baseEnd_1436566 < baseStart_1436566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436577 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 7]
def baseStart_1436577 : Nat := 118140960795 + 1436577 * 2 ^ 59
def prefixEnd_1436577 : Nat := 4983230072969 + 3 ^ 40 * 1436577 * 2
def baseEnd_1436577 : Nat := 163923221820918026573513

theorem tailTrace_1436577 : CollatzResearch.WordTrace tailWord_1436577 prefixEnd_1436577 163923221820918026573513 := by
  unfold tailWord_1436577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52396267716534351663571985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34930845144356234442381323 52396267716534351663571985)
  ·
    refine ⟨39297200787400763747678989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52396267716534351663571985 39297200787400763747678989)
    ·
      refine ⟨14736450295275286405379621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39297200787400763747678989 14736450295275286405379621)
      ·
        refine ⟨2763084430364116201008679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14736450295275286405379621 2763084430364116201008679)
        ·
          refine ⟨4144626645546174301513019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763084430364116201008679 4144626645546174301513019)
          ·
            refine ⟨6216939968319261452269529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4144626645546174301513019 6216939968319261452269529)
            ·
              refine ⟨4662704976239446089202147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6216939968319261452269529 4662704976239446089202147)
              ·
                refine ⟨6994057464359169133803221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662704976239446089202147 6994057464359169133803221)
                ·
                  refine ⟨163923221820918026573513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6994057464359169133803221 163923221820918026573513)
                  ·
                    rfl

theorem cell22_1436577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_1436577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436577 prefixEnd_1436577 := by exact prefixLift 1436577
  have htrace : WordTrace (prefixWord ++ tailWord_1436577) baseStart_1436577 baseEnd_1436577 := by
    simpa [prefixWord, tailWord_1436577, baseEnd_1436577] using wordTrace_append hprefix tailTrace_1436577
  have hstable : (prefixWord ++ tailWord_1436577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436577).length < 2 ^ (prefixWord ++ tailWord_1436577).sum := by decide
  have hdescent : baseEnd_1436577 < baseStart_1436577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436607 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 1, 4]
def baseStart_1436607 : Nat := 118140960795 + 1436607 * 2 ^ 59
def prefixEnd_1436607 : Nat := 4983230072969 + 3 ^ 40 * 1436607 * 2
def baseEnd_1436607 : Nat := 491779935075844001470447

theorem tailTrace_1436607 : CollatzResearch.WordTrace tailWord_1436607 prefixEnd_1436607 491779935075844001470447 := by
  unfold tailWord_1436607
  simp only [CollatzResearch.WordTrace]
  refine ⟨52397361906425666787164075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34931574604283777858109383 52397361906425666787164075)
  ·
    refine ⟨78596042859638500180746113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52397361906425666787164075 78596042859638500180746113)
    ·
      refine ⟨58947032144728875135559585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78596042859638500180746113 58947032144728875135559585)
      ·
        refine ⟨44210274108546656351669689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58947032144728875135559585 44210274108546656351669689)
        ·
          refine ⟨33157705581409992263752267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44210274108546656351669689 33157705581409992263752267)
          ·
            refine ⟨49736558372114988395628401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33157705581409992263752267 49736558372114988395628401)
            ·
              refine ⟨37302418779086241296721301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49736558372114988395628401 37302418779086241296721301)
              ·
                refine ⟨1748550880269667560783811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37302418779086241296721301 1748550880269667560783811)
                ·
                  refine ⟨2622826320404501341175717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748550880269667560783811 2622826320404501341175717)
                  ·
                    refine ⟨491779935075844001470447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622826320404501341175717 491779935075844001470447)
                    ·
                      rfl

theorem cell22_1436607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_1436607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436607 prefixEnd_1436607 := by exact prefixLift 1436607
  have htrace : WordTrace (prefixWord ++ tailWord_1436607) baseStart_1436607 baseEnd_1436607 := by
    simpa [prefixWord, tailWord_1436607, baseEnd_1436607] using wordTrace_append hprefix tailTrace_1436607
  have hstable : (prefixWord ++ tailWord_1436607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436607).length < 2 ^ (prefixWord ++ tailWord_1436607).sum := by decide
  have hdescent : baseEnd_1436607 < baseStart_1436607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436733 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1436733 : Nat := 118140960795 + 1436733 * 2 ^ 59
def prefixEnd_1436733 : Nat := 4983230072969 + 3 ^ 40 * 1436733 * 2
def baseEnd_1436733 : Nat := 491823067450821672820061

theorem tailTrace_1436733 : CollatzResearch.WordTrace tailWord_1436733 prefixEnd_1436733 491823067450821672820061 := by
  unfold tailWord_1436733
  simp only [CollatzResearch.WordTrace]
  refine ⟨52401957503969190306250853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34934638335979460204167235 52401957503969190306250853)
  ·
    refine ⟨9825367031994223182422035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52401957503969190306250853 9825367031994223182422035)
    ·
      refine ⟨14738050547991334773633053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9825367031994223182422035 14738050547991334773633053)
      ·
        refine ⟨5526768955496750540112395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14738050547991334773633053 5526768955496750540112395)
        ·
          refine ⟨8290153433245125810168593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526768955496750540112395 8290153433245125810168593)
          ·
            refine ⟨6217615074933844357626445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8290153433245125810168593 6217615074933844357626445)
            ·
              refine ⟨2331605653100191634109917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6217615074933844357626445 2331605653100191634109917)
              ·
                refine ⟨874352119912571862791219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2331605653100191634109917 874352119912571862791219)
                ·
                  refine ⟨1311528179868857794186829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874352119912571862791219 1311528179868857794186829)
                  ·
                    refine ⟨491823067450821672820061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1311528179868857794186829 491823067450821672820061)
                    ·
                      rfl

theorem cell22_1436733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1436733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436733 prefixEnd_1436733 := by exact prefixLift 1436733
  have htrace : WordTrace (prefixWord ++ tailWord_1436733) baseStart_1436733 baseEnd_1436733 := by
    simpa [prefixWord, tailWord_1436733, baseEnd_1436733] using wordTrace_append hprefix tailTrace_1436733
  have hstable : (prefixWord ++ tailWord_1436733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436733).length < 2 ^ (prefixWord ++ tailWord_1436733).sum := by decide
  have hdescent : baseEnd_1436733 < baseStart_1436733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436793 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_1436793 : Nat := 118140960795 + 1436793 * 2 ^ 59
def prefixEnd_1436793 : Nat := 4983230072969 + 3 ^ 40 * 1436793 * 2
def baseEnd_1436793 : Nat := 491843606677001516319877

theorem tailTrace_1436793 : CollatzResearch.WordTrace tailWord_1436793 prefixEnd_1436793 491843606677001516319877 := by
  unfold tailWord_1436793
  simp only [CollatzResearch.WordTrace]
  refine ⟨52404145883751820553435033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34936097255834547035623355 52404145883751820553435033)
  ·
    refine ⟨39303109412813865415076275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52404145883751820553435033 39303109412813865415076275)
    ·
      refine ⟨58954664119220798122614413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39303109412813865415076275 58954664119220798122614413)
      ·
        refine ⟨22107999044707799295980405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58954664119220798122614413 22107999044707799295980405)
        ·
          refine ⟨2072624910441356183998163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22107999044707799295980405 2072624910441356183998163)
          ·
            refine ⟨3108937365662034275997245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072624910441356183998163 3108937365662034275997245)
            ·
              refine ⟨1165851512123262853498967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3108937365662034275997245 1165851512123262853498967)
              ·
                refine ⟨1748777268184894280248451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165851512123262853498967 1748777268184894280248451)
                ·
                  refine ⟨2623165902277341420372677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748777268184894280248451 2623165902277341420372677)
                  ·
                    refine ⟨491843606677001516319877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2623165902277341420372677 491843606677001516319877)
                    ·
                      rfl

theorem cell22_1436793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_1436793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436793 prefixEnd_1436793 := by exact prefixLift 1436793
  have htrace : WordTrace (prefixWord ++ tailWord_1436793) baseStart_1436793 baseEnd_1436793 := by
    simpa [prefixWord, tailWord_1436793, baseEnd_1436793] using wordTrace_append hprefix tailTrace_1436793
  have hstable : (prefixWord ++ tailWord_1436793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436793).length < 2 ^ (prefixWord ++ tailWord_1436793).sum := by decide
  have hdescent : baseEnd_1436793 < baseStart_1436793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436808 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_1436808 : Nat := 118140960795 + 1436808 * 2 ^ 59
def prefixEnd_1436808 : Nat := 4983230072969 + 3 ^ 40 * 1436808 * 2
def baseEnd_1436808 : Nat := 163949580494515492398277

theorem tailTrace_1436808 : CollatzResearch.WordTrace tailWord_1436808 prefixEnd_1436808 163949580494515492398277 := by
  unfold tailWord_1436808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202346489348739057615539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34936461985798318743487385 26202346489348739057615539)
  ·
    refine ⟨39303519734023108586423309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26202346489348739057615539 39303519734023108586423309)
    ·
      refine ⟨14738819900258665719908741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39303519734023108586423309 14738819900258665719908741)
      ·
        refine ⟨2763528731298499822482889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14738819900258665719908741 2763528731298499822482889)
        ·
          refine ⟨2072646548473874866862167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2763528731298499822482889 2072646548473874866862167)
          ·
            refine ⟨3108969822710812300293251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072646548473874866862167 3108969822710812300293251)
            ·
              refine ⟨4663454734066218450439877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108969822710812300293251 4663454734066218450439877)
              ·
                refine ⟨874397762637415959457477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4663454734066218450439877 874397762637415959457477)
                ·
                  refine ⟨163949580494515492398277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874397762637415959457477 163949580494515492398277)
                  ·
                    rfl

theorem cell22_1436808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_1436808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436808 prefixEnd_1436808 := by exact prefixLift 1436808
  have htrace : WordTrace (prefixWord ++ tailWord_1436808) baseStart_1436808 baseEnd_1436808 := by
    simpa [prefixWord, tailWord_1436808, baseEnd_1436808] using wordTrace_append hprefix tailTrace_1436808
  have hstable : (prefixWord ++ tailWord_1436808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436808).length < 2 ^ (prefixWord ++ tailWord_1436808).sum := by decide
  have hdescent : baseEnd_1436808 < baseStart_1436808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436836 : List Nat := [2, 3, 1, 2, 3, 2, 3, 6]
def baseStart_1436836 : Nat := 118140960795 + 1436836 * 2 ^ 59
def prefixEnd_1436836 : Nat := 4983230072969 + 3 ^ 40 * 1436836 * 2
def baseEnd_1436836 : Nat := 54650925161751526388305

theorem tailTrace_1436836 : CollatzResearch.WordTrace tailWord_1436836 prefixEnd_1436836 54650925161751526388305 := by
  unfold tailWord_1436836
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202857111298019448625181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34937142815064025931500241 26202857111298019448625181)
  ·
    refine ⟨9826071416736757293234443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26202857111298019448625181 9826071416736757293234443)
    ·
      refine ⟨14739107125105135939851665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826071416736757293234443 14739107125105135939851665)
      ·
        refine ⟨11054330343828851954888749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14739107125105135939851665 11054330343828851954888749)
        ·
          refine ⟨4145373878935819483083281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11054330343828851954888749 4145373878935819483083281)
          ·
            refine ⟨3109030409201864612312461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145373878935819483083281 3109030409201864612312461)
            ·
              refine ⟨1165886403450699229617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3109030409201864612312461 1165886403450699229617173)
              ·
                refine ⟨54650925161751526388305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1165886403450699229617173 54650925161751526388305)
                ·
                  rfl

theorem cell22_1436836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_1436836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436836 prefixEnd_1436836 := by exact prefixLift 1436836
  have htrace : WordTrace (prefixWord ++ tailWord_1436836) baseStart_1436836 baseEnd_1436836 := by
    simpa [prefixWord, tailWord_1436836, baseEnd_1436836] using wordTrace_append hprefix tailTrace_1436836
  have hstable : (prefixWord ++ tailWord_1436836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436836).length < 2 ^ (prefixWord ++ tailWord_1436836).sum := by decide
  have hdescent : baseEnd_1436836 < baseStart_1436836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436956 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1436956 : Nat := 118140960795 + 1436956 * 2 ^ 59
def prefixEnd_1436956 : Nat := 4983230072969 + 3 ^ 40 * 1436956 * 2
def baseEnd_1436956 : Nat := 491899404908123424494377

theorem tailTrace_1436956 : CollatzResearch.WordTrace tailWord_1436956 prefixEnd_1436956 491899404908123424494377 := by
  unfold tailWord_1436956
  simp only [CollatzResearch.WordTrace]
  refine ⟨26205045491080649695809361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34940060654774199594412481 26205045491080649695809361)
  ·
    refine ⟨19653784118310487271857021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26205045491080649695809361 19653784118310487271857021)
    ·
      refine ⟨7370169044366432726946383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19653784118310487271857021 7370169044366432726946383)
      ·
        refine ⟨11055253566549649090419575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370169044366432726946383 11055253566549649090419575)
        ·
          refine ⟨16582880349824473635629363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055253566549649090419575 16582880349824473635629363)
          ·
            refine ⟨24874320524736710453444045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582880349824473635629363 24874320524736710453444045)
            ·
              refine ⟨9327870196776266420041517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24874320524736710453444045 9327870196776266420041517)
              ·
                refine ⟨3497951323791099907515569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327870196776266420041517 3497951323791099907515569)
                ·
                  refine ⟨2623463492843324930636677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497951323791099907515569 2623463492843324930636677)
                  ·
                    refine ⟨491899404908123424494377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2623463492843324930636677 491899404908123424494377)
                    ·
                      rfl

theorem cell22_1436956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1436956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1436956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1436956 prefixEnd_1436956 := by exact prefixLift 1436956
  have htrace : WordTrace (prefixWord ++ tailWord_1436956) baseStart_1436956 baseEnd_1436956 := by
    simpa [prefixWord, tailWord_1436956, baseEnd_1436956] using wordTrace_append hprefix tailTrace_1436956
  have hstable : (prefixWord ++ tailWord_1436956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436956).length < 2 ^ (prefixWord ++ tailWord_1436956).sum := by decide
  have hdescent : baseEnd_1436956 < baseStart_1436956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437061 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 6]
def baseStart_1437061 : Nat := 118140960795 + 1437061 * 2 ^ 59
def prefixEnd_1437061 : Nat := 4983230072969 + 3 ^ 40 * 1437061 * 2
def baseEnd_1437061 : Nat := 163978449517979383539685

theorem tailTrace_1437061 : CollatzResearch.WordTrace tailWord_1437061 prefixEnd_1437061 163978449517979383539685 := by
  unfold tailWord_1437061
  simp only [CollatzResearch.WordTrace]
  refine ⟨52413920646780902324191037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34942613764520601549460691 52413920646780902324191037)
  ·
    refine ⟨19655220242542838371571639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52413920646780902324191037 19655220242542838371571639)
    ·
      refine ⟨29482830363814257557357459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655220242542838371571639 29482830363814257557357459)
      ·
        refine ⟨44224245545721386336036189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29482830363814257557357459 44224245545721386336036189)
        ·
          refine ⟨16584092079645519876013571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44224245545721386336036189 16584092079645519876013571)
          ·
            refine ⟨24876138119468279814020357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16584092079645519876013571 24876138119468279814020357)
            ·
              refine ⟨4664275897400302465128817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24876138119468279814020357 4664275897400302465128817)
              ·
                refine ⟨3498206923050226848846613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4664275897400302465128817 3498206923050226848846613)
                ·
                  refine ⟨163978449517979383539685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3498206923050226848846613 163978449517979383539685)
                  ·
                    rfl

theorem cell22_1437061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_1437061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437061 prefixEnd_1437061 := by exact prefixLift 1437061
  have htrace : WordTrace (prefixWord ++ tailWord_1437061) baseStart_1437061 baseEnd_1437061 := by
    simpa [prefixWord, tailWord_1437061, baseEnd_1437061] using wordTrace_append hprefix tailTrace_1437061
  have hstable : (prefixWord ++ tailWord_1437061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437061).length < 2 ^ (prefixWord ++ tailWord_1437061).sum := by decide
  have hdescent : baseEnd_1437061 < baseStart_1437061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437063 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1437063 : Nat := 118140960795 + 1437063 * 2 ^ 59
def prefixEnd_1437063 : Nat := 4983230072969 + 3 ^ 40 * 1437063 * 2
def baseEnd_1437063 : Nat := 491936033194810812069049

theorem tailTrace_1437063 : CollatzResearch.WordTrace tailWord_1437063 prefixEnd_1437063 491936033194810812069049 := by
  unfold tailWord_1437063
  simp only [CollatzResearch.WordTrace]
  refine ⟨52413993592773656665763843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34942662395182437777175895 52413993592773656665763843)
  ·
    refine ⟨78620990389160484998645765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52413993592773656665763843 78620990389160484998645765)
    ·
      refine ⟨14741435697967590937246081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78620990389160484998645765 14741435697967590937246081)
      ·
        refine ⟨11056076773475693202934561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14741435697967590937246081 11056076773475693202934561)
        ·
          refine ⟨8292057580106769902200921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11056076773475693202934561 8292057580106769902200921)
          ·
            refine ⟨6219043185080077426650691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292057580106769902200921 6219043185080077426650691)
            ·
              refine ⟨9328564777620116139976037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219043185080077426650691 9328564777620116139976037)
              ·
                refine ⟨1749105895803771776245507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9328564777620116139976037 1749105895803771776245507)
                ·
                  refine ⟨2623658843705657664368261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749105895803771776245507 2623658843705657664368261)
                  ·
                    refine ⟨491936033194810812069049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2623658843705657664368261 491936033194810812069049)
                    ·
                      rfl

theorem cell22_1437063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1437063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437063 prefixEnd_1437063 := by exact prefixLift 1437063
  have htrace : WordTrace (prefixWord ++ tailWord_1437063) baseStart_1437063 baseEnd_1437063 := by
    simpa [prefixWord, tailWord_1437063, baseEnd_1437063] using wordTrace_append hprefix tailTrace_1437063
  have hstable : (prefixWord ++ tailWord_1437063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437063).length < 2 ^ (prefixWord ++ tailWord_1437063).sum := by decide
  have hdescent : baseEnd_1437063 < baseStart_1437063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437168 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_1437168 : Nat := 118140960795 + 1437168 * 2 ^ 59
def prefixEnd_1437168 : Nat := 4983230072969 + 3 ^ 40 * 1437168 * 2
def baseEnd_1437168 : Nat := 163990658946875179397909

theorem tailTrace_1437168 : CollatzResearch.WordTrace tailWord_1437168 prefixEnd_1437168 163990658946875179397909 := by
  unfold tailWord_1437168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208911628696629799168079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34945215504928839732224105 26208911628696629799168079)
  ·
    refine ⟨39313367443044944698752119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26208911628696629799168079 39313367443044944698752119)
    ·
      refine ⟨58970051164567417048128179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39313367443044944698752119 58970051164567417048128179)
      ·
        refine ⟨88455076746851125572192269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58970051164567417048128179 88455076746851125572192269)
        ·
          refine ⟨33170653780069172089572101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88455076746851125572192269 33170653780069172089572101)
          ·
            refine ⟨6219497583762969766794769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33170653780069172089572101 6219497583762969766794769)
            ·
              refine ⟨4664623187822227325096077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219497583762969766794769 4664623187822227325096077)
              ·
                refine ⟨1749233695433335246911029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664623187822227325096077 1749233695433335246911029)
                ·
                  refine ⟨163990658946875179397909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1749233695433335246911029 163990658946875179397909)
                  ·
                    rfl

theorem cell22_1437168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_1437168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437168 prefixEnd_1437168 := by exact prefixLift 1437168
  have htrace : WordTrace (prefixWord ++ tailWord_1437168) baseStart_1437168 baseEnd_1437168 := by
    simpa [prefixWord, tailWord_1437168, baseEnd_1437168] using wordTrace_append hprefix tailTrace_1437168
  have hstable : (prefixWord ++ tailWord_1437168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437168).length < 2 ^ (prefixWord ++ tailWord_1437168).sum := by decide
  have hdescent : baseEnd_1437168 < baseStart_1437168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437211 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_1437211 : Nat := 118140960795 + 1437211 * 2 ^ 59
def prefixEnd_1437211 : Nat := 4983230072969 + 3 ^ 40 * 1437211 * 2
def baseEnd_1437211 : Nat := 491986696619387759368595

theorem tailTrace_1437211 : CollatzResearch.WordTrace tailWord_1437211 prefixEnd_1437211 491986696619387759368595 := by
  unfold tailWord_1437211
  simp only [CollatzResearch.WordTrace]
  refine ⟨52419391596237477942151487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34946261064158318628100991 52419391596237477942151487)
  ·
    refine ⟨78629087394356216913227231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52419391596237477942151487 78629087394356216913227231)
    ·
      refine ⟨117943631091534325369840847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78629087394356216913227231 117943631091534325369840847)
      ·
        refine ⟨176915446637301488054761271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117943631091534325369840847 176915446637301488054761271)
        ·
          refine ⟨265373169955952232082141907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176915446637301488054761271 265373169955952232082141907)
          ·
            refine ⟨398059754933928348123212861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265373169955952232082141907 398059754933928348123212861)
            ·
              refine ⟨149272408100223130546204823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398059754933928348123212861 149272408100223130546204823)
              ·
                refine ⟨223908612150334695819307235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149272408100223130546204823 223908612150334695819307235)
                ·
                  refine ⟨335862918225502043728960853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223908612150334695819307235 335862918225502043728960853)
                  ·
                    refine ⟨491986696619387759368595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 335862918225502043728960853 491986696619387759368595)
                    ·
                      rfl

theorem cell22_1437211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_1437211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437211 prefixEnd_1437211 := by exact prefixLift 1437211
  have htrace : WordTrace (prefixWord ++ tailWord_1437211) baseStart_1437211 baseEnd_1437211 := by
    simpa [prefixWord, tailWord_1437211, baseEnd_1437211] using wordTrace_append hprefix tailTrace_1437211
  have hstable : (prefixWord ++ tailWord_1437211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437211).length < 2 ^ (prefixWord ++ tailWord_1437211).sum := by decide
  have hdescent : baseEnd_1437211 < baseStart_1437211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437230 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1437230 : Nat := 118140960795 + 1437230 * 2 ^ 59
def prefixEnd_1437230 : Nat := 4983230072969 + 3 ^ 40 * 1437230 * 2
def baseEnd_1437230 : Nat := 163997733569226014381179

theorem tailTrace_1437230 : CollatzResearch.WordTrace tailWord_1437230 prefixEnd_1437230 163997733569226014381179 := by
  unfold tailWord_1437230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6552510572896080523386643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34946723055445762791395429 6552510572896080523386643)
  ·
    refine ⟨9828765859344120785079965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6552510572896080523386643 9828765859344120785079965)
    ·
      refine ⟨3685787197254045294404987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9828765859344120785079965 3685787197254045294404987)
      ·
        refine ⟨5528680795881067941607481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685787197254045294404987 5528680795881067941607481)
        ·
          refine ⟨4146510596910800956205611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5528680795881067941607481 4146510596910800956205611)
          ·
            refine ⟨6219765895366201434308417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146510596910800956205611 6219765895366201434308417)
            ·
              refine ⟨4664824421524651075731313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219765895366201434308417 4664824421524651075731313)
              ·
                refine ⟨3498618316143488306798485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4664824421524651075731313 3498618316143488306798485)
                ·
                  refine ⟨163997733569226014381179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3498618316143488306798485 163997733569226014381179)
                  ·
                    rfl

theorem cell22_1437230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1437230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437230 prefixEnd_1437230 := by exact prefixLift 1437230
  have htrace : WordTrace (prefixWord ++ tailWord_1437230) baseStart_1437230 baseEnd_1437230 := by
    simpa [prefixWord, tailWord_1437230, baseEnd_1437230] using wordTrace_append hprefix tailTrace_1437230
  have hstable : (prefixWord ++ tailWord_1437230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437230).length < 2 ^ (prefixWord ++ tailWord_1437230).sum := by decide
  have hdescent : baseEnd_1437230 < baseStart_1437230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437247 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 4]
def baseStart_1437247 : Nat := 118140960795 + 1437247 * 2 ^ 59
def prefixEnd_1437247 : Nat := 4983230072969 + 3 ^ 40 * 1437247 * 2
def baseEnd_1437247 : Nat := 163999673385031888489495

theorem tailTrace_1437247 : CollatzResearch.WordTrace tailWord_1437247 prefixEnd_1437247 163999673385031888489495 := by
  unfold tailWord_1437247
  simp only [CollatzResearch.WordTrace]
  refine ⟨52420704624107056090461995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34947136416071370726974663 52420704624107056090461995)
  ·
    refine ⟨78631056936160584135692993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52420704624107056090461995 78631056936160584135692993)
    ·
      refine ⟨58973292702120438101769745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78631056936160584135692993 58973292702120438101769745)
      ·
        refine ⟨44229969526590328576327309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58973292702120438101769745 44229969526590328576327309)
        ·
          refine ⟨16586238572471373216122741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44229969526590328576327309 16586238572471373216122741)
          ·
            refine ⟨1554959866169191239011507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16586238572471373216122741 1554959866169191239011507)
            ·
              refine ⟨2332439799253786858517261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554959866169191239011507 2332439799253786858517261)
              ·
                refine ⟨874664924720170071943973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332439799253786858517261 874664924720170071943973)
                ·
                  refine ⟨163999673385031888489495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874664924720170071943973 163999673385031888489495)
                  ·
                    rfl

theorem cell22_1437247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 4].length) (baseStart_1437247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437247 prefixEnd_1437247 := by exact prefixLift 1437247
  have htrace : WordTrace (prefixWord ++ tailWord_1437247) baseStart_1437247 baseEnd_1437247 := by
    simpa [prefixWord, tailWord_1437247, baseEnd_1437247] using wordTrace_append hprefix tailTrace_1437247
  have hstable : (prefixWord ++ tailWord_1437247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437247).length < 2 ^ (prefixWord ++ tailWord_1437247).sum := by decide
  have hdescent : baseEnd_1437247 < baseStart_1437247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437260 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1437260 : Nat := 118140960795 + 1437260 * 2 ^ 59
def prefixEnd_1437260 : Nat := 4983230072969 + 3 ^ 40 * 1437260 * 2
def baseEnd_1437260 : Nat := 492003470320767964893445

theorem tailTrace_1437260 : CollatzResearch.WordTrace tailWord_1437260 prefixEnd_1437260 492003470320767964893445 := by
  unfold tailWord_1437260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26210589386529979655342617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34947452515373306207123489 26210589386529979655342617)
  ·
    refine ⟨19657942039897484741506963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26210589386529979655342617 19657942039897484741506963)
    ·
      refine ⟨29486913059846227112260445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19657942039897484741506963 29486913059846227112260445)
      ·
        refine ⟨11057592397442335167097667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29486913059846227112260445 11057592397442335167097667)
        ·
          refine ⟨16586388596163502750646501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057592397442335167097667 16586388596163502750646501)
          ·
            refine ⟨3109947861780656765746219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16586388596163502750646501 3109947861780656765746219)
            ·
              refine ⟨4664921792670985148619329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109947861780656765746219 4664921792670985148619329)
              ·
                refine ⟨3498691344503238861464497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4664921792670985148619329 3498691344503238861464497)
                ·
                  refine ⟨2624018508377429146098373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3498691344503238861464497 2624018508377429146098373)
                  ·
                    refine ⟨492003470320767964893445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624018508377429146098373 492003470320767964893445)
                    ·
                      rfl

theorem cell22_1437260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1437260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437260 prefixEnd_1437260 := by exact prefixLift 1437260
  have htrace : WordTrace (prefixWord ++ tailWord_1437260) baseStart_1437260 baseEnd_1437260 := by
    simpa [prefixWord, tailWord_1437260, baseEnd_1437260] using wordTrace_append hprefix tailTrace_1437260
  have hstable : (prefixWord ++ tailWord_1437260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437260).length < 2 ^ (prefixWord ++ tailWord_1437260).sum := by decide
  have hdescent : baseEnd_1437260 < baseStart_1437260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437307 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 1, 3]
def baseStart_1437307 : Nat := 118140960795 + 1437307 * 2 ^ 59
def prefixEnd_1437307 : Nat := 4983230072969 + 3 ^ 40 * 1437307 * 2
def baseEnd_1437307 : Nat := 492019559381275508968301

theorem tailTrace_1437307 : CollatzResearch.WordTrace tailWord_1437307 prefixEnd_1437307 492019559381275508968301 := by
  unfold tailWord_1437307
  simp only [CollatzResearch.WordTrace]
  refine ⟨52422893003889686337646175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34948595335926457558430783 52422893003889686337646175)
  ·
    refine ⟨78634339505834529506469263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52422893003889686337646175 78634339505834529506469263)
    ·
      refine ⟨117951509258751794259703895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78634339505834529506469263 117951509258751794259703895)
      ·
        refine ⟨176927263888127691389555843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117951509258751794259703895 176927263888127691389555843)
        ·
          refine ⟨265390895832191537084333765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176927263888127691389555843 265390895832191537084333765)
          ·
            refine ⟨49760792968535913203312581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265390895832191537084333765 49760792968535913203312581)
            ·
              refine ⟨9330148681600483725621109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49760792968535913203312581 9330148681600483725621109)
              ·
                refine ⟨874701438900045349276979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9330148681600483725621109 874701438900045349276979)
                ·
                  refine ⟨1312052158350068023915469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874701438900045349276979 1312052158350068023915469)
                  ·
                    refine ⟨492019559381275508968301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312052158350068023915469 492019559381275508968301)
                    ·
                      rfl

theorem cell22_1437307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 3].length) (baseStart_1437307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437307 prefixEnd_1437307 := by exact prefixLift 1437307
  have htrace : WordTrace (prefixWord ++ tailWord_1437307) baseStart_1437307 baseEnd_1437307 := by
    simpa [prefixWord, tailWord_1437307, baseEnd_1437307] using wordTrace_append hprefix tailTrace_1437307
  have hstable : (prefixWord ++ tailWord_1437307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437307).length < 2 ^ (prefixWord ++ tailWord_1437307).sum := by decide
  have hdescent : baseEnd_1437307 < baseStart_1437307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437335 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1437335 : Nat := 118140960795 + 1437335 * 2 ^ 59
def prefixEnd_1437335 : Nat := 4983230072969 + 3 ^ 40 * 1437335 * 2
def baseEnd_1437335 : Nat := 492029144353492769268215

theorem tailTrace_1437335 : CollatzResearch.WordTrace tailWord_1437335 prefixEnd_1437335 492029144353492769268215 := by
  unfold tailWord_1437335
  simp only [CollatzResearch.WordTrace]
  refine ⟨52423914247788247119665459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34949276165192164746443639 52423914247788247119665459)
  ·
    refine ⟨78635871371682370679498189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52423914247788247119665459 78635871371682370679498189)
    ·
      refine ⟨29488451764380889004811821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78635871371682370679498189 29488451764380889004811821)
      ·
        refine ⟨11058169411642833376804433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29488451764380889004811821 11058169411642833376804433)
        ·
          refine ⟨8293627058732125032603325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11058169411642833376804433 8293627058732125032603325)
          ·
            refine ⟨3110110147024546887226247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8293627058732125032603325 3110110147024546887226247)
            ·
              refine ⟨4665165220536820330839371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110110147024546887226247 4665165220536820330839371)
              ·
                refine ⟨6997747830805230496259057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665165220536820330839371 6997747830805230496259057)
                ·
                  refine ⟨5248310873103922872194293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6997747830805230496259057 5248310873103922872194293)
                  ·
                    refine ⟨492029144353492769268215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5248310873103922872194293 492029144353492769268215)
                    ·
                      rfl

theorem cell22_1437335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1437335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437335 prefixEnd_1437335 := by exact prefixLift 1437335
  have htrace : WordTrace (prefixWord ++ tailWord_1437335) baseStart_1437335 baseEnd_1437335 := by
    simpa [prefixWord, tailWord_1437335, baseEnd_1437335] using wordTrace_append hprefix tailTrace_1437335
  have hstable : (prefixWord ++ tailWord_1437335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437335).length < 2 ^ (prefixWord ++ tailWord_1437335).sum := by decide
  have hdescent : baseEnd_1437335 < baseStart_1437335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437358 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1437358 : Nat := 118140960795 + 1437358 * 2 ^ 59
def prefixEnd_1437358 : Nat := 4983230072969 + 3 ^ 40 * 1437358 * 2
def baseEnd_1437358 : Nat := 492037017723528375943145

theorem tailTrace_1437358 : CollatzResearch.WordTrace tailWord_1437358 prefixEnd_1437358 492037017723528375943145 := by
  unfold tailWord_1437358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553094140838115255969091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34949835417803281365168485 6553094140838115255969091)
  ·
    refine ⟨9829641211257172883953637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553094140838115255969091 9829641211257172883953637)
    ·
      refine ⟨1843057727110719915741307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9829641211257172883953637 1843057727110719915741307)
      ·
        refine ⟨2764586590666079873611961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843057727110719915741307 2764586590666079873611961)
        ·
          refine ⟨2073439942999559905208971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764586590666079873611961 2073439942999559905208971)
          ·
            refine ⟨3110159914499339857813457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073439942999559905208971 3110159914499339857813457)
            ·
              refine ⟨2332619935874504893360093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3110159914499339857813457 2332619935874504893360093)
              ·
                refine ⟨874732475952939335010035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332619935874504893360093 874732475952939335010035)
                ·
                  refine ⟨1312098713929409002515053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874732475952939335010035 1312098713929409002515053)
                  ·
                    refine ⟨492037017723528375943145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312098713929409002515053 492037017723528375943145)
                    ·
                      rfl

theorem cell22_1437358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1437358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437358 prefixEnd_1437358 := by exact prefixLift 1437358
  have htrace : WordTrace (prefixWord ++ tailWord_1437358) baseStart_1437358 baseEnd_1437358 := by
    simpa [prefixWord, tailWord_1437358, baseEnd_1437358] using wordTrace_append hprefix tailTrace_1437358
  have hstable : (prefixWord ++ tailWord_1437358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437358).length < 2 ^ (prefixWord ++ tailWord_1437358).sum := by decide
  have hdescent : baseEnd_1437358 < baseStart_1437358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437367 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 1, 4]
def baseStart_1437367 : Nat := 118140960795 + 1437367 * 2 ^ 59
def prefixEnd_1437367 : Nat := 4983230072969 + 3 ^ 40 * 1437367 * 2
def baseEnd_1437367 : Nat := 492040098607455352468117

theorem tailTrace_1437367 : CollatzResearch.WordTrace tailWord_1437367 prefixEnd_1437367 492040098607455352468117 := by
  unfold tailWord_1437367
  simp only [CollatzResearch.WordTrace]
  refine ⟨52425081383672316584830355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34950054255781544389886903 52425081383672316584830355)
  ·
    refine ⟨78637622075508474877245533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52425081383672316584830355 78637622075508474877245533)
    ·
      refine ⟨29489108278315678078967075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78637622075508474877245533 29489108278315678078967075)
      ·
        refine ⟨44233662417473517118450613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29489108278315678078967075 44233662417473517118450613)
        ·
          refine ⟨4146905851638142229854745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44233662417473517118450613 4146905851638142229854745)
          ·
            refine ⟨3110179388728606672391059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146905851638142229854745 3110179388728606672391059)
            ·
              refine ⟨4665269083092910008586589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110179388728606672391059 4665269083092910008586589)
              ·
                refine ⟨1749475906159841253219971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665269083092910008586589 1749475906159841253219971)
                ·
                  refine ⟨2624213859239761879829957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749475906159841253219971 2624213859239761879829957)
                  ·
                    refine ⟨492040098607455352468117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624213859239761879829957 492040098607455352468117)
                    ·
                      rfl

theorem cell22_1437367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_1437367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437367 prefixEnd_1437367 := by exact prefixLift 1437367
  have htrace : WordTrace (prefixWord ++ tailWord_1437367) baseStart_1437367 baseEnd_1437367 := by
    simpa [prefixWord, tailWord_1437367, baseEnd_1437367] using wordTrace_append hprefix tailTrace_1437367
  have hstable : (prefixWord ++ tailWord_1437367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437367).length < 2 ^ (prefixWord ++ tailWord_1437367).sum := by decide
  have hdescent : baseEnd_1437367 < baseStart_1437367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437536 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_1437536 : Nat := 118140960795 + 1437536 * 2 ^ 59
def prefixEnd_1437536 : Nat := 4983230072969 + 3 ^ 40 * 1437536 * 2
def baseEnd_1437536 : Nat := 492097950761195244992599

theorem tailTrace_1437536 : CollatzResearch.WordTrace tailWord_1437536 prefixEnd_1437536 492097950761195244992599 := by
  unfold tailWord_1437536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26215622660030029223866231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34954163546706705631821641 26215622660030029223866231)
  ·
    refine ⟨39323433990045043835799347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26215622660030029223866231 39323433990045043835799347)
    ·
      refine ⟨58985150985067565753699021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39323433990045043835799347 58985150985067565753699021)
      ·
        refine ⟨22119431619400337157637133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58985150985067565753699021 22119431619400337157637133)
        ·
          refine ⟨8294786857275126434113925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22119431619400337157637133 8294786857275126434113925)
          ·
            refine ⟨1555272535739086206396361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8294786857275126434113925 1555272535739086206396361)
            ·
              refine ⟨1166454401804314654797271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555272535739086206396361 1166454401804314654797271)
              ·
                refine ⟨1749681602706471982195907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166454401804314654797271 1749681602706471982195907)
                ·
                  refine ⟨2624522404059707973293861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749681602706471982195907 2624522404059707973293861)
                  ·
                    refine ⟨492097950761195244992599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624522404059707973293861 492097950761195244992599)
                    ·
                      rfl

theorem cell22_1437536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_1437536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437536 prefixEnd_1437536 := by exact prefixLift 1437536
  have htrace : WordTrace (prefixWord ++ tailWord_1437536) baseStart_1437536 baseEnd_1437536 := by
    simpa [prefixWord, tailWord_1437536, baseEnd_1437536] using wordTrace_append hprefix tailTrace_1437536
  have hstable : (prefixWord ++ tailWord_1437536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437536).length < 2 ^ (prefixWord ++ tailWord_1437536).sum := by decide
  have hdescent : baseEnd_1437536 < baseStart_1437536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437566 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1437566 : Nat := 118140960795 + 1437566 * 2 ^ 59
def prefixEnd_1437566 : Nat := 4983230072969 + 3 ^ 40 * 1437566 * 2
def baseEnd_1437566 : Nat := 492108220374285166742507

theorem tailTrace_1437566 : CollatzResearch.WordTrace tailWord_1437566 prefixEnd_1437566 492108220374285166742507 := by
  unfold tailWord_1437566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6554042438743921696415569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34954893006634249047549701 6554042438743921696415569)
  ·
    refine ⟨4915531829057941272311677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6554042438743921696415569 4915531829057941272311677)
    ·
      refine ⟨1843324435896727977116879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4915531829057941272311677 1843324435896727977116879)
      ·
        refine ⟨2764986653845091965675319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843324435896727977116879 2764986653845091965675319)
        ·
          refine ⟨4147479980767637948512979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764986653845091965675319 4147479980767637948512979)
          ·
            refine ⟨6221219971151456922769469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147479980767637948512979 6221219971151456922769469)
            ·
              refine ⟨2332957489181796346038551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6221219971151456922769469 2332957489181796346038551)
              ·
                refine ⟨3499436233772694519057827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332957489181796346038551 3499436233772694519057827)
                ·
                  refine ⟨5249154350659041778586741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499436233772694519057827 5249154350659041778586741)
                  ·
                    refine ⟨492108220374285166742507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5249154350659041778586741 492108220374285166742507)
                    ·
                      rfl

theorem cell22_1437566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1437566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437566 prefixEnd_1437566 := by exact prefixLift 1437566
  have htrace : WordTrace (prefixWord ++ tailWord_1437566) baseStart_1437566 baseEnd_1437566 := by
    simpa [prefixWord, tailWord_1437566, baseEnd_1437566] using wordTrace_append hprefix tailTrace_1437566
  have hstable : (prefixWord ++ tailWord_1437566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437566).length < 2 ^ (prefixWord ++ tailWord_1437566).sum := by decide
  have hdescent : baseEnd_1437566 < baseStart_1437566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437598 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1437598 : Nat := 118140960795 + 1437598 * 2 ^ 59
def prefixEnd_1437598 : Nat := 4983230072969 + 3 ^ 40 * 1437598 * 2
def baseEnd_1437598 : Nat := 492119174628247749942409

theorem tailTrace_1437598 : CollatzResearch.WordTrace tailWord_1437598 prefixEnd_1437598 492119174628247749942409 := by
  unfold tailWord_1437598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6554188330729430379561181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34955671097223628690992965 6554188330729430379561181)
  ·
    refine ⟨2457820624023536392335443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6554188330729430379561181 2457820624023536392335443)
    ·
      refine ⟨3686730936035304588503165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457820624023536392335443 3686730936035304588503165)
      ·
        refine ⟨1382524101013239220688687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3686730936035304588503165 1382524101013239220688687)
        ·
          refine ⟨2073786151519858831033031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382524101013239220688687 2073786151519858831033031)
          ·
            refine ⟨3110679227279788246549547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073786151519858831033031 3110679227279788246549547)
            ·
              refine ⟨4666018840919682369824321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110679227279788246549547 4666018840919682369824321)
              ·
                refine ⟨3499514130689761777368241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4666018840919682369824321 3499514130689761777368241)
                ·
                  refine ⟨2624635598017321333026181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499514130689761777368241 2624635598017321333026181)
                  ·
                    refine ⟨492119174628247749942409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624635598017321333026181 492119174628247749942409)
                    ·
                      rfl

theorem cell22_1437598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1437598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437598 prefixEnd_1437598 := by exact prefixLift 1437598
  have htrace : WordTrace (prefixWord ++ tailWord_1437598) baseStart_1437598 baseEnd_1437598 := by
    simpa [prefixWord, tailWord_1437598, baseEnd_1437598] using wordTrace_append hprefix tailTrace_1437598
  have hstable : (prefixWord ++ tailWord_1437598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437598).length < 2 ^ (prefixWord ++ tailWord_1437598).sum := by decide
  have hdescent : baseEnd_1437598 < baseStart_1437598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437686 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1437686 : Nat := 118140960795 + 1437686 * 2 ^ 59
def prefixEnd_1437686 : Nat := 4983230072969 + 3 ^ 40 * 1437686 * 2
def baseEnd_1437686 : Nat := 164049766275548284580713

theorem tailTrace_1437686 : CollatzResearch.WordTrace tailWord_1437686 prefixEnd_1437686 164049766275548284580713 := by
  unfold tailWord_1437686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277294766844789629105807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34957810846344422710461941 3277294766844789629105807)
  ·
    refine ⟨4915942150267184443658711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277294766844789629105807 4915942150267184443658711)
    ·
      refine ⟨7373913225400776665488067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915942150267184443658711 7373913225400776665488067)
      ·
        refine ⟨11060869838101164998232101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7373913225400776665488067 11060869838101164998232101)
        ·
          refine ⟨2073913094643968437168519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11060869838101164998232101 2073913094643968437168519)
          ·
            refine ⟨3110869641965952655752779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073913094643968437168519 3110869641965952655752779)
            ·
              refine ⟨4666304462948928983629169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110869641965952655752779 4666304462948928983629169)
              ·
                refine ⟨3499728347211696737721877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4666304462948928983629169 3499728347211696737721877)
                ·
                  refine ⟨164049766275548284580713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3499728347211696737721877 164049766275548284580713)
                  ·
                    rfl

theorem cell22_1437686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1437686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437686 prefixEnd_1437686 := by exact prefixLift 1437686
  have htrace : WordTrace (prefixWord ++ tailWord_1437686) baseStart_1437686 baseEnd_1437686 := by
    simpa [prefixWord, tailWord_1437686, baseEnd_1437686] using wordTrace_append hprefix tailTrace_1437686
  have hstable : (prefixWord ++ tailWord_1437686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437686).length < 2 ^ (prefixWord ++ tailWord_1437686).sum := by decide
  have hdescent : baseEnd_1437686 < baseStart_1437686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437735 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1437735 : Nat := 118140960795 + 1437735 * 2 ^ 59
def prefixEnd_1437735 : Nat := 4983230072969 + 3 ^ 40 * 1437735 * 2
def baseEnd_1437735 : Nat := 492166072528025059266989

theorem tailTrace_1437735 : CollatzResearch.WordTrace tailWord_1437735 prefixEnd_1437735 492166072528025059266989 := by
  unfold tailWord_1437735
  simp only [CollatzResearch.WordTrace]
  refine ⟨52438503446339115434226659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34959002297559410289484439 52438503446339115434226659)
  ·
    refine ⟨78657755169508673151339989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52438503446339115434226659 78657755169508673151339989)
    ·
      refine ⟨1843541136785359526984531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 78657755169508673151339989 1843541136785359526984531)
      ·
        refine ⟨2765311705178039290476797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843541136785359526984531 2765311705178039290476797)
        ·
          refine ⟨1036991889441764733928799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2765311705178039290476797 1036991889441764733928799)
          ·
            refine ⟨1555487834162647100893199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036991889441764733928799 1555487834162647100893199)
            ·
              refine ⟨2333231751243970651339799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555487834162647100893199 2333231751243970651339799)
              ·
                refine ⟨3499847626865955977009699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2333231751243970651339799 3499847626865955977009699)
                ·
                  refine ⟨5249771440298933965514549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499847626865955977009699 5249771440298933965514549)
                  ·
                    refine ⟨492166072528025059266989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5249771440298933965514549 492166072528025059266989)
                    ·
                      rfl

theorem cell22_1437735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1437735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437735 prefixEnd_1437735 := by exact prefixLift 1437735
  have htrace : WordTrace (prefixWord ++ tailWord_1437735) baseStart_1437735 baseEnd_1437735 := by
    simpa [prefixWord, tailWord_1437735, baseEnd_1437735] using wordTrace_append hprefix tailTrace_1437735
  have hstable : (prefixWord ++ tailWord_1437735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437735).length < 2 ^ (prefixWord ++ tailWord_1437735).sum := by decide
  have hdescent : baseEnd_1437735 < baseStart_1437735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437746 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_1437746 : Nat := 118140960795 + 1437746 * 2 ^ 59
def prefixEnd_1437746 : Nat := 4983230072969 + 3 ^ 40 * 1437746 * 2
def baseEnd_1437746 : Nat := 492169838052824697241955

theorem tailTrace_1437746 : CollatzResearch.WordTrace tailWord_1437746 prefixEnd_1437746 492169838052824697241955 := by
  unfold tailWord_1437746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13109726162324816078219273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34959269766199509541918061 13109726162324816078219273)
  ·
    refine ⟨9832294621743612058664455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13109726162324816078219273 9832294621743612058664455)
    ·
      refine ⟨14748441932615418087996683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9832294621743612058664455 14748441932615418087996683)
      ·
        refine ⟨22122662898923127131995025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14748441932615418087996683 22122662898923127131995025)
        ·
          refine ⟨16591997174192345348996269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22122662898923127131995025 16591997174192345348996269)
          ·
            refine ⟨6221998940322129505873601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16591997174192345348996269 6221998940322129505873601)
            ·
              refine ⟨4666499205241597129405201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6221998940322129505873601 4666499205241597129405201)
              ·
                refine ⟨3499874403931197847053901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4666499205241597129405201 3499874403931197847053901)
                ·
                  refine ⟨1312452901474199192645213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3499874403931197847053901 1312452901474199192645213)
                  ·
                    refine ⟨492169838052824697241955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312452901474199192645213 492169838052824697241955)
                    ·
                      rfl

theorem cell22_1437746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_1437746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437746 prefixEnd_1437746 := by exact prefixLift 1437746
  have htrace : WordTrace (prefixWord ++ tailWord_1437746) baseStart_1437746 baseEnd_1437746 := by
    simpa [prefixWord, tailWord_1437746, baseEnd_1437746] using wordTrace_append hprefix tailTrace_1437746
  have hstable : (prefixWord ++ tailWord_1437746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437746).length < 2 ^ (prefixWord ++ tailWord_1437746).sum := by decide
  have hdescent : baseEnd_1437746 < baseStart_1437746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437806 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1437806 : Nat := 118140960795 + 1437806 * 2 ^ 59
def prefixEnd_1437806 : Nat := 4983230072969 + 3 ^ 40 * 1437806 * 2
def baseEnd_1437806 : Nat := 492190377279004540741771

theorem tailTrace_1437806 : CollatzResearch.WordTrace tailWord_1437806 prefixEnd_1437806 492190377279004540741771 := by
  unfold tailWord_1437806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555136628635236820007659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34960728686054596373374181 6555136628635236820007659)
  ·
    refine ⟨9832704942952855230011489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6555136628635236820007659 9832704942952855230011489)
    ·
      refine ⟨7374528707214641422508617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9832704942952855230011489 7374528707214641422508617)
      ·
        refine ⟨5530896530410981066881463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7374528707214641422508617 5530896530410981066881463)
        ·
          refine ⟨8296344795616471600322195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530896530410981066881463 8296344795616471600322195)
          ·
            refine ⟨12444517193424707400483293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8296344795616471600322195 12444517193424707400483293)
            ·
              refine ⟨4666693947534265275181235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12444517193424707400483293 4666693947534265275181235)
              ·
                refine ⟨7000040921301397912771853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666693947534265275181235 7000040921301397912771853)
                ·
                  refine ⟨2625015345488024217289445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7000040921301397912771853 2625015345488024217289445)
                  ·
                    refine ⟨492190377279004540741771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2625015345488024217289445 492190377279004540741771)
                    ·
                      rfl

theorem cell22_1437806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1437806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437806 prefixEnd_1437806 := by exact prefixLift 1437806
  have htrace : WordTrace (prefixWord ++ tailWord_1437806) baseStart_1437806 baseEnd_1437806 := by
    simpa [prefixWord, tailWord_1437806, baseEnd_1437806] using wordTrace_append hprefix tailTrace_1437806
  have hstable : (prefixWord ++ tailWord_1437806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437806).length < 2 ^ (prefixWord ++ tailWord_1437806).sum := by decide
  have hdescent : baseEnd_1437806 < baseStart_1437806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437853 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1437853 : Nat := 118140960795 + 1437853 * 2 ^ 59
def prefixEnd_1437853 : Nat := 4983230072969 + 3 ^ 40 * 1437853 * 2
def baseEnd_1437853 : Nat := 492206466339512084816627

theorem tailTrace_1437853 : CollatzResearch.WordTrace tailWord_1437853 prefixEnd_1437853 492206466339512084816627 := by
  unfold tailWord_1437853
  simp only [CollatzResearch.WordTrace]
  refine ⟨52442807259911621587022213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34961871506607747724681475 52442807259911621587022213)
  ·
    refine ⟨9833026361233429047566665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52442807259911621587022213 9833026361233429047566665)
    ·
      refine ⟨7374769770925071785674999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9833026361233429047566665 7374769770925071785674999)
      ·
        refine ⟨11062154656387607678512499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374769770925071785674999 11062154656387607678512499)
        ·
          refine ⟨16593231984581411517768749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062154656387607678512499 16593231984581411517768749)
          ·
            refine ⟨6222461994218029319163281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16593231984581411517768749 6222461994218029319163281)
            ·
              refine ⟨4666846495663521989372461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6222461994218029319163281 4666846495663521989372461)
              ·
                refine ⟨1750067435873820746014673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4666846495663521989372461 1750067435873820746014673)
                ·
                  refine ⟨1312550576905365559511005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750067435873820746014673 1312550576905365559511005)
                  ·
                    refine ⟨492206466339512084816627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312550576905365559511005 492206466339512084816627)
                    ·
                      rfl

theorem cell22_1437853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1437853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437853 prefixEnd_1437853 := by exact prefixLift 1437853
  have htrace : WordTrace (prefixWord ++ tailWord_1437853) baseStart_1437853 baseEnd_1437853 := by
    simpa [prefixWord, tailWord_1437853, baseEnd_1437853] using wordTrace_append hprefix tailTrace_1437853
  have hstable : (prefixWord ++ tailWord_1437853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437853).length < 2 ^ (prefixWord ++ tailWord_1437853).sum := by decide
  have hdescent : baseEnd_1437853 < baseStart_1437853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437881 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_1437881 : Nat := 118140960795 + 1437881 * 2 ^ 59
def prefixEnd_1437881 : Nat := 4983230072969 + 3 ^ 40 * 1437881 * 2
def baseEnd_1437881 : Nat := 492216051311729345116541

theorem tailTrace_1437881 : CollatzResearch.WordTrace tailWord_1437881 prefixEnd_1437881 492216051311729345116541 := by
  unfold tailWord_1437881
  simp only [CollatzResearch.WordTrace]
  refine ⟨52443828503810182369041497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34962552335873454912694331 52443828503810182369041497)
  ·
    refine ⟨39332871377857636776781123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52443828503810182369041497 39332871377857636776781123)
    ·
      refine ⟨58999307066786455165171685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39332871377857636776781123 58999307066786455165171685)
      ·
        refine ⟨11062370075022460343469691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58999307066786455165171685 11062370075022460343469691)
        ·
          refine ⟨16593555112533690515204537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062370075022460343469691 16593555112533690515204537)
          ·
            refine ⟨12445166334400267886403403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16593555112533690515204537 12445166334400267886403403)
            ·
              refine ⟨18667749501600401829605105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12445166334400267886403403 18667749501600401829605105)
              ·
                refine ⟨14000812126200301372203829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18667749501600401829605105 14000812126200301372203829)
                ·
                  refine ⟨1312576136831278253644109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14000812126200301372203829 1312576136831278253644109)
                  ·
                    refine ⟨492216051311729345116541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312576136831278253644109 492216051311729345116541)
                    ·
                      rfl

theorem cell22_1437881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_1437881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437881 prefixEnd_1437881 := by exact prefixLift 1437881
  have htrace : WordTrace (prefixWord ++ tailWord_1437881) baseStart_1437881 baseEnd_1437881 := by
    simpa [prefixWord, tailWord_1437881, baseEnd_1437881] using wordTrace_append hprefix tailTrace_1437881
  have hstable : (prefixWord ++ tailWord_1437881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437881).length < 2 ^ (prefixWord ++ tailWord_1437881).sum := by decide
  have hdescent : baseEnd_1437881 < baseStart_1437881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437898 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1437898 : Nat := 118140960795 + 1437898 * 2 ^ 59
def prefixEnd_1437898 : Nat := 4983230072969 + 3 ^ 40 * 1437898 * 2
def baseEnd_1437898 : Nat := 492221870759146967441489

theorem tailTrace_1437898 : CollatzResearch.WordTrace tailWord_1437898 prefixEnd_1437898 492221870759146967441489 := by
  unfold tailWord_1437898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13111112136187148568102587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34962965696499062848273565 13111112136187148568102587)
  ·
    refine ⟨19666668204280722852153881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13111112136187148568102587 19666668204280722852153881)
    ·
      refine ⟨14750001153210542139115411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19666668204280722852153881 14750001153210542139115411)
      ·
        refine ⟨22125001729815813208673117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14750001153210542139115411 22125001729815813208673117)
        ·
          refine ⟨8296875648680929953252419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22125001729815813208673117 8296875648680929953252419)
          ·
            refine ⟨12445313473021394929878629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8296875648680929953252419 12445313473021394929878629)
            ·
              refine ⟨2333496276191511549352243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12445313473021394929878629 2333496276191511549352243)
              ·
                refine ⟨3500244414287267324028365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2333496276191511549352243 3500244414287267324028365)
                ·
                  refine ⟨1312591655357725246510637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3500244414287267324028365 1312591655357725246510637)
                  ·
                    refine ⟨492221870759146967441489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312591655357725246510637 492221870759146967441489)
                    ·
                      rfl

theorem cell22_1437898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1437898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437898 prefixEnd_1437898 := by exact prefixLift 1437898
  have htrace : WordTrace (prefixWord ++ tailWord_1437898) baseStart_1437898 baseEnd_1437898 := by
    simpa [prefixWord, tailWord_1437898, baseEnd_1437898] using wordTrace_append hprefix tailTrace_1437898
  have hstable : (prefixWord ++ tailWord_1437898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437898).length < 2 ^ (prefixWord ++ tailWord_1437898).sum := by decide
  have hdescent : baseEnd_1437898 < baseStart_1437898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437975 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 1, 4]
def baseStart_1437975 : Nat := 118140960795 + 1437975 * 2 ^ 59
def prefixEnd_1437975 : Nat := 4983230072969 + 3 ^ 40 * 1437975 * 2
def baseEnd_1437975 : Nat := 492248229432744433266253

theorem tailTrace_1437975 : CollatzResearch.WordTrace tailWord_1437975 prefixEnd_1437975 492248229432744433266253 := by
  unfold tailWord_1437975
  simp only [CollatzResearch.WordTrace]
  refine ⟨52447256965469636422963379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34964837976979757615308919 52447256965469636422963379)
  ·
    refine ⟨78670885448204454634445069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52447256965469636422963379 78670885448204454634445069)
    ·
      refine ⟨29501582043076670487916901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78670885448204454634445069 29501582043076670487916901)
      ·
        refine ⟨5531546633076875716484419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29501582043076670487916901 5531546633076875716484419)
        ·
          refine ⟨8297319949615313574726629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5531546633076875716484419 8297319949615313574726629)
          ·
            refine ⟨1555747490552871295261243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8297319949615313574726629 1555747490552871295261243)
            ·
              refine ⟨2333621235829306942891865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555747490552871295261243 2333621235829306942891865)
              ·
                refine ⟨1750215926871980207168899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333621235829306942891865 1750215926871980207168899)
                ·
                  refine ⟨2625323890307970310753349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750215926871980207168899 2625323890307970310753349)
                  ·
                    refine ⟨492248229432744433266253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2625323890307970310753349 492248229432744433266253)
                    ·
                      rfl

theorem cell22_1437975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_1437975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437975 prefixEnd_1437975 := by exact prefixLift 1437975
  have htrace : WordTrace (prefixWord ++ tailWord_1437975) baseStart_1437975 baseEnd_1437975 := by
    simpa [prefixWord, tailWord_1437975, baseEnd_1437975] using wordTrace_append hprefix tailTrace_1437975
  have hstable : (prefixWord ++ tailWord_1437975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437975).length < 2 ^ (prefixWord ++ tailWord_1437975).sum := by decide
  have hdescent : baseEnd_1437975 < baseStart_1437975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437988 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1437988 : Nat := 118140960795 + 1437988 * 2 ^ 59
def prefixEnd_1437988 : Nat := 4983230072969 + 3 ^ 40 * 1437988 * 2
def baseEnd_1437988 : Nat := 492252679598416732691213

theorem tailTrace_1437988 : CollatzResearch.WordTrace tailWord_1437988 prefixEnd_1437988 492252679598416732691213 := by
  unfold tailWord_1437988
  simp only [CollatzResearch.WordTrace]
  refine ⟨26223865557211269821593309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34965154076281693095457745 26223865557211269821593309)
  ·
    refine ⟨9833949583954226183097491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26223865557211269821593309 9833949583954226183097491)
    ·
      refine ⟨14750924375931339274646237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9833949583954226183097491 14750924375931339274646237)
      ·
        refine ⟨5531596640974252227992339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14750924375931339274646237 5531596640974252227992339)
        ·
          refine ⟨8297394961461378341988509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5531596640974252227992339 8297394961461378341988509)
          ·
            refine ⟨3111523110548016878245691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8297394961461378341988509 3111523110548016878245691)
            ·
              refine ⟨4667284665822025317368537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111523110548016878245691 4667284665822025317368537)
              ·
                refine ⟨3500463499366518988026403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667284665822025317368537 3500463499366518988026403)
                ·
                  refine ⟨5250695249049778482039605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500463499366518988026403 5250695249049778482039605)
                  ·
                    refine ⟨492252679598416732691213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5250695249049778482039605 492252679598416732691213)
                    ·
                      rfl

theorem cell22_1437988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1437988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437988 prefixEnd_1437988 := by exact prefixLift 1437988
  have htrace : WordTrace (prefixWord ++ tailWord_1437988) baseStart_1437988 baseEnd_1437988 := by
    simpa [prefixWord, tailWord_1437988, baseEnd_1437988] using wordTrace_append hprefix tailTrace_1437988
  have hstable : (prefixWord ++ tailWord_1437988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437988).length < 2 ^ (prefixWord ++ tailWord_1437988).sum := by decide
  have hdescent : baseEnd_1437988 < baseStart_1437988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437992 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1437992 : Nat := 118140960795 + 1437992 * 2 ^ 59
def prefixEnd_1437992 : Nat := 4983230072969 + 3 ^ 40 * 1437992 * 2
def baseEnd_1437992 : Nat := 492254048880162055591201

theorem tailTrace_1437992 : CollatzResearch.WordTrace tailWord_1437992 prefixEnd_1437992 492254048880162055591201 := by
  unfold tailWord_1437992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26223938503204024163166115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34965251337605365550888153 26223938503204024163166115)
  ·
    refine ⟨39335907754806036244749173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26223938503204024163166115 39335907754806036244749173)
    ·
      refine ⟨3687741352013065897945235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39335907754806036244749173 3687741352013065897945235)
      ·
        refine ⟨5531612028019598846917853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3687741352013065897945235 5531612028019598846917853)
        ·
          refine ⟨2074354510507349567594195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5531612028019598846917853 2074354510507349567594195)
          ·
            refine ⟨3111531765761024351391293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074354510507349567594195 3111531765761024351391293)
            ·
              refine ⟨1166824412160384131771735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3111531765761024351391293 1166824412160384131771735)
              ·
                refine ⟨1750236618240576197657603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166824412160384131771735 1750236618240576197657603)
                ·
                  refine ⟨2625354927360864296486405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750236618240576197657603 2625354927360864296486405)
                  ·
                    refine ⟨492254048880162055591201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2625354927360864296486405 492254048880162055591201)
                    ·
                      rfl

theorem cell22_1437992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1437992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1437992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1437992 prefixEnd_1437992 := by exact prefixLift 1437992
  have htrace : WordTrace (prefixWord ++ tailWord_1437992) baseStart_1437992 baseEnd_1437992 := by
    simpa [prefixWord, tailWord_1437992, baseEnd_1437992] using wordTrace_append hprefix tailTrace_1437992
  have hstable : (prefixWord ++ tailWord_1437992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437992).length < 2 ^ (prefixWord ++ tailWord_1437992).sum := by decide
  have hdescent : baseEnd_1437992 < baseStart_1437992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438001 : List Nat := [1, 2, 2, 3, 4, 10]
def baseStart_1438001 : Nat := 118140960795 + 1438001 * 2 ^ 59
def prefixEnd_1438001 : Nat := 4983230072969 + 3 ^ 40 * 1438001 * 2
def baseEnd_1438001 : Nat := 6077248515606037433533

theorem tailTrace_1438001 : CollatzResearch.WordTrace tailWord_1438001 prefixEnd_1438001 6077248515606037433533 := by
  unfold tailWord_1438001
  simp only [CollatzResearch.WordTrace]
  refine ⟨52448205263375442863409857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34965470175583628575606571 52448205263375442863409857)
  ·
    refine ⟨39336153947531582147557393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52448205263375442863409857 39336153947531582147557393)
    ·
      refine ⟨29502115460648686610668045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39336153947531582147557393 29502115460648686610668045)
      ·
        refine ⟨11063293297743257479000517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29502115460648686610668045 11063293297743257479000517)
        ·
          refine ⟨2074367493326860777312597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11063293297743257479000517 2074367493326860777312597)
          ·
            refine ⟨6077248515606037433533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2074367493326860777312597 6077248515606037433533)
            ·
              rfl

theorem cell22_1438001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 10].length) (baseStart_1438001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438001 prefixEnd_1438001 := by exact prefixLift 1438001
  have htrace : WordTrace (prefixWord ++ tailWord_1438001) baseStart_1438001 baseEnd_1438001 := by
    simpa [prefixWord, tailWord_1438001, baseEnd_1438001] using wordTrace_append hprefix tailTrace_1438001
  have hstable : (prefixWord ++ tailWord_1438001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438001).length < 2 ^ (prefixWord ++ tailWord_1438001).sum := by decide
  have hdescent : baseEnd_1438001 < baseStart_1438001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438005 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1438005 : Nat := 118140960795 + 1438005 * 2 ^ 59
def prefixEnd_1438005 : Nat := 4983230072969 + 3 ^ 40 * 1438005 * 2
def baseEnd_1438005 : Nat := 492258499045834355016161

theorem tailTrace_1438005 : CollatzResearch.WordTrace tailWord_1438005 prefixEnd_1438005 492258499045834355016161 := by
  unfold tailWord_1438005
  simp only [CollatzResearch.WordTrace]
  refine ⟨52448351155360951546555469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34965567436907301031036979 52448351155360951546555469)
  ·
    refine ⟨19668131683260356829958301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52448351155360951546555469 19668131683260356829958301)
    ·
      refine ⟨7375549381222633811234363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19668131683260356829958301 7375549381222633811234363)
      ·
        refine ⟨11063324071833950716851545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7375549381222633811234363 11063324071833950716851545)
        ·
          refine ⟨8297493053875463037638659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11063324071833950716851545 8297493053875463037638659)
          ·
            refine ⟨12446239580813194556457989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8297493053875463037638659 12446239580813194556457989)
            ·
              refine ⟨2333669921402473979335873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12446239580813194556457989 2333669921402473979335873)
              ·
                refine ⟨1750252441051855484501905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333669921402473979335873 1750252441051855484501905)
                ·
                  refine ⟨1312689330788891613376429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750252441051855484501905 1312689330788891613376429)
                  ·
                    refine ⟨492258499045834355016161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312689330788891613376429 492258499045834355016161)
                    ·
                      rfl

theorem cell22_1438005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1438005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438005 prefixEnd_1438005 := by exact prefixLift 1438005
  have htrace : WordTrace (prefixWord ++ tailWord_1438005) baseStart_1438005 baseEnd_1438005 := by
    simpa [prefixWord, tailWord_1438005, baseEnd_1438005] using wordTrace_append hprefix tailTrace_1438005
  have hstable : (prefixWord ++ tailWord_1438005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438005).length < 2 ^ (prefixWord ++ tailWord_1438005).sum := by decide
  have hdescent : baseEnd_1438005 < baseStart_1438005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438033 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_1438033 : Nat := 118140960795 + 1438033 * 2 ^ 59
def prefixEnd_1438033 : Nat := 4983230072969 + 3 ^ 40 * 1438033 * 2
def baseEnd_1438033 : Nat := 492268084018051615316075

theorem tailTrace_1438033 : CollatzResearch.WordTrace tailWord_1438033 prefixEnd_1438033 492268084018051615316075 := by
  unfold tailWord_1438033
  simp only [CollatzResearch.WordTrace]
  refine ⟨52449372399259512328574753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34966248266173008219049835 52449372399259512328574753)
  ·
    refine ⟨39337029299444634246431065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52449372399259512328574753 39337029299444634246431065)
    ·
      refine ⟨29502771974583475684823299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39337029299444634246431065 29502771974583475684823299)
      ·
        refine ⟨44254157961875213527234949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29502771974583475684823299 44254157961875213527234949)
        ·
          refine ⟨8297654617851602536356553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44254157961875213527234949 8297654617851602536356553)
          ·
            refine ⟨6223240963388701902267415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8297654617851602536356553 6223240963388701902267415)
            ·
              refine ⟨9334861445083052853401123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223240963388701902267415 9334861445083052853401123)
              ·
                refine ⟨14002292167624579280101685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334861445083052853401123 14002292167624579280101685)
                ·
                  refine ⟨1312714890714804307509533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14002292167624579280101685 1312714890714804307509533)
                  ·
                    refine ⟨492268084018051615316075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312714890714804307509533 492268084018051615316075)
                    ·
                      rfl

theorem cell22_1438033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_1438033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438033 prefixEnd_1438033 := by exact prefixLift 1438033
  have htrace : WordTrace (prefixWord ++ tailWord_1438033) baseStart_1438033 baseEnd_1438033 := by
    simpa [prefixWord, tailWord_1438033, baseEnd_1438033] using wordTrace_append hprefix tailTrace_1438033
  have hstable : (prefixWord ++ tailWord_1438033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438033).length < 2 ^ (prefixWord ++ tailWord_1438033).sum := by decide
  have hdescent : baseEnd_1438033 < baseStart_1438033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438037 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_1438037 : Nat := 118140960795 + 1438037 * 2 ^ 59
def prefixEnd_1438037 : Nat := 4983230072969 + 3 ^ 40 * 1438037 * 2
def baseEnd_1438037 : Nat := 492269453299796938216063

theorem tailTrace_1438037 : CollatzResearch.WordTrace tailWord_1438037 prefixEnd_1438037 492269453299796938216063 := by
  unfold tailWord_1438037
  simp only [CollatzResearch.WordTrace]
  refine ⟨52449518291245021011720365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34966345527496680674480243 52449518291245021011720365)
  ·
    refine ⟨19668569359216882879395137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52449518291245021011720365 19668569359216882879395137)
    ·
      refine ⟨14751427019412662159546353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19668569359216882879395137 14751427019412662159546353)
      ·
        refine ⟨11063570264559496619659765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14751427019412662159546353 11063570264559496619659765)
        ·
          refine ⟨1037209712302452808093103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11063570264559496619659765 1037209712302452808093103)
          ·
            refine ⟨1555814568453679212139655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037209712302452808093103 1555814568453679212139655)
            ·
              refine ⟨2333721852680518818209483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555814568453679212139655 2333721852680518818209483)
              ·
                refine ⟨3500582779020778227314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2333721852680518818209483 3500582779020778227314225)
                ·
                  refine ⟨2625437084265583670485669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3500582779020778227314225 2625437084265583670485669)
                  ·
                    refine ⟨492269453299796938216063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2625437084265583670485669 492269453299796938216063)
                    ·
                      rfl

theorem cell22_1438037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_1438037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438037 prefixEnd_1438037 := by exact prefixLift 1438037
  have htrace : WordTrace (prefixWord ++ tailWord_1438037) baseStart_1438037 baseEnd_1438037 := by
    simpa [prefixWord, tailWord_1438037, baseEnd_1438037] using wordTrace_append hprefix tailTrace_1438037
  have hstable : (prefixWord ++ tailWord_1438037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438037).length < 2 ^ (prefixWord ++ tailWord_1438037).sum := by decide
  have hdescent : baseEnd_1438037 < baseStart_1438037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438076 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1438076 : Nat := 118140960795 + 1438076 * 2 ^ 59
def prefixEnd_1438076 : Nat := 4983230072969 + 3 ^ 40 * 1438076 * 2
def baseEnd_1438076 : Nat := 492282803796813836490943

theorem tailTrace_1438076 : CollatzResearch.WordTrace tailWord_1438076 prefixEnd_1438076 492282803796813836490943 := by
  unfold tailWord_1438076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225470369051865336195041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34967293825402487114926721 26225470369051865336195041)
  ·
    refine ⟨19669102776788899002146281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26225470369051865336195041 19669102776788899002146281)
    ·
      refine ⟨14751827082591674251609711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19669102776788899002146281 14751827082591674251609711)
      ·
        refine ⟨22127740623887511377414567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14751827082591674251609711 22127740623887511377414567)
        ·
          refine ⟨33191610935831267066121851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22127740623887511377414567 33191610935831267066121851)
          ·
            refine ⟨49787416403746900599182777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33191610935831267066121851 49787416403746900599182777)
            ·
              refine ⟨37340562302810175449387083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49787416403746900599182777 37340562302810175449387083)
              ·
                refine ⟨56010843454215263174080625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37340562302810175449387083 56010843454215263174080625)
                ·
                  refine ⟨42008132590661447380560469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56010843454215263174080625 42008132590661447380560469)
                  ·
                    refine ⟨492282803796813836490943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42008132590661447380560469 492282803796813836490943)
                    ·
                      rfl

theorem cell22_1438076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1438076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438076 prefixEnd_1438076 := by exact prefixLift 1438076
  have htrace : WordTrace (prefixWord ++ tailWord_1438076) baseStart_1438076 baseEnd_1438076 := by
    simpa [prefixWord, tailWord_1438076, baseEnd_1438076] using wordTrace_append hprefix tailTrace_1438076
  have hstable : (prefixWord ++ tailWord_1438076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438076).length < 2 ^ (prefixWord ++ tailWord_1438076).sum := by decide
  have hdescent : baseEnd_1438076 < baseStart_1438076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438183 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1438183 : Nat := 118140960795 + 1438183 * 2 ^ 59
def prefixEnd_1438183 : Nat := 4983230072969 + 3 ^ 40 * 1438183 * 2
def baseEnd_1438183 : Nat := 492319432083501224065615

theorem tailTrace_1438183 : CollatzResearch.WordTrace tailWord_1438183 prefixEnd_1438183 492319432083501224065615 := by
  unfold tailWord_1438183
  simp only [CollatzResearch.WordTrace]
  refine ⟨52454843348716087946535203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34969895565810725297690135 52454843348716087946535203)
  ·
    refine ⟨78682265023074131919802805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52454843348716087946535203 78682265023074131919802805)
    ·
      refine ⟨7376462345913199867481513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78682265023074131919802805 7376462345913199867481513)
      ·
        refine ⟨5532346759434899900611135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7376462345913199867481513 5532346759434899900611135)
        ·
          refine ⟨8298520139152349850916703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532346759434899900611135 8298520139152349850916703)
          ·
            refine ⟨12447780208728524776375055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298520139152349850916703 12447780208728524776375055)
            ·
              refine ⟨18671670313092787164562583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12447780208728524776375055 18671670313092787164562583)
              ·
                refine ⟨28007505469639180746843875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18671670313092787164562583 28007505469639180746843875)
                ·
                  refine ⟨42011258204458771120265813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28007505469639180746843875 42011258204458771120265813)
                  ·
                    refine ⟨492319432083501224065615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42011258204458771120265813 492319432083501224065615)
                    ·
                      rfl

theorem cell22_1438183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1438183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438183 prefixEnd_1438183 := by exact prefixLift 1438183
  have htrace : WordTrace (prefixWord ++ tailWord_1438183) baseStart_1438183 baseEnd_1438183 := by
    simpa [prefixWord, tailWord_1438183, baseEnd_1438183] using wordTrace_append hprefix tailTrace_1438183
  have hstable : (prefixWord ++ tailWord_1438183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438183).length < 2 ^ (prefixWord ++ tailWord_1438183).sum := by decide
  have hdescent : baseEnd_1438183 < baseStart_1438183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438219 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 1, 3]
def baseStart_1438219 : Nat := 118140960795 + 1438219 * 2 ^ 59
def prefixEnd_1438219 : Nat := 4983230072969 + 3 ^ 40 * 1438219 * 2
def baseEnd_1438219 : Nat := 492331755619209130165505

theorem tailTrace_1438219 : CollatzResearch.WordTrace tailWord_1438219 prefixEnd_1438219 492331755619209130165505 := by
  unfold tailWord_1438219
  simp only [CollatzResearch.WordTrace]
  refine ⟨52456156376585666094845711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34970770917723777396563807 52456156376585666094845711)
  ·
    refine ⟨78684234564878499142268567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52456156376585666094845711 78684234564878499142268567)
    ·
      refine ⟨118026351847317748713402851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78684234564878499142268567 118026351847317748713402851)
      ·
        refine ⟨177039527770976623070104277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118026351847317748713402851 177039527770976623070104277)
        ·
          refine ⟨4149363932132264603205569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 177039527770976623070104277 4149363932132264603205569)
          ·
            refine ⟨3112022949099198452404177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149363932132264603205569 3112022949099198452404177)
            ·
              refine ⟨2334017211824398839303133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3112022949099198452404177 2334017211824398839303133)
              ·
                refine ⟨875256454434149564738675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334017211824398839303133 875256454434149564738675)
                ·
                  refine ⟨1312884681651224347108013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875256454434149564738675 1312884681651224347108013)
                  ·
                    refine ⟨492331755619209130165505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312884681651224347108013 492331755619209130165505)
                    ·
                      rfl

theorem cell22_1438219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 3].length) (baseStart_1438219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438219 prefixEnd_1438219 := by exact prefixLift 1438219
  have htrace : WordTrace (prefixWord ++ tailWord_1438219) baseStart_1438219 baseEnd_1438219 := by
    simpa [prefixWord, tailWord_1438219, baseEnd_1438219] using wordTrace_append hprefix tailTrace_1438219
  have hstable : (prefixWord ++ tailWord_1438219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438219).length < 2 ^ (prefixWord ++ tailWord_1438219).sum := by decide
  have hdescent : baseEnd_1438219 < baseStart_1438219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438232 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_1438232 : Nat := 118140960795 + 1438232 * 2 ^ 59
def prefixEnd_1438232 : Nat := 4983230072969 + 3 ^ 40 * 1438232 * 2
def baseEnd_1438232 : Nat := 164112068594960476530155

theorem tailTrace_1438232 : CollatzResearch.WordTrace tailWord_1438232 prefixEnd_1438232 164112068594960476530155 := by
  unfold tailWord_1438232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26228315262769284657534475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34971087017025712876712633 26228315262769284657534475)
  ·
    refine ⟨39342472894153926986301713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26228315262769284657534475 39342472894153926986301713)
    ·
      refine ⟨29506854670615445239726285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39342472894153926986301713 29506854670615445239726285)
      ·
        refine ⟨11065070501480791964897357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29506854670615445239726285 11065070501480791964897357)
        ·
          refine ⟨4149401438055296986836509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11065070501480791964897357 4149401438055296986836509)
          ·
            refine ⟨1556025539270736370063691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4149401438055296986836509 1556025539270736370063691)
            ·
              refine ⟨2334038308906104555095537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556025539270736370063691 2334038308906104555095537)
              ·
                refine ⟨1750528731679578416321653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334038308906104555095537 1750528731679578416321653)
                ·
                  refine ⟨164112068594960476530155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1750528731679578416321653 164112068594960476530155)
                  ·
                    rfl

theorem cell22_1438232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_1438232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438232 prefixEnd_1438232 := by exact prefixLift 1438232
  have htrace : WordTrace (prefixWord ++ tailWord_1438232) baseStart_1438232 baseEnd_1438232 := by
    simpa [prefixWord, tailWord_1438232, baseEnd_1438232] using wordTrace_append hprefix tailTrace_1438232
  have hstable : (prefixWord ++ tailWord_1438232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438232).length < 2 ^ (prefixWord ++ tailWord_1438232).sum := by decide
  have hdescent : baseEnd_1438232 < baseStart_1438232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438270 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_1438270 : Nat := 118140960795 + 1438270 * 2 ^ 59
def prefixEnd_1438270 : Nat := 4983230072969 + 3 ^ 40 * 1438270 * 2
def baseEnd_1438270 : Nat := 492349213961461997140349

theorem tailTrace_1438270 : CollatzResearch.WordTrace tailWord_1438270 prefixEnd_1438270 492349213961461997140349 := by
  unfold tailWord_1438270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557252062425112725619033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34972010999600601203301509 6557252062425112725619033)
  ·
    refine ⟨4917939046818834544214275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6557252062425112725619033 4917939046818834544214275)
    ·
      refine ⟨7376908570228251816321413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4917939046818834544214275 7376908570228251816321413)
      ·
        refine ⟨1383170356917797215560265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7376908570228251816321413 1383170356917797215560265)
        ·
          refine ⟨1037377767688347911670199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383170356917797215560265 1037377767688347911670199)
          ·
            refine ⟨1556066651532521867505299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037377767688347911670199 1556066651532521867505299)
            ·
              refine ⟨2334099977298782801257949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556066651532521867505299 2334099977298782801257949)
              ·
                refine ⟨875287491487043550471731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334099977298782801257949 875287491487043550471731)
                ·
                  refine ⟨1312931237230565325707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875287491487043550471731 1312931237230565325707597)
                  ·
                    refine ⟨492349213961461997140349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312931237230565325707597 492349213961461997140349)
                    ·
                      rfl

theorem cell22_1438270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_1438270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438270 prefixEnd_1438270 := by exact prefixLift 1438270
  have htrace : WordTrace (prefixWord ++ tailWord_1438270) baseStart_1438270 baseEnd_1438270 := by
    simpa [prefixWord, tailWord_1438270, baseEnd_1438270] using wordTrace_append hprefix tailTrace_1438270
  have hstable : (prefixWord ++ tailWord_1438270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438270).length < 2 ^ (prefixWord ++ tailWord_1438270).sum := by decide
  have hdescent : baseEnd_1438270 < baseStart_1438270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438277 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 4]
def baseStart_1438277 : Nat := 118140960795 + 1438277 * 2 ^ 59
def prefixEnd_1438277 : Nat := 4983230072969 + 3 ^ 40 * 1438277 * 2
def baseEnd_1438277 : Nat := 164117203401505437405109

theorem tailTrace_1438277 : CollatzResearch.WordTrace tailWord_1438277 prefixEnd_1438277 164117203401505437405109 := by
  unfold tailWord_1438277
  simp only [CollatzResearch.WordTrace]
  refine ⟨52458271810375542000457085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34972181206917028000304723 52458271810375542000457085)
  ·
    refine ⟨19671851928890828250171407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52458271810375542000457085 19671851928890828250171407)
    ·
      refine ⟨29507777893336242375257111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19671851928890828250171407 29507777893336242375257111)
      ·
        refine ⟨44261666840004363562885667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29507777893336242375257111 44261666840004363562885667)
        ·
          refine ⟨66392500260006545344328501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44261666840004363562885667 66392500260006545344328501)
          ·
            refine ⟨6224296899375613626030797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66392500260006545344328501 6224296899375613626030797)
            ·
              refine ⟨2334111337265855109761549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6224296899375613626030797 2334111337265855109761549)
              ·
                refine ⟨875291751474695666160581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334111337265855109761549 875291751474695666160581)
                ·
                  refine ⟨164117203401505437405109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875291751474695666160581 164117203401505437405109)
                  ·
                    rfl

theorem cell22_1438277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_1438277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438277 prefixEnd_1438277 := by exact prefixLift 1438277
  have htrace : WordTrace (prefixWord ++ tailWord_1438277) baseStart_1438277 baseEnd_1438277 := by
    simpa [prefixWord, tailWord_1438277, baseEnd_1438277] using wordTrace_append hprefix tailTrace_1438277
  have hstable : (prefixWord ++ tailWord_1438277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438277).length < 2 ^ (prefixWord ++ tailWord_1438277).sum := by decide
  have hdescent : baseEnd_1438277 < baseStart_1438277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438292 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1438292 : Nat := 118140960795 + 1438292 * 2 ^ 59
def prefixEnd_1438292 : Nat := 4983230072969 + 3 ^ 40 * 1438292 * 2
def baseEnd_1438292 : Nat := 492356745011061273090281

theorem tailTrace_1438292 : CollatzResearch.WordTrace tailWord_1438292 prefixEnd_1438292 492356745011061273090281 := by
  unfold tailWord_1438292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26229409452660599781126565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34972545936880799708168753 26229409452660599781126565)
  ·
    refine ⟨4918014272373862458961231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26229409452660599781126565 4918014272373862458961231)
    ·
      refine ⟨7377021408560793688441847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918014272373862458961231 7377021408560793688441847)
      ·
        refine ⟨11065532112841190532662771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377021408560793688441847 11065532112841190532662771)
        ·
          refine ⟨16598298169261785798994157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11065532112841190532662771 16598298169261785798994157)
          ·
            refine ⟨6224361813473169674622809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16598298169261785798994157 6224361813473169674622809)
            ·
              refine ⟨4668271360104877255967107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6224361813473169674622809 4668271360104877255967107)
              ·
                refine ⟨7002407040157315883950661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668271360104877255967107 7002407040157315883950661)
                ·
                  refine ⟨1312951320029496728240749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7002407040157315883950661 1312951320029496728240749)
                  ·
                    refine ⟨492356745011061273090281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1312951320029496728240749 492356745011061273090281)
                    ·
                      rfl

theorem cell22_1438292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1438292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1438292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1438292 prefixEnd_1438292 := by exact prefixLift 1438292
  have htrace : WordTrace (prefixWord ++ tailWord_1438292) baseStart_1438292 baseEnd_1438292 := by
    simpa [prefixWord, tailWord_1438292, baseEnd_1438292] using wordTrace_append hprefix tailTrace_1438292
  have hstable : (prefixWord ++ tailWord_1438292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438292).length < 2 ^ (prefixWord ++ tailWord_1438292).sum := by decide
  have hdescent : baseEnd_1438292 < baseStart_1438292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
