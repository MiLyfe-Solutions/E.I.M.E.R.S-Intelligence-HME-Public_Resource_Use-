import V185TrunkScan21Chunk104

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1273934 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_1273934 : Nat := 118140960795 + 1273934 * 2 ^ 59
def prefixEnd_1273934 : Nat := 4983230072969 + 3 ^ 40 * 1273934 * 2
def baseEnd_1273934 : Nat := 290729095157743982696129

theorem tailTrace_1273934 : CollatzResearch.WordTrace tailWord_1273934 prefixEnd_1273934 290729095157743982696129 := by
  unfold tailWord_1273934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808023770845270431328607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30976126777841442300419237 5808023770845270431328607)
  ·
    refine ⟨8712035656267905646992911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808023770845270431328607 8712035656267905646992911)
    ·
      refine ⟨13068053484401858470489367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8712035656267905646992911 13068053484401858470489367)
      ·
        refine ⟨19602080226602787705734051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13068053484401858470489367 19602080226602787705734051)
        ·
          refine ⟨29403120339904181558601077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19602080226602787705734051 29403120339904181558601077)
          ·
            refine ⟨2756542531866017021118851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29403120339904181558601077 2756542531866017021118851)
            ·
              refine ⟨4134813797799025531678277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756542531866017021118851 4134813797799025531678277)
              ·
                refine ⟨775277587087317287189677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4134813797799025531678277 775277587087317287189677)
                ·
                  refine ⟨290729095157743982696129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775277587087317287189677 290729095157743982696129)
                  ·
                    rfl

theorem cell21_1273934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_1273934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273934 prefixEnd_1273934 := by exact prefixLift 1273934
  have htrace : WordTrace (prefixWord ++ tailWord_1273934) baseStart_1273934 baseEnd_1273934 := by
    simpa [prefixWord, tailWord_1273934, baseEnd_1273934] using wordTrace_append hprefix tailTrace_1273934
  have hstable : (prefixWord ++ tailWord_1273934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273934).length < 2 ^ (prefixWord ++ tailWord_1273934).sum := by decide
  have hdescent : baseEnd_1273934 < baseStart_1273934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273948 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1273948 : Nat := 118140960795 + 1273948 * 2 ^ 59
def prefixEnd_1273948 : Nat := 4983230072969 + 3 ^ 40 * 1273948 * 2
def baseEnd_1273948 : Nat := 290732290148483069462767

theorem tailTrace_1273948 : CollatzResearch.WordTrace tailWord_1273948 prefixEnd_1273948 290732290148483069462767 := by
  unfold tailWord_1273948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23232350394355721920819249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30976467192474295894425665 23232350394355721920819249)
  ·
    refine ⟨17424262795766791440614437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23232350394355721920819249 17424262795766791440614437)
    ·
      refine ⟨3267049274206273395115207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17424262795766791440614437 3267049274206273395115207)
      ·
        refine ⟨4900573911309410092672811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267049274206273395115207 4900573911309410092672811)
        ·
          refine ⟨7350860866964115139009217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900573911309410092672811 7350860866964115139009217)
          ·
            refine ⟨5513145650223086354256913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7350860866964115139009217 5513145650223086354256913)
            ·
              refine ⟨4134859237667314765692685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513145650223086354256913 4134859237667314765692685)
              ·
                refine ⟨1550572214125243037134757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4134859237667314765692685 1550572214125243037134757)
                ·
                  refine ⟨290732290148483069462767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550572214125243037134757 290732290148483069462767)
                  ·
                    rfl

theorem cell21_1273948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1273948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273948 prefixEnd_1273948 := by exact prefixLift 1273948
  have htrace : WordTrace (prefixWord ++ tailWord_1273948) baseStart_1273948 baseEnd_1273948 := by
    simpa [prefixWord, tailWord_1273948, baseEnd_1273948] using wordTrace_append hprefix tailTrace_1273948
  have hstable : (prefixWord ++ tailWord_1273948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273948).length < 2 ^ (prefixWord ++ tailWord_1273948).sum := by decide
  have hdescent : baseEnd_1273948 < baseStart_1273948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273993 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 3]
def baseStart_1273993 : Nat := 118140960795 + 1273993 * 2 ^ 59
def prefixEnd_1273993 : Nat := 4983230072969 + 3 ^ 40 * 1273993 * 2
def baseEnd_1273993 : Nat := 290742559761572991212675

theorem tailTrace_1273993 : CollatzResearch.WordTrace tailWord_1273993 prefixEnd_1273993 290742559761572991212675 := by
  unfold tailWord_1273993
  simp only [CollatzResearch.WordTrace]
  refine ⟨46466342073548416527026633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30977561382365611018017755 46466342073548416527026633)
  ·
    refine ⟨34849756555161312395269975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46466342073548416527026633 34849756555161312395269975)
    ·
      refine ⟨52274634832741968592904963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34849756555161312395269975 52274634832741968592904963)
      ·
        refine ⟨78411952249112952889357445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52274634832741968592904963 78411952249112952889357445)
        ·
          refine ⟨14702241046708678666754521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78411952249112952889357445 14702241046708678666754521)
          ·
            refine ⟨11026680785031509000065891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14702241046708678666754521 11026680785031509000065891)
            ·
              refine ⟨16540021177547263500098837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11026680785031509000065891 16540021177547263500098837)
              ·
                refine ⟨775313492697527976567133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16540021177547263500098837 775313492697527976567133)
                ·
                  refine ⟨290742559761572991212675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775313492697527976567133 290742559761572991212675)
                  ·
                    rfl

theorem cell21_1273993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_1273993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273993 prefixEnd_1273993 := by exact prefixLift 1273993
  have htrace : WordTrace (prefixWord ++ tailWord_1273993) baseStart_1273993 baseEnd_1273993 := by
    simpa [prefixWord, tailWord_1273993, baseEnd_1273993] using wordTrace_append hprefix tailTrace_1273993
  have hstable : (prefixWord ++ tailWord_1273993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273993).length < 2 ^ (prefixWord ++ tailWord_1273993).sum := by decide
  have hdescent : baseEnd_1273993 < baseStart_1273993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274021 : List Nat := [1, 3, 1, 2, 1, 3, 3, 7]
def baseStart_1274021 : Nat := 118140960795 + 1274021 * 2 ^ 59
def prefixEnd_1274021 : Nat := 4983230072969 + 3 ^ 40 * 1274021 * 2
def baseEnd_1274021 : Nat := 96916316581017054915317

theorem tailTrace_1274021 : CollatzResearch.WordTrace tailWord_1274021 prefixEnd_1274021 96916316581017054915317 := by
  unfold tailWord_1274021
  simp only [CollatzResearch.WordTrace]
  refine ⟨46467363317446977309045917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30978242211631318206030611 46467363317446977309045917)
  ·
    refine ⟨17425261244042616490892219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46467363317446977309045917 17425261244042616490892219)
    ·
      refine ⟨26137891866063924736338329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17425261244042616490892219 26137891866063924736338329)
      ·
        refine ⟨19603418899547943552253747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26137891866063924736338329 19603418899547943552253747)
        ·
          refine ⟨29405128349321915328380621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19603418899547943552253747 29405128349321915328380621)
          ·
            refine ⟨11026923130995718248142733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29405128349321915328380621 11026923130995718248142733)
            ·
              refine ⟨4135096174123394343053525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11026923130995718248142733 4135096174123394343053525)
              ·
                refine ⟨96916316581017054915317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4135096174123394343053525 96916316581017054915317)
                ·
                  rfl

theorem cell21_1274021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_1274021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274021 prefixEnd_1274021 := by exact prefixLift 1274021
  have htrace : WordTrace (prefixWord ++ tailWord_1274021) baseStart_1274021 baseEnd_1274021 := by
    simpa [prefixWord, tailWord_1274021, baseEnd_1274021] using wordTrace_append hprefix tailTrace_1274021
  have hstable : (prefixWord ++ tailWord_1274021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274021).length < 2 ^ (prefixWord ++ tailWord_1274021).sum := by decide
  have hdescent : baseEnd_1274021 < baseStart_1274021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274145 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 3]
def baseStart_1274145 : Nat := 118140960795 + 1274145 * 2 ^ 59
def prefixEnd_1274145 : Nat := 4983230072969 + 3 ^ 40 * 1274145 * 2
def baseEnd_1274145 : Nat := 290777248232454504679031

theorem tailTrace_1274145 : CollatzResearch.WordTrace tailWord_1274145 prefixEnd_1274145 290777248232454504679031 := by
  unfold tailWord_1274145
  simp only [CollatzResearch.WordTrace]
  refine ⟨46471885968997746486559889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30981257312665164324373259 46471885968997746486559889)
  ·
    refine ⟨34853914476748309864919917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46471885968997746486559889 34853914476748309864919917)
    ·
      refine ⟨13070217928780616199344969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34853914476748309864919917 13070217928780616199344969)
      ·
        refine ⟨9802663446585462149508727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13070217928780616199344969 9802663446585462149508727)
        ·
          refine ⟨14703995169878193224263091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802663446585462149508727 14703995169878193224263091)
          ·
            refine ⟨22055992754817289836394637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703995169878193224263091 22055992754817289836394637)
            ·
              refine ⟨8270997283056483688647989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22055992754817289836394637 8270997283056483688647989)
              ·
                refine ⟨775405995286545345810749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8270997283056483688647989 775405995286545345810749)
                ·
                  refine ⟨290777248232454504679031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775405995286545345810749 290777248232454504679031)
                  ·
                    rfl

theorem cell21_1274145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_1274145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274145 prefixEnd_1274145 := by exact prefixLift 1274145
  have htrace : WordTrace (prefixWord ++ tailWord_1274145) baseStart_1274145 baseEnd_1274145 := by
    simpa [prefixWord, tailWord_1274145, baseEnd_1274145] using wordTrace_append hprefix tailTrace_1274145
  have hstable : (prefixWord ++ tailWord_1274145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274145).length < 2 ^ (prefixWord ++ tailWord_1274145).sum := by decide
  have hdescent : baseEnd_1274145 < baseStart_1274145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274151 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 4]
def baseStart_1274151 : Nat := 118140960795 + 1274151 * 2 ^ 59
def prefixEnd_1274151 : Nat := 4983230072969 + 3 ^ 40 * 1274151 * 2
def baseEnd_1274151 : Nat := 290778617514199827579019

theorem tailTrace_1274151 : CollatzResearch.WordTrace tailWord_1274151 prefixEnd_1274151 290778617514199827579019 := by
  unfold tailWord_1274151
  simp only [CollatzResearch.WordTrace]
  refine ⟨46472104806976009511278307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30981403204650673007518871 46472104806976009511278307)
  ·
    refine ⟨69708157210464014266917461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46472104806976009511278307 69708157210464014266917461)
    ·
      refine ⟨816892467310125167190439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 69708157210464014266917461 816892467310125167190439)
      ·
        refine ⟨1225338700965187750785659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816892467310125167190439 1225338700965187750785659)
        ·
          refine ⟨1838008051447781626178489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225338700965187750785659 1838008051447781626178489)
          ·
            refine ⟨1378506038585836219633867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838008051447781626178489 1378506038585836219633867)
            ·
              refine ⟨2067759057878754329450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378506038585836219633867 2067759057878754329450801)
              ·
                refine ⟨1550819293409065747088101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067759057878754329450801 1550819293409065747088101)
                ·
                  refine ⟨290778617514199827579019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550819293409065747088101 290778617514199827579019)
                  ·
                    rfl

theorem cell21_1274151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4].length) (baseStart_1274151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274151 prefixEnd_1274151 := by exact prefixLift 1274151
  have htrace : WordTrace (prefixWord ++ tailWord_1274151) baseStart_1274151 baseEnd_1274151 := by
    simpa [prefixWord, tailWord_1274151, baseEnd_1274151] using wordTrace_append hprefix tailTrace_1274151
  have hstable : (prefixWord ++ tailWord_1274151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274151).length < 2 ^ (prefixWord ++ tailWord_1274151).sum := by decide
  have hdescent : baseEnd_1274151 < baseStart_1274151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274159 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_1274159 : Nat := 118140960795 + 1274159 * 2 ^ 59
def prefixEnd_1274159 : Nat := 4983230072969 + 3 ^ 40 * 1274159 * 2
def baseEnd_1274159 : Nat := 290780443223193591445669

theorem tailTrace_1274159 : CollatzResearch.WordTrace tailWord_1274159 prefixEnd_1274159 290780443223193591445669 := by
  unfold tailWord_1274159
  simp only [CollatzResearch.WordTrace]
  refine ⟨46472396590947026877569531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30981597727298017918379687 46472396590947026877569531)
  ·
    refine ⟨69708594886420540316354297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46472396590947026877569531 69708594886420540316354297)
    ·
      refine ⟨52281446164815405237265723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69708594886420540316354297 52281446164815405237265723)
      ·
        refine ⟨78422169247223107855898585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52281446164815405237265723 78422169247223107855898585)
        ·
          refine ⟨58816626935417330891923939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78422169247223107855898585 58816626935417330891923939)
          ·
            refine ⟨88224940403125996337885909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58816626935417330891923939 88224940403125996337885909)
            ·
              refine ⟨2067772040698265539169201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 88224940403125996337885909 2067772040698265539169201)
              ·
                refine ⟨1550829030523699154376901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067772040698265539169201 1550829030523699154376901)
                ·
                  refine ⟨290780443223193591445669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550829030523699154376901 290780443223193591445669)
                  ·
                    rfl

theorem cell21_1274159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_1274159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274159 prefixEnd_1274159 := by exact prefixLift 1274159
  have htrace : WordTrace (prefixWord ++ tailWord_1274159) baseStart_1274159 baseEnd_1274159 := by
    simpa [prefixWord, tailWord_1274159, baseEnd_1274159] using wordTrace_append hprefix tailTrace_1274159
  have hstable : (prefixWord ++ tailWord_1274159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274159).length < 2 ^ (prefixWord ++ tailWord_1274159).sum := by decide
  have hdescent : baseEnd_1274159 < baseStart_1274159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274187 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_1274187 : Nat := 118140960795 + 1274187 * 2 ^ 59
def prefixEnd_1274187 : Nat := 4983230072969 + 3 ^ 40 * 1274187 * 2
def baseEnd_1274187 : Nat := 290786833204671764978945

theorem tailTrace_1274187 : CollatzResearch.WordTrace tailWord_1274187 prefixEnd_1274187 290786833204671764978945 := by
  unfold tailWord_1274187
  simp only [CollatzResearch.WordTrace]
  refine ⟨46473417834845587659588815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30982278556563725106392543 46473417834845587659588815)
  ·
    refine ⟨69710126752268381489383223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46473417834845587659588815 69710126752268381489383223)
    ·
      refine ⟨104565190128402572234074835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69710126752268381489383223 104565190128402572234074835)
      ·
        refine ⟨156847785192603858351112253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104565190128402572234074835 156847785192603858351112253)
        ·
          refine ⟨58817919447226446881667095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156847785192603858351112253 58817919447226446881667095)
          ·
            refine ⟨88226879170839670322500643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58817919447226446881667095 88226879170839670322500643)
            ·
              refine ⟨132340318756259505483750965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88226879170839670322500643 132340318756259505483750965)
              ·
                refine ⟨12406904883399328639101653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132340318756259505483750965 12406904883399328639101653)
                ·
                  refine ⟨290786833204671764978945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12406904883399328639101653 290786833204671764978945)
                  ·
                    rfl

theorem cell21_1274187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_1274187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274187 prefixEnd_1274187 := by exact prefixLift 1274187
  have htrace : WordTrace (prefixWord ++ tailWord_1274187) baseStart_1274187 baseEnd_1274187 := by
    simpa [prefixWord, tailWord_1274187, baseEnd_1274187] using wordTrace_append hprefix tailTrace_1274187
  have hstable : (prefixWord ++ tailWord_1274187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274187).length < 2 ^ (prefixWord ++ tailWord_1274187).sum := by decide
  have hdescent : baseEnd_1274187 < baseStart_1274187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274235 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_1274235 : Nat := 118140960795 + 1274235 * 2 ^ 59
def prefixEnd_1274235 : Nat := 4983230072969 + 3 ^ 40 * 1274235 * 2
def baseEnd_1274235 : Nat := 290797787458634348178847

theorem tailTrace_1274235 : CollatzResearch.WordTrace tailWord_1274235 prefixEnd_1274235 290797787458634348178847 := by
  unfold tailWord_1274235
  simp only [CollatzResearch.WordTrace]
  refine ⟨46475168538671691857336159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30983445692447794571557439 46475168538671691857336159)
  ·
    refine ⟨69712752808007537786004239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46475168538671691857336159 69712752808007537786004239)
    ·
      refine ⟨104569129212011306679006359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69712752808007537786004239 104569129212011306679006359)
      ·
        refine ⟨156853693818016960018509539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104569129212011306679006359 156853693818016960018509539)
        ·
          refine ⟨235280540727025440027764309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156853693818016960018509539 235280540727025440027764309)
          ·
            refine ⟨2757193836644829375325363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 235280540727025440027764309 2757193836644829375325363)
            ·
              refine ⟨4135790754967244062988045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757193836644829375325363 4135790754967244062988045)
              ·
                refine ⟨1550921533112716523620517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135790754967244062988045 1550921533112716523620517)
                ·
                  refine ⟨290797787458634348178847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550921533112716523620517 290797787458634348178847)
                  ·
                    rfl

theorem cell21_1274235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_1274235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274235 prefixEnd_1274235 := by exact prefixLift 1274235
  have htrace : WordTrace (prefixWord ++ tailWord_1274235) baseStart_1274235 baseEnd_1274235 := by
    simpa [prefixWord, tailWord_1274235, baseEnd_1274235] using wordTrace_append hprefix tailTrace_1274235
  have hstable : (prefixWord ++ tailWord_1274235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274235).length < 2 ^ (prefixWord ++ tailWord_1274235).sum := by decide
  have hdescent : baseEnd_1274235 < baseStart_1274235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274249 : List Nat := [1, 2, 1, 1, 6, 1, 2, 7]
def baseStart_1274249 : Nat := 118140960795 + 1274249 * 2 ^ 59
def prefixEnd_1274249 : Nat := 4983230072969 + 3 ^ 40 * 1274249 * 2
def baseEnd_1274249 : Nat := 96933660816457811648495

theorem tailTrace_1274249 : CollatzResearch.WordTrace tailWord_1274249 prefixEnd_1274249 96933660816457811648495 := by
  unfold tailWord_1274249
  simp only [CollatzResearch.WordTrace]
  refine ⟨46475679160620972248345801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30983786107080648165563867 46475679160620972248345801)
  ·
    refine ⟨34856759370465729186259351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46475679160620972248345801 34856759370465729186259351)
    ·
      refine ⟨52285139055698593779389027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34856759370465729186259351 52285139055698593779389027)
      ·
        refine ⟨78427708583547890669083541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52285139055698593779389027 78427708583547890669083541)
        ·
          refine ⟨3676298839853807375113291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78427708583547890669083541 3676298839853807375113291)
          ·
            refine ⟨5514448259780711062669937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676298839853807375113291 5514448259780711062669937)
            ·
              refine ⟨4135836194835533297002453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5514448259780711062669937 4135836194835533297002453)
              ·
                refine ⟨96933660816457811648495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4135836194835533297002453 96933660816457811648495)
                ·
                  rfl

theorem cell21_1274249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_1274249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274249 prefixEnd_1274249 := by exact prefixLift 1274249
  have htrace : WordTrace (prefixWord ++ tailWord_1274249) baseStart_1274249 baseEnd_1274249 := by
    simpa [prefixWord, tailWord_1274249, baseEnd_1274249] using wordTrace_append hprefix tailTrace_1274249
  have hstable : (prefixWord ++ tailWord_1274249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274249).length < 2 ^ (prefixWord ++ tailWord_1274249).sum := by decide
  have hdescent : baseEnd_1274249 < baseStart_1274249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274325 : List Nat := [1, 3, 2, 3, 1, 3, 8]
def baseStart_1274325 : Nat := 118140960795 + 1274325 * 2 ^ 59
def prefixEnd_1274325 : Nat := 4983230072969 + 3 ^ 40 * 1274325 * 2
def baseEnd_1274325 : Nat := 32313147409423799075407

theorem tailTrace_1274325 : CollatzResearch.WordTrace tailWord_1274325 prefixEnd_1274325 32313147409423799075407 := by
  unfold tailWord_1274325
  simp only [CollatzResearch.WordTrace]
  refine ⟨46478451108345637228112429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30985634072230424818741619 46478451108345637228112429)
  ·
    refine ⟨17429419165629613960542161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46478451108345637228112429 17429419165629613960542161)
    ·
      refine ⟨13072064374222210470406621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17429419165629613960542161 13072064374222210470406621)
      ·
        refine ⟨4902024140333328926402483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13072064374222210470406621 4902024140333328926402483)
        ·
          refine ⟨7353036210499993389603725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902024140333328926402483 7353036210499993389603725)
          ·
            refine ⟨2757388578937497521101397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7353036210499993389603725 2757388578937497521101397)
            ·
              refine ⟨32313147409423799075407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2757388578937497521101397 32313147409423799075407)
              ·
                rfl

theorem cell21_1274325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 8].length) (baseStart_1274325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274325 prefixEnd_1274325 := by exact prefixLift 1274325
  have htrace : WordTrace (prefixWord ++ tailWord_1274325) baseStart_1274325 baseEnd_1274325 := by
    simpa [prefixWord, tailWord_1274325, baseEnd_1274325] using wordTrace_append hprefix tailTrace_1274325
  have hstable : (prefixWord ++ tailWord_1274325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274325).length < 2 ^ (prefixWord ++ tailWord_1274325).sum := by decide
  have hdescent : baseEnd_1274325 < baseStart_1274325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274373 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 3]
def baseStart_1274373 : Nat := 118140960795 + 1274373 * 2 ^ 59
def prefixEnd_1274373 : Nat := 4983230072969 + 3 ^ 40 * 1274373 * 2
def baseEnd_1274373 : Nat := 290829280938776774878565

theorem tailTrace_1274373 : CollatzResearch.WordTrace tailWord_1274373 prefixEnd_1274373 290829280938776774878565 := by
  unfold tailWord_1274373
  simp only [CollatzResearch.WordTrace]
  refine ⟨46480201812171741425859773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30986801208114494283906515 46480201812171741425859773)
  ·
    refine ⟨17430075679564403034697415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46480201812171741425859773 17430075679564403034697415)
    ·
      refine ⟨26145113519346604552046123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17430075679564403034697415 26145113519346604552046123)
      ·
        refine ⟨39217670279019906828069185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26145113519346604552046123 39217670279019906828069185)
        ·
          refine ⟨29413252709264930121051889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39217670279019906828069185 29413252709264930121051889)
          ·
            refine ⟨22059939531948697590788917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29413252709264930121051889 22059939531948697590788917)
            ·
              refine ⟨2068119331120190399136461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22059939531948697590788917 2068119331120190399136461)
              ·
                refine ⟨775544749170071399676173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2068119331120190399136461 775544749170071399676173)
                ·
                  refine ⟨290829280938776774878565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775544749170071399676173 290829280938776774878565)
                  ·
                    rfl

theorem cell21_1274373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_1274373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274373 prefixEnd_1274373 := by exact prefixLift 1274373
  have htrace : WordTrace (prefixWord ++ tailWord_1274373) baseStart_1274373 baseEnd_1274373 := by
    simpa [prefixWord, tailWord_1274373, baseEnd_1274373] using wordTrace_append hprefix tailTrace_1274373
  have hstable : (prefixWord ++ tailWord_1274373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274373).length < 2 ^ (prefixWord ++ tailWord_1274373).sum := by decide
  have hdescent : baseEnd_1274373 < baseStart_1274373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274401 : List Nat := [1, 2, 3, 2, 2, 1, 4, 6]
def baseStart_1274401 : Nat := 118140960795 + 1274401 * 2 ^ 59
def prefixEnd_1274401 : Nat := 4983230072969 + 3 ^ 40 * 1274401 * 2
def baseEnd_1274401 : Nat := 96945223640084982803947

theorem tailTrace_1274401 : CollatzResearch.WordTrace tailWord_1274401 prefixEnd_1274401 96945223640084982803947 := by
  unfold tailWord_1274401
  simp only [CollatzResearch.WordTrace]
  refine ⟨46481223056070302207879057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30987482037380201471919371 46481223056070302207879057)
  ·
    refine ⟨34860917292052726655909293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46481223056070302207879057 34860917292052726655909293)
    ·
      refine ⟨13072843984519772495965985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34860917292052726655909293 13072843984519772495965985)
      ·
        refine ⟨9804632988389829371974489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13072843984519772495965985 9804632988389829371974489)
        ·
          refine ⟨7353474741292372028980867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9804632988389829371974489 7353474741292372028980867)
          ·
            refine ⟨11030212111938558043471301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353474741292372028980867 11030212111938558043471301)
            ·
              refine ⟨2068164770988479633150869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11030212111938558043471301 2068164770988479633150869)
              ·
                refine ⟨96945223640084982803947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2068164770988479633150869 96945223640084982803947)
                ·
                  rfl

theorem cell21_1274401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_1274401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274401 prefixEnd_1274401 := by exact prefixLift 1274401
  have htrace : WordTrace (prefixWord ++ tailWord_1274401) baseStart_1274401 baseEnd_1274401 := by
    simpa [prefixWord, tailWord_1274401, baseEnd_1274401] using wordTrace_append hprefix tailTrace_1274401
  have hstable : (prefixWord ++ tailWord_1274401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274401).length < 2 ^ (prefixWord ++ tailWord_1274401).sum := by decide
  have hdescent : baseEnd_1274401 < baseStart_1274401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274446 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1274446 : Nat := 118140960795 + 1274446 * 2 ^ 59
def prefixEnd_1274446 : Nat := 4983230072969 + 3 ^ 40 * 1274446 * 2
def baseEnd_1274446 : Nat := 290845940533344870161749

theorem tailTrace_1274446 : CollatzResearch.WordTrace tailWord_1274446 prefixEnd_1274446 290845940533344870161749 := by
  unfold tailWord_1274446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810358042613409361658399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30988576227271516595511461 5810358042613409361658399)
  ·
    refine ⟨8715537063920114042487599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5810358042613409361658399 8715537063920114042487599)
    ·
      refine ⟨13073305595880171063731399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8715537063920114042487599 13073305595880171063731399)
      ·
        refine ⟨19609958393820256595597099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13073305595880171063731399 19609958393820256595597099)
        ·
          refine ⟨29414937590730384893395649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19609958393820256595597099 29414937590730384893395649)
          ·
            refine ⟨22061203193047788670046737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29414937590730384893395649 22061203193047788670046737)
            ·
              refine ⟨16545902394785841502535053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22061203193047788670046737 16545902394785841502535053)
              ·
                refine ⟨6204713398044690563450645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16545902394785841502535053 6204713398044690563450645)
                ·
                  refine ⟨290845940533344870161749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6204713398044690563450645 290845940533344870161749)
                  ·
                    rfl

theorem cell21_1274446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1274446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274446 prefixEnd_1274446 := by exact prefixLift 1274446
  have htrace : WordTrace (prefixWord ++ tailWord_1274446) baseStart_1274446 baseEnd_1274446 := by
    simpa [prefixWord, tailWord_1274446, baseEnd_1274446] using wordTrace_append hprefix tailTrace_1274446
  have hstable : (prefixWord ++ tailWord_1274446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274446).length < 2 ^ (prefixWord ++ tailWord_1274446).sum := by decide
  have hdescent : baseEnd_1274446 < baseStart_1274446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274449 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 3]
def baseStart_1274449 : Nat := 118140960795 + 1274449 * 2 ^ 59
def prefixEnd_1274449 : Nat := 4983230072969 + 3 ^ 40 * 1274449 * 2
def baseEnd_1274449 : Nat := 290846625174217531611743

theorem tailTrace_1274449 : CollatzResearch.WordTrace tailWord_1274449 prefixEnd_1274449 290846625174217531611743 := by
  unfold tailWord_1274449
  simp only [CollatzResearch.WordTrace]
  refine ⟨46482973759896406405626401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30988649173264270937084267 46482973759896406405626401)
  ·
    refine ⟨34862230319922304804219801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46482973759896406405626401 34862230319922304804219801)
    ·
      refine ⟨26146672739941728603164851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34862230319922304804219801 26146672739941728603164851)
      ·
        refine ⟨39220009109912592904747277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26146672739941728603164851 39220009109912592904747277)
        ·
          refine ⟨14707503416217222339280229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39220009109912592904747277 14707503416217222339280229)
          ·
            refine ⟨2757656890540729188615043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14707503416217222339280229 2757656890540729188615043)
            ·
              refine ⟨4136485335811093782922565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757656890540729188615043 4136485335811093782922565)
              ·
                refine ⟨775591000464580084297981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4136485335811093782922565 775591000464580084297981)
                ·
                  refine ⟨290846625174217531611743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775591000464580084297981 290846625174217531611743)
                  ·
                    rfl

theorem cell21_1274449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_1274449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274449 prefixEnd_1274449 := by exact prefixLift 1274449
  have htrace : WordTrace (prefixWord ++ tailWord_1274449) baseStart_1274449 baseEnd_1274449 := by
    simpa [prefixWord, tailWord_1274449, baseEnd_1274449] using wordTrace_append hprefix tailTrace_1274449
  have hstable : (prefixWord ++ tailWord_1274449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274449).length < 2 ^ (prefixWord ++ tailWord_1274449).sum := by decide
  have hdescent : baseEnd_1274449 < baseStart_1274449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274466 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1274466 : Nat := 118140960795 + 1274466 * 2 ^ 59
def prefixEnd_1274466 : Nat := 4983230072969 + 3 ^ 40 * 1274466 * 2
def baseEnd_1274466 : Nat := 290850504805829279828375

theorem tailTrace_1274466 : CollatzResearch.WordTrace tailWord_1274466 prefixEnd_1274466 290850504805829279828375 := by
  unfold tailWord_1274466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620898450208704577248813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30989062533889878872663501 11620898450208704577248813)
  ·
    refine ⟨4357836918828264216468305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11620898450208704577248813 4357836918828264216468305)
    ·
      refine ⟨3268377689121198162351229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4357836918828264216468305 3268377689121198162351229)
      ·
        refine ⟨1225641633420449310881711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3268377689121198162351229 1225641633420449310881711)
        ·
          refine ⟨1838462450130673966322567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225641633420449310881711 1838462450130673966322567)
          ·
            refine ⟨2757693675196010949483851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838462450130673966322567 2757693675196010949483851)
            ·
              refine ⟨4136540512794016424225777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757693675196010949483851 4136540512794016424225777)
              ·
                refine ⟨3102405384595512318169333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4136540512794016424225777 3102405384595512318169333)
                ·
                  refine ⟨290850504805829279828375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102405384595512318169333 290850504805829279828375)
                  ·
                    rfl

theorem cell21_1274466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1274466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274466 prefixEnd_1274466 := by exact prefixLift 1274466
  have htrace : WordTrace (prefixWord ++ tailWord_1274466) baseStart_1274466 baseEnd_1274466 := by
    simpa [prefixWord, tailWord_1274466, baseEnd_1274466] using wordTrace_append hprefix tailTrace_1274466
  have hstable : (prefixWord ++ tailWord_1274466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274466).length < 2 ^ (prefixWord ++ tailWord_1274466).sum := by decide
  have hdescent : baseEnd_1274466 < baseStart_1274466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274567 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_1274567 : Nat := 118140960795 + 1274567 * 2 ^ 59
def prefixEnd_1274567 : Nat := 4983230072969 + 3 ^ 40 * 1274567 * 2
def baseEnd_1274567 : Nat := 290873554381875548644835

theorem tailTrace_1274567 : CollatzResearch.WordTrace tailWord_1274567 prefixEnd_1274567 290873554381875548644835 := by
  unfold tailWord_1274567
  simp only [CollatzResearch.WordTrace]
  refine ⟨46487277573468912558421955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30991518382312608372281303 46487277573468912558421955)
  ·
    refine ⟨69730916360203368837632933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46487277573468912558421955 69730916360203368837632933)
    ·
      refine ⟨13074546817538131657056175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69730916360203368837632933 13074546817538131657056175)
      ·
        refine ⟨19611820226307197485584263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13074546817538131657056175 19611820226307197485584263)
        ·
          refine ⟨29417730339460796228376395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19611820226307197485584263 29417730339460796228376395)
          ·
            refine ⟨44126595509191194342564593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29417730339460796228376395 44126595509191194342564593)
            ·
              refine ⟨33094946631893395756923445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44126595509191194342564593 33094946631893395756923445)
              ·
                refine ⟨3102651246740005852211573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33094946631893395756923445 3102651246740005852211573)
                ·
                  refine ⟨290873554381875548644835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102651246740005852211573 290873554381875548644835)
                  ·
                    rfl

theorem cell21_1274567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_1274567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274567 prefixEnd_1274567 := by exact prefixLift 1274567
  have htrace : WordTrace (prefixWord ++ tailWord_1274567) baseStart_1274567 baseEnd_1274567 := by
    simpa [prefixWord, tailWord_1274567, baseEnd_1274567] using wordTrace_append hprefix tailTrace_1274567
  have hstable : (prefixWord ++ tailWord_1274567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274567).length < 2 ^ (prefixWord ++ tailWord_1274567).sum := by decide
  have hdescent : baseEnd_1274567 < baseStart_1274567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274573 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1274573 : Nat := 118140960795 + 1274573 * 2 ^ 59
def prefixEnd_1274573 : Nat := 4983230072969 + 3 ^ 40 * 1274573 * 2
def baseEnd_1274573 : Nat := 290874923663620871544823

theorem tailTrace_1274573 : CollatzResearch.WordTrace tailWord_1274573 prefixEnd_1274573 290874923663620871544823 := by
  unfold tailWord_1274573
  simp only [CollatzResearch.WordTrace]
  refine ⟨46487496411447175583140373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30991664274298117055426915 46487496411447175583140373)
  ·
    refine ⟨2179101394286586355459705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46487496411447175583140373 2179101394286586355459705)
    ·
      refine ⟨1634326045714939766594779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2179101394286586355459705 1634326045714939766594779)
      ·
        refine ⟨2451489068572409649892169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634326045714939766594779 2451489068572409649892169)
        ·
          refine ⟨1838616801429307237419127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2451489068572409649892169 1838616801429307237419127)
          ·
            refine ⟨2757925202143960856128691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838616801429307237419127 2757925202143960856128691)
            ·
              refine ⟨4136887803215941284193037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757925202143960856128691 4136887803215941284193037)
              ·
                refine ⟨1551332926205977981572389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4136887803215941284193037 1551332926205977981572389)
                ·
                  refine ⟨290874923663620871544823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551332926205977981572389 290874923663620871544823)
                  ·
                    rfl

theorem cell21_1274573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1274573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274573 prefixEnd_1274573 := by exact prefixLift 1274573
  have htrace : WordTrace (prefixWord ++ tailWord_1274573) baseStart_1274573 baseEnd_1274573 := by
    simpa [prefixWord, tailWord_1274573, baseEnd_1274573] using wordTrace_append hprefix tailTrace_1274573
  have hstable : (prefixWord ++ tailWord_1274573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274573).length < 2 ^ (prefixWord ++ tailWord_1274573).sum := by decide
  have hdescent : baseEnd_1274573 < baseStart_1274573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274643 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_1274643 : Nat := 118140960795 + 1274643 * 2 ^ 59
def prefixEnd_1274643 : Nat := 4983230072969 + 3 ^ 40 * 1274643 * 2
def baseEnd_1274643 : Nat := 290890898617316305378013

theorem tailTrace_1274643 : CollatzResearch.WordTrace tailWord_1274643 prefixEnd_1274643 290890898617316305378013 := by
  unfold tailWord_1274643
  simp only [CollatzResearch.WordTrace]
  refine ⟨46490049521193577538188583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30993366347462385025459055 46490049521193577538188583)
  ·
    refine ⟨69735074281790366307282875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46490049521193577538188583 69735074281790366307282875)
    ·
      refine ⟨104602611422685549460924313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69735074281790366307282875 104602611422685549460924313)
      ·
        refine ⟨78451958567014162095693235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104602611422685549460924313 78451958567014162095693235)
        ·
          refine ⟨117677937850521243143539853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78451958567014162095693235 117677937850521243143539853)
          ·
            refine ⟨44129226693945466178827445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117677937850521243143539853 44129226693945466178827445)
            ·
              refine ⟨4137115002557387454265073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44129226693945466178827445 4137115002557387454265073)
              ·
                refine ⟨3102836251918040590698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137115002557387454265073 3102836251918040590698805)
                ·
                  refine ⟨290890898617316305378013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102836251918040590698805 290890898617316305378013)
                  ·
                    rfl

theorem cell21_1274643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_1274643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274643 prefixEnd_1274643 := by exact prefixLift 1274643
  have htrace : WordTrace (prefixWord ++ tailWord_1274643) baseStart_1274643 baseEnd_1274643 := by
    simpa [prefixWord, tailWord_1274643, baseEnd_1274643] using wordTrace_append hprefix tailTrace_1274643
  have hstable : (prefixWord ++ tailWord_1274643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274643).length < 2 ^ (prefixWord ++ tailWord_1274643).sum := by decide
  have hdescent : baseEnd_1274643 < baseStart_1274643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274666 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_1274666 : Nat := 118140960795 + 1274666 * 2 ^ 59
def prefixEnd_1274666 : Nat := 4983230072969 + 3 ^ 40 * 1274666 * 2
def baseEnd_1274666 : Nat := 290896147530673376494633

theorem tailTrace_1274666 : CollatzResearch.WordTrace tailWord_1274666 prefixEnd_1274666 290896147530673376494633 := by
  unfold tailWord_1274666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622722100027563116568963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30993925600073501644183901 11622722100027563116568963)
  ·
    refine ⟨17434083150041344674853445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11622722100027563116568963 17434083150041344674853445)
    ·
      refine ⟨3268890590632752126535021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17434083150041344674853445 3268890590632752126535021)
      ·
        refine ⟨1225833971487282047450633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3268890590632752126535021 1225833971487282047450633)
        ·
          refine ⟨919375478615461535587975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225833971487282047450633 919375478615461535587975)
          ·
            refine ⟨1379063217923192303381963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919375478615461535587975 1379063217923192303381963)
            ·
              refine ⟨2068594826884788455072945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379063217923192303381963 2068594826884788455072945)
              ·
                refine ⟨1551446120163591341304709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068594826884788455072945 1551446120163591341304709)
                ·
                  refine ⟨290896147530673376494633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551446120163591341304709 290896147530673376494633)
                  ·
                    rfl

theorem cell21_1274666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_1274666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274666 prefixEnd_1274666 := by exact prefixLift 1274666
  have htrace : WordTrace (prefixWord ++ tailWord_1274666) baseStart_1274666 baseEnd_1274666 := by
    simpa [prefixWord, tailWord_1274666, baseEnd_1274666] using wordTrace_append hprefix tailTrace_1274666
  have hstable : (prefixWord ++ tailWord_1274666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274666).length < 2 ^ (prefixWord ++ tailWord_1274666).sum := by decide
  have hdescent : baseEnd_1274666 < baseStart_1274666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274674 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1274674 : Nat := 118140960795 + 1274674 * 2 ^ 59
def prefixEnd_1274674 : Nat := 4983230072969 + 3 ^ 40 * 1274674 * 2
def baseEnd_1274674 : Nat := 290897973239667140361283

theorem tailTrace_1274674 : CollatzResearch.WordTrace tailWord_1274674 prefixEnd_1274674 290897973239667140361283 := by
  unfold tailWord_1274674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622795046020317458141769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30994120122720846555044717 11622795046020317458141769)
  ·
    refine ⟨8717096284515238093606327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11622795046020317458141769 8717096284515238093606327)
    ·
      refine ⟨13075644426772857140409491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8717096284515238093606327 13075644426772857140409491)
      ·
        refine ⟨19613466640159285710614237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13075644426772857140409491 19613466640159285710614237)
        ·
          refine ⟨7355049990059732141480339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19613466640159285710614237 7355049990059732141480339)
          ·
            refine ⟨11032574985089598212220509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355049990059732141480339 11032574985089598212220509)
            ·
              refine ⟨4137215619408599329582691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11032574985089598212220509 4137215619408599329582691)
              ·
                refine ⟨6205823429112898994374037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137215619408599329582691 6205823429112898994374037)
                ·
                  refine ⟨290897973239667140361283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6205823429112898994374037 290897973239667140361283)
                  ·
                    rfl

theorem cell21_1274674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1274674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274674 prefixEnd_1274674 := by exact prefixLift 1274674
  have htrace : WordTrace (prefixWord ++ tailWord_1274674) baseStart_1274674 baseEnd_1274674 := by
    simpa [prefixWord, tailWord_1274674, baseEnd_1274674] using wordTrace_append hprefix tailTrace_1274674
  have hstable : (prefixWord ++ tailWord_1274674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274674).length < 2 ^ (prefixWord ++ tailWord_1274674).sum := by decide
  have hdescent : baseEnd_1274674 < baseStart_1274674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274677 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 3]
def baseStart_1274677 : Nat := 118140960795 + 1274677 * 2 ^ 59
def prefixEnd_1274677 : Nat := 4983230072969 + 3 ^ 40 * 1274677 * 2
def baseEnd_1274677 : Nat := 290898657880539801811277

theorem tailTrace_1274677 : CollatzResearch.WordTrace tailWord_1274677 prefixEnd_1274677 290898657880539801811277 := by
  unfold tailWord_1274677
  simp only [CollatzResearch.WordTrace]
  refine ⟨46491289603070401344926285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30994193068713600896617523 46491289603070401344926285)
  ·
    refine ⟨17434233601151400504347357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46491289603070401344926285 17434233601151400504347357)
    ·
      refine ⟨6537837600431775189130259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17434233601151400504347357 6537837600431775189130259)
      ·
        refine ⟨9806756400647662783695389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6537837600431775189130259 9806756400647662783695389)
        ·
          refine ⟨3677533650242873543885771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9806756400647662783695389 3677533650242873543885771)
          ·
            refine ⟨5516300475364310315828657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677533650242873543885771 5516300475364310315828657)
            ·
              refine ⟨4137225356523232736871493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5516300475364310315828657 4137225356523232736871493)
              ·
                refine ⟨775729754348106138163405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4137225356523232736871493 775729754348106138163405)
                ·
                  refine ⟨290898657880539801811277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775729754348106138163405 290898657880539801811277)
                  ·
                    rfl

theorem cell21_1274677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_1274677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274677 prefixEnd_1274677 := by exact prefixLift 1274677
  have htrace : WordTrace (prefixWord ++ tailWord_1274677) baseStart_1274677 baseEnd_1274677 := by
    simpa [prefixWord, tailWord_1274677, baseEnd_1274677] using wordTrace_append hprefix tailTrace_1274677
  have hstable : (prefixWord ++ tailWord_1274677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274677).length < 2 ^ (prefixWord ++ tailWord_1274677).sum := by decide
  have hdescent : baseEnd_1274677 < baseStart_1274677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274691 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 4]
def baseStart_1274691 : Nat := 118140960795 + 1274691 * 2 ^ 59
def prefixEnd_1274691 : Nat := 4983230072969 + 3 ^ 40 * 1274691 * 2
def baseEnd_1274691 : Nat := 290901852871278888577915

theorem tailTrace_1274691 : CollatzResearch.WordTrace tailWord_1274691 prefixEnd_1274691 290901852871278888577915 := by
  unfold tailWord_1274691
  simp only [CollatzResearch.WordTrace]
  refine ⟨46491800225019681735935927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30994533483346454490623951 46491800225019681735935927)
  ·
    refine ⟨69737700337529522603903891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46491800225019681735935927 69737700337529522603903891)
    ·
      refine ⟨104606550506294283905855837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69737700337529522603903891 104606550506294283905855837)
      ·
        refine ⟨39227456439860356464695939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104606550506294283905855837 39227456439860356464695939)
        ·
          refine ⟨58841184659790534697043909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39227456439860356464695939 58841184659790534697043909)
          ·
            refine ⟨11032722123710725255695733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58841184659790534697043909 11032722123710725255695733)
            ·
              refine ⟨1034317699097880492721475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11032722123710725255695733 1034317699097880492721475)
              ·
                refine ⟨1551476548646820739082213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034317699097880492721475 1551476548646820739082213)
                ·
                  refine ⟨290901852871278888577915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551476548646820739082213 290901852871278888577915)
                  ·
                    rfl

theorem cell21_1274691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4].length) (baseStart_1274691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274691 prefixEnd_1274691 := by exact prefixLift 1274691
  have htrace : WordTrace (prefixWord ++ tailWord_1274691) baseStart_1274691 baseEnd_1274691 := by
    simpa [prefixWord, tailWord_1274691, baseEnd_1274691] using wordTrace_append hprefix tailTrace_1274691
  have hstable : (prefixWord ++ tailWord_1274691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274691).length < 2 ^ (prefixWord ++ tailWord_1274691).sum := by decide
  have hdescent : baseEnd_1274691 < baseStart_1274691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274705 : List Nat := [1, 2, 2, 1, 6, 1, 1, 7]
def baseStart_1274705 : Nat := 118140960795 + 1274705 * 2 ^ 59
def prefixEnd_1274705 : Nat := 4983230072969 + 3 ^ 40 * 1274705 * 2
def baseEnd_1274705 : Nat := 96968349287339325114851

theorem tailTrace_1274705 : CollatzResearch.WordTrace tailWord_1274705 prefixEnd_1274705 96968349287339325114851 := by
  unfold tailWord_1274705
  simp only [CollatzResearch.WordTrace]
  refine ⟨46492310846968962126945569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30994873897979308084630379 46492310846968962126945569)
  ·
    refine ⟨34869233135226721595209177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46492310846968962126945569 34869233135226721595209177)
    ·
      refine ⟨26151924851420041196406883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34869233135226721595209177 26151924851420041196406883)
      ·
        refine ⟨39227887277130061794610325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26151924851420041196406883 39227887277130061794610325)
        ·
          refine ⟨1838807216115471646622359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39227887277130061794610325 1838807216115471646622359)
          ·
            refine ⟨2758210824173207469933539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838807216115471646622359 2758210824173207469933539)
            ·
              refine ⟨4137316236259811204900309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758210824173207469933539 4137316236259811204900309)
              ·
                refine ⟨96968349287339325114851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4137316236259811204900309 96968349287339325114851)
                ·
                  rfl

theorem cell21_1274705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_1274705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274705 prefixEnd_1274705 := by exact prefixLift 1274705
  have htrace : WordTrace (prefixWord ++ tailWord_1274705) baseStart_1274705 baseEnd_1274705 := by
    simpa [prefixWord, tailWord_1274705, baseEnd_1274705] using wordTrace_append hprefix tailTrace_1274705
  have hstable : (prefixWord ++ tailWord_1274705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274705).length < 2 ^ (prefixWord ++ tailWord_1274705).sum := by decide
  have hdescent : baseEnd_1274705 < baseStart_1274705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274722 : List Nat := [3, 3, 2, 1, 3, 2, 7]
def baseStart_1274722 : Nat := 118140960795 + 1274722 * 2 ^ 59
def prefixEnd_1274722 : Nat := 4983230072969 + 3 ^ 40 * 1274722 * 2
def baseEnd_1274722 : Nat := 32323214165958858173465

theorem tailTrace_1274722 : CollatzResearch.WordTrace tailWord_1274722 prefixEnd_1274722 32323214165958858173465 := by
  unfold tailWord_1274722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623232721976843507578605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30995287258604916020209613 11623232721976843507578605)
  ·
    refine ⟨4358712270741316315341977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11623232721976843507578605 4358712270741316315341977)
    ·
      refine ⟨3269034203055987236506483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4358712270741316315341977 3269034203055987236506483)
      ·
        refine ⟨4903551304583980854759725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269034203055987236506483 4903551304583980854759725)
        ·
          refine ⟨1838831739218992820534897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4903551304583980854759725 1838831739218992820534897)
          ·
            refine ⟨1379123804414244615401173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838831739218992820534897 1379123804414244615401173)
            ·
              refine ⟨32323214165958858173465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1379123804414244615401173 32323214165958858173465)
              ·
                rfl

theorem cell21_1274722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 7].length) (baseStart_1274722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274722 prefixEnd_1274722 := by exact prefixLift 1274722
  have htrace : WordTrace (prefixWord ++ tailWord_1274722) baseStart_1274722 baseEnd_1274722 := by
    simpa [prefixWord, tailWord_1274722, baseEnd_1274722] using wordTrace_append hprefix tailTrace_1274722
  have hstable : (prefixWord ++ tailWord_1274722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274722).length < 2 ^ (prefixWord ++ tailWord_1274722).sum := by decide
  have hdescent : baseEnd_1274722 < baseStart_1274722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274736 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_1274736 : Nat := 118140960795 + 1274736 * 2 ^ 59
def prefixEnd_1274736 : Nat := 4983230072969 + 3 ^ 40 * 1274736 * 2
def baseEnd_1274736 : Nat := 290912122484368810327823

theorem tailTrace_1274736 : CollatzResearch.WordTrace tailWord_1274736 prefixEnd_1274736 290912122484368810327823 := by
  unfold tailWord_1274736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246720754928327210662031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30995627673237769614216041 23246720754928327210662031)
  ·
    refine ⟨34870081132392490815993047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23246720754928327210662031 34870081132392490815993047)
    ·
      refine ⟨52305121698588736223989571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34870081132392490815993047 52305121698588736223989571)
      ·
        refine ⟨78457682547883104335984357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52305121698588736223989571 78457682547883104335984357)
        ·
          refine ⟨14710815477728082062997067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78457682547883104335984357 14710815477728082062997067)
          ·
            refine ⟨22066223216592123094495601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14710815477728082062997067 22066223216592123094495601)
            ·
              refine ⟨16549667412444092320871701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22066223216592123094495601 16549667412444092320871701)
              ·
                refine ⟨775765659958316827540861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16549667412444092320871701 775765659958316827540861)
                ·
                  refine ⟨290912122484368810327823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775765659958316827540861 290912122484368810327823)
                  ·
                    rfl

theorem cell21_1274736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_1274736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274736 prefixEnd_1274736 := by exact prefixLift 1274736
  have htrace : WordTrace (prefixWord ++ tailWord_1274736) baseStart_1274736 baseEnd_1274736 := by
    simpa [prefixWord, tailWord_1274736, baseEnd_1274736] using wordTrace_append hprefix tailTrace_1274736
  have hstable : (prefixWord ++ tailWord_1274736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274736).length < 2 ^ (prefixWord ++ tailWord_1274736).sum := by decide
  have hdescent : baseEnd_1274736 < baseStart_1274736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274764 : List Nat := [2, 2, 1, 2, 1, 2, 4, 7]
def baseStart_1274764 : Nat := 118140960795 + 1274764 * 2 ^ 59
def prefixEnd_1274764 : Nat := 4983230072969 + 3 ^ 40 * 1274764 * 2
def baseEnd_1274764 : Nat := 96972837488615661287033

theorem tailTrace_1274764 : CollatzResearch.WordTrace tailWord_1274764 prefixEnd_1274764 96972837488615661287033 := by
  unfold tailWord_1274764
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247231376877607601671673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30996308502503476802228897 23247231376877607601671673)
  ·
    refine ⟨17435423532658205701253755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23247231376877607601671673 17435423532658205701253755)
    ·
      refine ⟨26153135298987308551880633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17435423532658205701253755 26153135298987308551880633)
      ·
        refine ⟨19614851474240481413910475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26153135298987308551880633 19614851474240481413910475)
        ·
          refine ⟨29422277211360722120865713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19614851474240481413910475 29422277211360722120865713)
          ·
            refine ⟨22066707908520541590649285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29422277211360722120865713 22066707908520541590649285)
            ·
              refine ⟨4137507732847601548246741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22066707908520541590649285 4137507732847601548246741)
              ·
                refine ⟨96972837488615661287033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4137507732847601548246741 96972837488615661287033)
                ·
                  rfl

theorem cell21_1274764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_1274764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274764 prefixEnd_1274764 := by exact prefixLift 1274764
  have htrace : WordTrace (prefixWord ++ tailWord_1274764) baseStart_1274764 baseEnd_1274764 := by
    simpa [prefixWord, tailWord_1274764, baseEnd_1274764] using wordTrace_append hprefix tailTrace_1274764
  have hstable : (prefixWord ++ tailWord_1274764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274764).length < 2 ^ (prefixWord ++ tailWord_1274764).sum := by decide
  have hdescent : baseEnd_1274764 < baseStart_1274764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274840 : List Nat := [2, 1, 2, 2, 2, 4, 8]
def baseStart_1274840 : Nat := 118140960795 + 1274840 * 2 ^ 59
def prefixEnd_1274840 : Nat := 4983230072969 + 3 ^ 40 * 1274840 * 2
def baseEnd_1274840 : Nat := 32326206300143082288253

theorem tailTrace_1274840 : CollatzResearch.WordTrace tailWord_1274840 prefixEnd_1274840 32326206300143082288253 := by
  unfold tailWord_1274840
  simp only [CollatzResearch.WordTrace]
  refine ⟨23248617350739940091554987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30998156467653253455406649 23248617350739940091554987)
  ·
    refine ⟨34872926026109910137332481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23248617350739940091554987 34872926026109910137332481)
    ·
      refine ⟨26154694519582432602999361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34872926026109910137332481 26154694519582432602999361)
      ·
        refine ⟨19616020889686824452249521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26154694519582432602999361 19616020889686824452249521)
        ·
          refine ⟨14712015667265118339187141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19616020889686824452249521 14712015667265118339187141)
          ·
            refine ⟨2758502937612209688597589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14712015667265118339187141 2758502937612209688597589)
            ·
              refine ⟨32326206300143082288253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2758502937612209688597589 32326206300143082288253)
              ·
                rfl

theorem cell21_1274840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 8].length) (baseStart_1274840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274840 prefixEnd_1274840 := by exact prefixLift 1274840
  have htrace : WordTrace (prefixWord ++ tailWord_1274840) baseStart_1274840 baseEnd_1274840 := by
    simpa [prefixWord, tailWord_1274840, baseEnd_1274840] using wordTrace_append hprefix tailTrace_1274840
  have hstable : (prefixWord ++ tailWord_1274840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274840).length < 2 ^ (prefixWord ++ tailWord_1274840).sum := by decide
  have hdescent : baseEnd_1274840 < baseStart_1274840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274885 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_1274885 : Nat := 118140960795 + 1274885 * 2 ^ 59
def prefixEnd_1274885 : Nat := 4983230072969 + 3 ^ 40 * 1274885 * 2
def baseEnd_1274885 : Nat := 290946126314377662344185

theorem tailTrace_1274885 : CollatzResearch.WordTrace tailWord_1274885 prefixEnd_1274885 290946126314377662344185 := by
  unfold tailWord_1274885
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498875986316852868498109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30999250657544568578998739 46498875986316852868498109)
  ·
    refine ⟨17437078494868819825686791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46498875986316852868498109 17437078494868819825686791)
    ·
      refine ⟨26155617742303229738530187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17437078494868819825686791 26155617742303229738530187)
      ·
        refine ⟨39233426613454844607795281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26155617742303229738530187 39233426613454844607795281)
        ·
          refine ⟨29425069960091133455846461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39233426613454844607795281 29425069960091133455846461)
          ·
            refine ⟨11034401235034175045942423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29425069960091133455846461 11034401235034175045942423)
            ·
              refine ⟨16551601852551262568913635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11034401235034175045942423 16551601852551262568913635)
              ·
                refine ⟨24827402778826893853370453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16551601852551262568913635 24827402778826893853370453)
                ·
                  refine ⟨290946126314377662344185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24827402778826893853370453 290946126314377662344185)
                  ·
                    rfl

theorem cell21_1274885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_1274885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274885 prefixEnd_1274885 := by exact prefixLift 1274885
  have htrace : WordTrace (prefixWord ++ tailWord_1274885) baseStart_1274885 baseEnd_1274885 := by
    simpa [prefixWord, tailWord_1274885, baseEnd_1274885] using wordTrace_append hprefix tailTrace_1274885
  have hstable : (prefixWord ++ tailWord_1274885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274885).length < 2 ^ (prefixWord ++ tailWord_1274885).sum := by decide
  have hdescent : baseEnd_1274885 < baseStart_1274885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274961 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1274961 : Nat := 118140960795 + 1274961 * 2 ^ 59
def prefixEnd_1274961 : Nat := 4983230072969 + 3 ^ 40 * 1274961 * 2
def baseEnd_1274961 : Nat := 290963470549818419077363

theorem tailTrace_1274961 : CollatzResearch.WordTrace tailWord_1274961 prefixEnd_1274961 290963470549818419077363 := by
  unfold tailWord_1274961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46501647934041517848264737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31001098622694345232176491 46501647934041517848264737)
  ·
    refine ⟨34876235950531138386198553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46501647934041517848264737 34876235950531138386198553)
    ·
      refine ⟨26157176962898353789648915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34876235950531138386198553 26157176962898353789648915)
      ·
        refine ⟨39235765444347530684473373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26157176962898353789648915 39235765444347530684473373)
        ·
          refine ⟨14713412041630324006677515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39235765444347530684473373 14713412041630324006677515)
          ·
            refine ⟨22070118062445486010016273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14713412041630324006677515 22070118062445486010016273)
            ·
              refine ⟨16552588546834114507512205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22070118062445486010016273 16552588546834114507512205)
              ·
                refine ⟨6207220705062792940317077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16552588546834114507512205 6207220705062792940317077)
                ·
                  refine ⟨290963470549818419077363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6207220705062792940317077 290963470549818419077363)
                  ·
                    rfl

theorem cell21_1274961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1274961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1274961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1274961 prefixEnd_1274961 := by exact prefixLift 1274961
  have htrace : WordTrace (prefixWord ++ tailWord_1274961) baseStart_1274961 baseEnd_1274961 := by
    simpa [prefixWord, tailWord_1274961, baseEnd_1274961] using wordTrace_append hprefix tailTrace_1274961
  have hstable : (prefixWord ++ tailWord_1274961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274961).length < 2 ^ (prefixWord ++ tailWord_1274961).sum := by decide
  have hdescent : baseEnd_1274961 < baseStart_1274961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275057 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 3]
def baseStart_1275057 : Nat := 118140960795 + 1275057 * 2 ^ 59
def prefixEnd_1275057 : Nat := 4983230072969 + 3 ^ 40 * 1275057 * 2
def baseEnd_1275057 : Nat := 290985379057743585477167

theorem tailTrace_1275057 : CollatzResearch.WordTrace tailWord_1275057 prefixEnd_1275057 290985379057743585477167 := by
  unfold tailWord_1275057
  simp only [CollatzResearch.WordTrace]
  refine ⟨46505149341693726243759425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31003432894462484162506283 46505149341693726243759425)
  ·
    refine ⟨34878862006270294682819569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46505149341693726243759425 34878862006270294682819569)
    ·
      refine ⟨26159146504702721012114677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34878862006270294682819569 26159146504702721012114677)
      ·
        refine ⟨2452419984815880094885751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26159146504702721012114677 2452419984815880094885751)
        ·
          refine ⟨3678629977223820142328627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452419984815880094885751 3678629977223820142328627)
          ·
            refine ⟨5517944965835730213492941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678629977223820142328627 5517944965835730213492941)
            ·
              refine ⟨2069229362188398830059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5517944965835730213492941 2069229362188398830059853)
              ·
                refine ⟨775961010820649561272445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2069229362188398830059853 775961010820649561272445)
                ·
                  refine ⟨290985379057743585477167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775961010820649561272445 290985379057743585477167)
                  ·
                    rfl

theorem cell21_1275057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_1275057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275057 prefixEnd_1275057 := by exact prefixLift 1275057
  have htrace : WordTrace (prefixWord ++ tailWord_1275057) baseStart_1275057 baseEnd_1275057 := by
    simpa [prefixWord, tailWord_1275057, baseEnd_1275057] using wordTrace_append hprefix tailTrace_1275057
  have hstable : (prefixWord ++ tailWord_1275057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275057).length < 2 ^ (prefixWord ++ tailWord_1275057).sum := by decide
  have hdescent : baseEnd_1275057 < baseStart_1275057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275068 : List Nat := [2, 2, 2, 3, 2, 1, 9]
def baseStart_1275068 : Nat := 118140960795 + 1275068 * 2 ^ 59
def prefixEnd_1275068 : Nat := 4983230072969 + 3 ^ 40 * 1275068 * 2
def baseEnd_1275068 : Nat := 32331987711956667865979

theorem tailTrace_1275068 : CollatzResearch.WordTrace tailWord_1275068 prefixEnd_1275068 32331987711956667865979 := by
  unfold tailWord_1275068
  simp only [CollatzResearch.WordTrace]
  refine ⟨23252775272326937561204929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31003700363102583414939905 23252775272326937561204929)
  ·
    refine ⟨17439581454245203170903697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23252775272326937561204929 17439581454245203170903697)
    ·
      refine ⟨13079686090683902378177773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17439581454245203170903697 13079686090683902378177773)
      ·
        refine ⟨4904882284006463391816665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13079686090683902378177773 4904882284006463391816665)
        ·
          refine ⟨3678661713004847543862499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904882284006463391816665 3678661713004847543862499)
          ·
            refine ⟨5517992569507271315793749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678661713004847543862499 5517992569507271315793749)
            ·
              refine ⟨32331987711956667865979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5517992569507271315793749 32331987711956667865979)
              ·
                rfl

theorem cell21_1275068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 9].length) (baseStart_1275068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275068 prefixEnd_1275068 := by exact prefixLift 1275068
  have htrace : WordTrace (prefixWord ++ tailWord_1275068) baseStart_1275068 baseEnd_1275068 := by
    simpa [prefixWord, tailWord_1275068, baseEnd_1275068] using wordTrace_append hprefix tailTrace_1275068
  have hstable : (prefixWord ++ tailWord_1275068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275068).length < 2 ^ (prefixWord ++ tailWord_1275068).sum := by decide
  have hdescent : baseEnd_1275068 < baseStart_1275068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275130 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1275130 : Nat := 118140960795 + 1275130 * 2 ^ 59
def prefixEnd_1275130 : Nat := 4983230072969 + 3 ^ 40 * 1275130 * 2
def baseEnd_1275130 : Nat := 291002038652311680760351

theorem tailTrace_1275130 : CollatzResearch.WordTrace tailWord_1275130 prefixEnd_1275130 291002038652311680760351 := by
  unfold tailWord_1275130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11626952967607314927791711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31005207913619506474111229 11626952967607314927791711)
  ·
    refine ⟨17440429451410972391687567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11626952967607314927791711 17440429451410972391687567)
    ·
      refine ⟨26160644177116458587531351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17440429451410972391687567 26160644177116458587531351)
      ·
        refine ⟨39240966265674687881297027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26160644177116458587531351 39240966265674687881297027)
        ·
          refine ⟨58861449398512031821945541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39240966265674687881297027 58861449398512031821945541)
          ·
            refine ⟨11036521762221005966614789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58861449398512031821945541 11036521762221005966614789)
            ·
              refine ⟨2069347830416438618740273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11036521762221005966614789 2069347830416438618740273)
              ·
                refine ⟨1552010872812328964055205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069347830416438618740273 1552010872812328964055205)
                ·
                  refine ⟨291002038652311680760351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552010872812328964055205 291002038652311680760351)
                  ·
                    rfl

theorem cell21_1275130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1275130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275130 prefixEnd_1275130 := by exact prefixLift 1275130
  have htrace : WordTrace (prefixWord ++ tailWord_1275130) baseStart_1275130 baseEnd_1275130 := by
    simpa [prefixWord, tailWord_1275130, baseEnd_1275130] using wordTrace_append hprefix tailTrace_1275130
  have hstable : (prefixWord ++ tailWord_1275130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275130).length < 2 ^ (prefixWord ++ tailWord_1275130).sum := by decide
  have hdescent : baseEnd_1275130 < baseStart_1275130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275203 : List Nat := [1, 1, 1, 3, 1, 3, 1, 10]
def baseStart_1275203 : Nat := 118140960795 + 1275203 * 2 ^ 59
def prefixEnd_1275203 : Nat := 4983230072969 + 3 ^ 40 * 1275203 * 2
def baseEnd_1275203 : Nat := 97006232748959925347845

theorem tailTrace_1275203 : CollatzResearch.WordTrace tailWord_1275203 prefixEnd_1275203 97006232748959925347845 := by
  unfold tailWord_1275203
  simp only [CollatzResearch.WordTrace]
  refine ⟨46510474399164793178574263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31006982932776528785716175 46510474399164793178574263)
  ·
    refine ⟨69765711598747189767861395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46510474399164793178574263 69765711598747189767861395)
    ·
      refine ⟨104648567398120784651792093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69765711598747189767861395 104648567398120784651792093)
      ·
        refine ⟨39243212774295294244422035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104648567398120784651792093 39243212774295294244422035)
        ·
          refine ⟨58864819161442941366633053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39243212774295294244422035 58864819161442941366633053)
          ·
            refine ⟨22074307185541103012487395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58864819161442941366633053 22074307185541103012487395)
            ·
              refine ⟨33111460778311654518731093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22074307185541103012487395 33111460778311654518731093)
              ·
                refine ⟨97006232748959925347845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33111460778311654518731093 97006232748959925347845)
                ·
                  rfl

theorem cell21_1275203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_1275203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275203 prefixEnd_1275203 := by exact prefixLift 1275203
  have htrace : WordTrace (prefixWord ++ tailWord_1275203) baseStart_1275203 baseEnd_1275203 := by
    simpa [prefixWord, tailWord_1275203, baseEnd_1275203] using wordTrace_append hprefix tailTrace_1275203
  have hstable : (prefixWord ++ tailWord_1275203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275203).length < 2 ^ (prefixWord ++ tailWord_1275203).sum := by decide
  have hdescent : baseEnd_1275203 < baseStart_1275203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275220 : List Nat := [2, 4, 1, 1, 2, 1, 3, 7]
def baseStart_1275220 : Nat := 118140960795 + 1275220 * 2 ^ 59
def prefixEnd_1275220 : Nat := 4983230072969 + 3 ^ 40 * 1275220 * 2
def baseEnd_1275220 : Nat := 97007525959497174753389

theorem tailTrace_1275220 : CollatzResearch.WordTrace tailWord_1275220 prefixEnd_1275220 97007525959497174753389 := by
  unfold tailWord_1275220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255547220051602540971557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31007396293402136721295409 23255547220051602540971557)
  ·
    refine ⟨4360415103759675476432167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23255547220051602540971557 4360415103759675476432167)
    ·
      refine ⟨6540622655639513214648251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4360415103759675476432167 6540622655639513214648251)
      ·
        refine ⟨9810933983459269821972377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540622655639513214648251 9810933983459269821972377)
        ·
          refine ⟨7358200487594452366479283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9810933983459269821972377 7358200487594452366479283)
          ·
            refine ⟨11037300731391678549718925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358200487594452366479283 11037300731391678549718925)
            ·
              refine ⟨4138987774271879456144597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11037300731391678549718925 4138987774271879456144597)
              ·
                refine ⟨97007525959497174753389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4138987774271879456144597 97007525959497174753389)
                ·
                  rfl

theorem cell21_1275220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_1275220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275220 prefixEnd_1275220 := by exact prefixLift 1275220
  have htrace : WordTrace (prefixWord ++ tailWord_1275220) baseStart_1275220 baseEnd_1275220 := by
    simpa [prefixWord, tailWord_1275220, baseEnd_1275220] using wordTrace_append hprefix tailTrace_1275220
  have hstable : (prefixWord ++ tailWord_1275220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275220).length < 2 ^ (prefixWord ++ tailWord_1275220).sum := by decide
  have hdescent : baseEnd_1275220 < baseStart_1275220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275386 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1275386 : Nat := 118140960795 + 1275386 * 2 ^ 59
def prefixEnd_1275386 : Nat := 4983230072969 + 3 ^ 40 * 1275386 * 2
def baseEnd_1275386 : Nat := 291060461340112124493161

theorem tailTrace_1275386 : CollatzResearch.WordTrace tailWord_1275386 prefixEnd_1275386 291060461340112124493161 := by
  unfold tailWord_1275386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11629287239375453858121503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31011432638334543621657341 11629287239375453858121503)
  ·
    refine ⟨17443930859063180787182255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11629287239375453858121503 17443930859063180787182255)
    ·
      refine ⟨26165896288594771180773383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17443930859063180787182255 26165896288594771180773383)
      ·
        refine ⟨39248844432892156771160075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26165896288594771180773383 39248844432892156771160075)
        ·
          refine ⟨58873266649338235156740113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39248844432892156771160075 58873266649338235156740113)
          ·
            refine ⟨44154949987003676367555085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58873266649338235156740113 44154949987003676367555085)
            ·
              refine ⟨16558106245126378637833157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44154949987003676367555085 16558106245126378637833157)
              ·
                refine ⟨3104644920961195994593717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16558106245126378637833157 3104644920961195994593717)
                ·
                  refine ⟨291060461340112124493161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104644920961195994593717 291060461340112124493161)
                  ·
                    rfl

theorem cell21_1275386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1275386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275386 prefixEnd_1275386 := by exact prefixLift 1275386
  have htrace : WordTrace (prefixWord ++ tailWord_1275386) baseStart_1275386 baseEnd_1275386 := by
    simpa [prefixWord, tailWord_1275386, baseEnd_1275386] using wordTrace_append hprefix tailTrace_1275386
  have hstable : (prefixWord ++ tailWord_1275386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275386).length < 2 ^ (prefixWord ++ tailWord_1275386).sum := by decide
  have hdescent : baseEnd_1275386 < baseStart_1275386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275389 : List Nat := [1, 4, 1, 1, 1, 6, 2, 5]
def baseStart_1275389 : Nat := 118140960795 + 1275389 * 2 ^ 59
def prefixEnd_1275389 : Nat := 4983230072969 + 3 ^ 40 * 1275389 * 2
def baseEnd_1275389 : Nat := 97020381993661595314385

theorem tailTrace_1275389 : CollatzResearch.WordTrace tailWord_1275389 prefixEnd_1275389 97020381993661595314385 := by
  unfold tailWord_1275389
  simp only [CollatzResearch.WordTrace]
  refine ⟨46517258376490946944845221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31011505584327297963230147 46517258376490946944845221)
  ·
    refine ⟨8721985945592052552158479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46517258376490946944845221 8721985945592052552158479)
    ·
      refine ⟨13082978918388078828237719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8721985945592052552158479 13082978918388078828237719)
      ·
        refine ⟨19624468377582118242356579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13082978918388078828237719 19624468377582118242356579)
        ·
          refine ⟨29436702566373177363534869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19624468377582118242356579 29436702566373177363534869)
          ·
            refine ⟨1379845432798742688915697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29436702566373177363534869 1379845432798742688915697)
            ·
              refine ⟨1034884074599057016686773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379845432798742688915697 1034884074599057016686773)
              ·
                refine ⟨97020381993661595314385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1034884074599057016686773 97020381993661595314385)
                ·
                  rfl

theorem cell21_1275389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 5].length) (baseStart_1275389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275389 prefixEnd_1275389 := by exact prefixLift 1275389
  have htrace : WordTrace (prefixWord ++ tailWord_1275389) baseStart_1275389 baseEnd_1275389 := by
    simpa [prefixWord, tailWord_1275389, baseEnd_1275389] using wordTrace_append hprefix tailTrace_1275389
  have hstable : (prefixWord ++ tailWord_1275389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275389).length < 2 ^ (prefixWord ++ tailWord_1275389).sum := by decide
  have hdescent : baseEnd_1275389 < baseStart_1275389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275434 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_1275434 : Nat := 118140960795 + 1275434 * 2 ^ 59
def prefixEnd_1275434 : Nat := 4983230072969 + 3 ^ 40 * 1275434 * 2
def baseEnd_1275434 : Nat := 291071415594074707693063

theorem tailTrace_1275434 : CollatzResearch.WordTrace tailWord_1275434 prefixEnd_1275434 291071415594074707693063 := by
  unfold tailWord_1275434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11629724915331979907558339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31012599774218613086822237 11629724915331979907558339)
  ·
    refine ⟨17444587372997969861337509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11629724915331979907558339 17444587372997969861337509)
    ·
      refine ⟨3270860132437119349000783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17444587372997969861337509 3270860132437119349000783)
      ·
        refine ⟨4906290198655679023501175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270860132437119349000783 4906290198655679023501175)
        ·
          refine ⟨7359435297983518535251763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906290198655679023501175 7359435297983518535251763)
          ·
            refine ⟨11039152946975277802877645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7359435297983518535251763 11039152946975277802877645)
            ·
              refine ⟨4139682355115729176079117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11039152946975277802877645 4139682355115729176079117)
              ·
                refine ⟨1552380883168398441029669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4139682355115729176079117 1552380883168398441029669)
                ·
                  refine ⟨291071415594074707693063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552380883168398441029669 291071415594074707693063)
                  ·
                    rfl

theorem cell21_1275434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_1275434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275434 prefixEnd_1275434 := by exact prefixLift 1275434
  have htrace : WordTrace (prefixWord ++ tailWord_1275434) baseStart_1275434 baseEnd_1275434 := by
    simpa [prefixWord, tailWord_1275434, baseEnd_1275434] using wordTrace_append hprefix tailTrace_1275434
  have hstable : (prefixWord ++ tailWord_1275434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275434).length < 2 ^ (prefixWord ++ tailWord_1275434).sum := by decide
  have hdescent : baseEnd_1275434 < baseStart_1275434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275524 : List Nat := [2, 3, 2, 1, 4, 1, 8]
def baseStart_1275524 : Nat := 118140960795 + 1275524 * 2 ^ 59
def prefixEnd_1275524 : Nat := 4983230072969 + 3 ^ 40 * 1275524 * 2
def baseEnd_1275524 : Nat := 32343550535583839021431

theorem tailTrace_1275524 : CollatzResearch.WordTrace tailWord_1275524 prefixEnd_1275524 32343550535583839021431 := by
  unfold tailWord_1275524
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261091115500932500504813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31014788154001243334006417 23261091115500932500504813)
  ·
    refine ⟨8722909168312849687689305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23261091115500932500504813 8722909168312849687689305)
    ·
      refine ⟨6542181876234637265766979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8722909168312849687689305 6542181876234637265766979)
      ·
        refine ⟨9813272814351955898650469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6542181876234637265766979 9813272814351955898650469)
        ·
          refine ⟨1839988652690991730996963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9813272814351955898650469 1839988652690991730996963)
          ·
            refine ⟨2759982979036487596495445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839988652690991730996963 2759982979036487596495445)
            ·
              refine ⟨32343550535583839021431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2759982979036487596495445 32343550535583839021431)
              ·
                rfl

theorem cell21_1275524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 8].length) (baseStart_1275524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275524 prefixEnd_1275524 := by exact prefixLift 1275524
  have htrace : WordTrace (prefixWord ++ tailWord_1275524) baseStart_1275524 baseEnd_1275524 := by
    simpa [prefixWord, tailWord_1275524, baseEnd_1275524] using wordTrace_append hprefix tailTrace_1275524
  have hstable : (prefixWord ++ tailWord_1275524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275524).length < 2 ^ (prefixWord ++ tailWord_1275524).sum := by decide
  have hdescent : baseEnd_1275524 < baseStart_1275524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275628 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1275628 : Nat := 118140960795 + 1275628 * 2 ^ 59
def prefixEnd_1275628 : Nat := 4983230072969 + 3 ^ 40 * 1275628 * 2
def baseEnd_1275628 : Nat := 291115689037173481459333

theorem tailTrace_1275628 : CollatzResearch.WordTrace tailWord_1275628 prefixEnd_1275628 291115689037173481459333 := by
  unfold tailWord_1275628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23262987711312545381397769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31017316948416727175197025 23262987711312545381397769)
  ·
    refine ⟨17447240783484409036048327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23262987711312545381397769 17447240783484409036048327)
    ·
      refine ⟨26170861175226613554072491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17447240783484409036048327 26170861175226613554072491)
      ·
        refine ⟨39256291762839920331108737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26170861175226613554072491 39256291762839920331108737)
        ·
          refine ⟨29442218822129940248331553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39256291762839920331108737 29442218822129940248331553)
          ·
            refine ⟨22081664116597455186248665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29442218822129940248331553 22081664116597455186248665)
            ·
              refine ⟨16561248087448091389686499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22081664116597455186248665 16561248087448091389686499)
              ·
                refine ⟨24841872131172137084529749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16561248087448091389686499 24841872131172137084529749)
                ·
                  refine ⟨291115689037173481459333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24841872131172137084529749 291115689037173481459333)
                  ·
                    rfl

theorem cell21_1275628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1275628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275628 prefixEnd_1275628 := by exact prefixLift 1275628
  have htrace : WordTrace (prefixWord ++ tailWord_1275628) baseStart_1275628 baseEnd_1275628 := by
    simpa [prefixWord, tailWord_1275628, baseEnd_1275628] using wordTrace_append hprefix tailTrace_1275628
  have hstable : (prefixWord ++ tailWord_1275628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275628).length < 2 ^ (prefixWord ++ tailWord_1275628).sum := by decide
  have hdescent : baseEnd_1275628 < baseStart_1275628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275631 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 3]
def baseStart_1275631 : Nat := 118140960795 + 1275631 * 2 ^ 59
def prefixEnd_1275631 : Nat := 4983230072969 + 3 ^ 40 * 1275631 * 2
def baseEnd_1275631 : Nat := 291116373678046142909327

theorem tailTrace_1275631 : CollatzResearch.WordTrace tailWord_1275631 prefixEnd_1275631 291116373678046142909327 := by
  unfold tailWord_1275631
  simp only [CollatzResearch.WordTrace]
  refine ⟨46526084841614222275154747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31017389894409481516769831 46526084841614222275154747)
  ·
    refine ⟨69789127262421333412732121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46526084841614222275154747 69789127262421333412732121)
    ·
      refine ⟨52341845446816000059549091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69789127262421333412732121 52341845446816000059549091)
      ·
        refine ⟨78512768170224000089323637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52341845446816000059549091 78512768170224000089323637)
        ·
          refine ⟨7360572015958500008374091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78512768170224000089323637 7360572015958500008374091)
          ·
            refine ⟨11040858023937750012561137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360572015958500008374091 11040858023937750012561137)
            ·
              refine ⟨8280643517953312509420853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11040858023937750012561137 8280643517953312509420853)
              ·
                refine ⟨776310329808123047758205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8280643517953312509420853 776310329808123047758205)
                ·
                  refine ⟨291116373678046142909327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776310329808123047758205 291116373678046142909327)
                  ·
                    rfl

theorem cell21_1275631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3].length) (baseStart_1275631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275631 prefixEnd_1275631 := by exact prefixLift 1275631
  have htrace : WordTrace (prefixWord ++ tailWord_1275631) baseStart_1275631 baseEnd_1275631 := by
    simpa [prefixWord, tailWord_1275631, baseEnd_1275631] using wordTrace_append hprefix tailTrace_1275631
  have hstable : (prefixWord ++ tailWord_1275631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275631).length < 2 ^ (prefixWord ++ tailWord_1275631).sum := by decide
  have hdescent : baseEnd_1275631 < baseStart_1275631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275659 : List Nat := [1, 1, 1, 1, 5, 1, 5, 6]
def baseStart_1275659 : Nat := 118140960795 + 1275659 * 2 ^ 59
def prefixEnd_1275659 : Nat := 4983230072969 + 3 ^ 40 * 1275659 * 2
def baseEnd_1275659 : Nat := 97040921219841438814201

theorem tailTrace_1275659 : CollatzResearch.WordTrace tailWord_1275659 prefixEnd_1275659 97040921219841438814201 := by
  unfold tailWord_1275659
  simp only [CollatzResearch.WordTrace]
  refine ⟨46527106085512783057174031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31018070723675188704782687 46527106085512783057174031)
  ·
    refine ⟨69790659128269174585761047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46527106085512783057174031 69790659128269174585761047)
    ·
      refine ⟨104685988692403761878641571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69790659128269174585761047 104685988692403761878641571)
      ·
        refine ⟨157028983038605642817962357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104685988692403761878641571 157028983038605642817962357)
        ·
          refine ⟨14721467159869279014183971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157028983038605642817962357 14721467159869279014183971)
          ·
            refine ⟨22082200739803918521275957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14721467159869279014183971 22082200739803918521275957)
            ·
              refine ⟨2070206319356617361369621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22082200739803918521275957 2070206319356617361369621)
              ·
                refine ⟨97040921219841438814201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070206319356617361369621 97040921219841438814201)
                ·
                  rfl

theorem cell21_1275659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_1275659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275659 prefixEnd_1275659 := by exact prefixLift 1275659
  have htrace : WordTrace (prefixWord ++ tailWord_1275659) baseStart_1275659 baseEnd_1275659 := by
    simpa [prefixWord, tailWord_1275659, baseEnd_1275659] using wordTrace_append hprefix tailTrace_1275659
  have hstable : (prefixWord ++ tailWord_1275659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275659).length < 2 ^ (prefixWord ++ tailWord_1275659).sum := by decide
  have hdescent : baseEnd_1275659 < baseStart_1275659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275676 : List Nat := [2, 2, 3, 1, 1, 2, 5, 5]
def baseStart_1275676 : Nat := 118140960795 + 1275676 * 2 ^ 59
def prefixEnd_1275676 : Nat := 4983230072969 + 3 ^ 40 * 1275676 * 2
def baseEnd_1275676 : Nat := 97042214430378688219745

theorem tailTrace_1275676 : CollatzResearch.WordTrace tailWord_1275676 prefixEnd_1275676 97042214430378688219745 := by
  unfold tailWord_1275676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23263863063225597480271441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31018484084300796640361921 23263863063225597480271441)
  ·
    refine ⟨17447897297419198110203581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23263863063225597480271441 17447897297419198110203581)
    ·
      refine ⟨6542961486532199291326343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17447897297419198110203581 6542961486532199291326343)
      ·
        refine ⟨9814442229798298936989515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6542961486532199291326343 9814442229798298936989515)
        ·
          refine ⟨14721663344697448405484273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814442229798298936989515 14721663344697448405484273)
          ·
            refine ⟨11041247508523086304113205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14721663344697448405484273 11041247508523086304113205)
            ·
              refine ⟨1035116953924039341010613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11041247508523086304113205 1035116953924039341010613)
              ·
                refine ⟨97042214430378688219745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1035116953924039341010613 97042214430378688219745)
                ·
                  rfl

theorem cell21_1275676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_1275676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275676 prefixEnd_1275676 := by exact prefixLift 1275676
  have htrace : WordTrace (prefixWord ++ tailWord_1275676) baseStart_1275676 baseEnd_1275676 := by
    simpa [prefixWord, tailWord_1275676, baseEnd_1275676] using wordTrace_append hprefix tailTrace_1275676
  have hstable : (prefixWord ++ tailWord_1275676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275676).length < 2 ^ (prefixWord ++ tailWord_1275676).sum := by decide
  have hdescent : baseEnd_1275676 < baseStart_1275676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275873 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_1275873 : Nat := 118140960795 + 1275873 * 2 ^ 59
def prefixEnd_1275873 : Nat := 4983230072969 + 3 ^ 40 * 1275873 * 2
def baseEnd_1275873 : Nat := 291171601375107499875499

theorem tailTrace_1275873 : CollatzResearch.WordTrace tailWord_1275873 prefixEnd_1275873 291171601375107499875499 := by
  unfold tailWord_1275873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46534911306737497605464273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31023274204491665070309515 46534911306737497605464273)
  ·
    refine ⟨34901183480053123204098205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46534911306737497605464273 34901183480053123204098205)
    ·
      refine ⟨13087943805019921201536827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34901183480053123204098205 13087943805019921201536827)
      ·
        refine ⟨19631915707529881802305241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13087943805019921201536827 19631915707529881802305241)
        ·
          refine ⟨14723936780647411351728931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19631915707529881802305241 14723936780647411351728931)
          ·
            refine ⟨22085905170971117027593397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14723936780647411351728931 22085905170971117027593397)
            ·
              refine ⟨2070553609778542221336881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22085905170971117027593397 2070553609778542221336881)
              ·
                refine ⟨1552915207333906666002661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070553609778542221336881 1552915207333906666002661)
                ·
                  refine ⟨291171601375107499875499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552915207333906666002661 291171601375107499875499)
                  ·
                    rfl

theorem cell21_1275873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_1275873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275873 prefixEnd_1275873 := by exact prefixLift 1275873
  have htrace : WordTrace (prefixWord ++ tailWord_1275873) baseStart_1275873 baseEnd_1275873 := by
    simpa [prefixWord, tailWord_1275873, baseEnd_1275873] using wordTrace_append hprefix tailTrace_1275873
  have hstable : (prefixWord ++ tailWord_1275873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275873).length < 2 ^ (prefixWord ++ tailWord_1275873).sum := by decide
  have hdescent : baseEnd_1275873 < baseStart_1275873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275986 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_1275986 : Nat := 118140960795 + 1275986 * 2 ^ 59
def prefixEnd_1275986 : Nat := 4983230072969 + 3 ^ 40 * 1275986 * 2
def baseEnd_1275986 : Nat := 291197389514644414491935

theorem tailTrace_1275986 : CollatzResearch.WordTrace tailWord_1275986 prefixEnd_1275986 291197389514644414491935 := by
  unfold tailWord_1275986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634758188832029476081953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31026021836885411936218541 11634758188832029476081953)
  ·
    refine ⟨8726068641624022107061465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11634758188832029476081953 8726068641624022107061465)
    ·
      refine ⟨6544551481218016580296099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8726068641624022107061465 6544551481218016580296099)
      ·
        refine ⟨9816827221827024870444149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544551481218016580296099 9816827221827024870444149)
        ·
          refine ⟨920327552046283581604139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9816827221827024870444149 920327552046283581604139)
          ·
            refine ⟨1380491328069425372406209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920327552046283581604139 1380491328069425372406209)
            ·
              refine ⟨1035368496052069029304657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1380491328069425372406209 1035368496052069029304657)
              ·
                refine ⟨776526372039051771978493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035368496052069029304657 776526372039051771978493)
                ·
                  refine ⟨291197389514644414491935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776526372039051771978493 291197389514644414491935)
                  ·
                    rfl

theorem cell21_1275986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_1275986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275986 prefixEnd_1275986 := by exact prefixLift 1275986
  have htrace : WordTrace (prefixWord ++ tailWord_1275986) baseStart_1275986 baseEnd_1275986 := by
    simpa [prefixWord, tailWord_1275986, baseEnd_1275986] using wordTrace_append hprefix tailTrace_1275986
  have hstable : (prefixWord ++ tailWord_1275986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275986).length < 2 ^ (prefixWord ++ tailWord_1275986).sum := by decide
  have hdescent : baseEnd_1275986 < baseStart_1275986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275997 : List Nat := [1, 4, 4, 1, 1, 3, 1, 6]
def baseStart_1275997 : Nat := 118140960795 + 1275997 * 2 ^ 59
def prefixEnd_1275997 : Nat := 4983230072969 + 3 ^ 40 * 1275997 * 2
def baseEnd_1275997 : Nat := 97066633288170279936193

theorem tailTrace_1275997 : CollatzResearch.WordTrace tailWord_1275997 prefixEnd_1275997 97066633288170279936193 := by
  unfold tailWord_1275997
  simp only [CollatzResearch.WordTrace]
  refine ⟨46539433958288266782978245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31026289305525511188652163 46539433958288266782978245)
  ·
    refine ⟨8726143867179050021808421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46539433958288266782978245 8726143867179050021808421)
    ·
      refine ⟨1636151975096071879089079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8726143867179050021808421 1636151975096071879089079)
      ·
        refine ⟨2454227962644107818633619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636151975096071879089079 2454227962644107818633619)
        ·
          refine ⟨3681341943966161727950429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454227962644107818633619 3681341943966161727950429)
          ·
            refine ⟨1380503228987310647981411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3681341943966161727950429 1380503228987310647981411)
            ·
              refine ⟨2070754843480965971972117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380503228987310647981411 2070754843480965971972117)
              ·
                refine ⟨97066633288170279936193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070754843480965971972117 97066633288170279936193)
                ·
                  rfl

theorem cell21_1275997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 6].length) (baseStart_1275997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1275997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1275997 prefixEnd_1275997 := by exact prefixLift 1275997
  have htrace : WordTrace (prefixWord ++ tailWord_1275997) baseStart_1275997 baseEnd_1275997 := by
    simpa [prefixWord, tailWord_1275997, baseEnd_1275997] using wordTrace_append hprefix tailTrace_1275997
  have hstable : (prefixWord ++ tailWord_1275997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275997).length < 2 ^ (prefixWord ++ tailWord_1275997).sum := by decide
  have hdescent : baseEnd_1275997 < baseStart_1275997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276042 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1276042 : Nat := 118140960795 + 1276042 * 2 ^ 59
def prefixEnd_1276042 : Nat := 4983230072969 + 3 ^ 40 * 1276042 * 2
def baseEnd_1276042 : Nat := 291210169477600761558487

theorem tailTrace_1276042 : CollatzResearch.WordTrace tailWord_1276042 prefixEnd_1276042 291210169477600761558487 := by
  unfold tailWord_1276042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635268810781309867091595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31027383495416826312244253 11635268810781309867091595)
  ·
    refine ⟨17452903216171964800637393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11635268810781309867091595 17452903216171964800637393)
    ·
      refine ⟨13089677412128973600478045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17452903216171964800637393 13089677412128973600478045)
      ·
        refine ⟨4908629029548365100179267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13089677412128973600478045 4908629029548365100179267)
        ·
          refine ⟨7362943544322547650268901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908629029548365100179267 7362943544322547650268901)
          ·
            refine ⟨1380551914560477684425419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7362943544322547650268901 1380551914560477684425419)
            ·
              refine ⟨2070827871840716526638129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380551914560477684425419 2070827871840716526638129)
              ·
                refine ⟨1553120903880537394978597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070827871840716526638129 1553120903880537394978597)
                ·
                  refine ⟨291210169477600761558487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553120903880537394978597 291210169477600761558487)
                  ·
                    rfl

theorem cell21_1276042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1276042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276042 prefixEnd_1276042 := by exact prefixLift 1276042
  have htrace : WordTrace (prefixWord ++ tailWord_1276042) baseStart_1276042 baseEnd_1276042 := by
    simpa [prefixWord, tailWord_1276042, baseEnd_1276042] using wordTrace_append hprefix tailTrace_1276042
  have hstable : (prefixWord ++ tailWord_1276042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276042).length < 2 ^ (prefixWord ++ tailWord_1276042).sum := by decide
  have hdescent : baseEnd_1276042 < baseStart_1276042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276087 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 3]
def baseStart_1276087 : Nat := 118140960795 + 1276087 * 2 ^ 59
def prefixEnd_1276087 : Nat := 4983230072969 + 3 ^ 40 * 1276087 * 2
def baseEnd_1276087 : Nat := 291220439090690683308395

theorem tailTrace_1276087 : CollatzResearch.WordTrace tailWord_1276087 prefixEnd_1276087 291220439090690683308395 := by
  unfold tailWord_1276087
  simp only [CollatzResearch.WordTrace]
  refine ⟨46542716527962212153754515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31028477685308141435836343 46542716527962212153754515)
  ·
    refine ⟨69814074791943318230631773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46542716527962212153754515 69814074791943318230631773)
    ·
      refine ⟨26180278046978744336486915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69814074791943318230631773 26180278046978744336486915)
      ·
        refine ⟨39270417070468116504730373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26180278046978744336486915 39270417070468116504730373)
        ·
          refine ⟨7363203200712771844636945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39270417070468116504730373 7363203200712771844636945)
          ·
            refine ⟨5522402400534578883477709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7363203200712771844636945 5522402400534578883477709)
            ·
              refine ⟨2070900900200467081304141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5522402400534578883477709 2070900900200467081304141)
              ·
                refine ⟨776587837575175155489053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2070900900200467081304141 776587837575175155489053)
                ·
                  refine ⟨291220439090690683308395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776587837575175155489053 291220439090690683308395)
                  ·
                    rfl

theorem cell21_1276087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3].length) (baseStart_1276087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276087 prefixEnd_1276087 := by exact prefixLift 1276087
  have htrace : WordTrace (prefixWord ++ tailWord_1276087) baseStart_1276087 baseEnd_1276087 := by
    simpa [prefixWord, tailWord_1276087, baseEnd_1276087] using wordTrace_append hprefix tailTrace_1276087
  have hstable : (prefixWord ++ tailWord_1276087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276087).length < 2 ^ (prefixWord ++ tailWord_1276087).sum := by decide
  have hdescent : baseEnd_1276087 < baseStart_1276087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276129 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_1276129 : Nat := 118140960795 + 1276129 * 2 ^ 59
def prefixEnd_1276129 : Nat := 4983230072969 + 3 ^ 40 * 1276129 * 2
def baseEnd_1276129 : Nat := 291230024062907943608309

theorem tailTrace_1276129 : CollatzResearch.WordTrace tailWord_1276129 prefixEnd_1276129 291230024062907943608309 := by
  unfold tailWord_1276129
  simp only [CollatzResearch.WordTrace]
  refine ⟨46544248393810053326783441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31029498929206702217855627 46544248393810053326783441)
  ·
    refine ⟨34908186295357539995087581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46544248393810053326783441 34908186295357539995087581)
    ·
      refine ⟨13090569860759077498157843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34908186295357539995087581 13090569860759077498157843)
      ·
        refine ⟨19635854791138616247236765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13090569860759077498157843 19635854791138616247236765)
        ·
          refine ⟨7363445546676981092713787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19635854791138616247236765 7363445546676981092713787)
          ·
            refine ⟨11045168320015471639070681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363445546676981092713787 11045168320015471639070681)
            ·
              refine ⟨8283876240011603729303011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11045168320015471639070681 8283876240011603729303011)
              ·
                refine ⟨12425814360017405593954517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283876240011603729303011 12425814360017405593954517)
                ·
                  refine ⟨291230024062907943608309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12425814360017405593954517 291230024062907943608309)
                  ·
                    rfl

theorem cell21_1276129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_1276129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276129 prefixEnd_1276129 := by exact prefixLift 1276129
  have htrace : WordTrace (prefixWord ++ tailWord_1276129) baseStart_1276129 baseEnd_1276129 := by
    simpa [prefixWord, tailWord_1276129, baseEnd_1276129] using wordTrace_append hprefix tailTrace_1276129
  have hstable : (prefixWord ++ tailWord_1276129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276129).length < 2 ^ (prefixWord ++ tailWord_1276129).sum := by decide
  have hdescent : baseEnd_1276129 < baseStart_1276129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276160 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_1276160 : Nat := 118140960795 + 1276160 * 2 ^ 59
def prefixEnd_1276160 : Nat := 4983230072969 + 3 ^ 40 * 1276160 * 2
def baseEnd_1276160 : Nat := 291237098685258778591579

theorem tailTrace_1276160 : CollatzResearch.WordTrace tailWord_1276160 prefixEnd_1276160 291237098685258778591579 := by
  unfold tailWord_1276160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23272689528348872810580967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31030252704465163747441289 23272689528348872810580967)
  ·
    refine ⟨34909034292523309215871451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23272689528348872810580967 34909034292523309215871451)
    ·
      refine ⟨52363551438784963823807177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34909034292523309215871451 52363551438784963823807177)
      ·
        refine ⟨39272663579088722867855383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52363551438784963823807177 39272663579088722867855383)
        ·
          refine ⟨58908995368633084301783075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39272663579088722867855383 58908995368633084301783075)
          ·
            refine ⟨88363493052949626452674613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58908995368633084301783075 88363493052949626452674613)
            ·
              refine ⟨8284077473714027479938245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88363493052949626452674613 8284077473714027479938245)
              ·
                refine ⟨1553264526321380152488421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8284077473714027479938245 1553264526321380152488421)
                ·
                  refine ⟨291237098685258778591579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553264526321380152488421 291237098685258778591579)
                  ·
                    rfl

theorem cell21_1276160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_1276160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276160 prefixEnd_1276160 := by exact prefixLift 1276160
  have htrace : WordTrace (prefixWord ++ tailWord_1276160) baseStart_1276160 baseEnd_1276160 := by
    simpa [prefixWord, tailWord_1276160, baseEnd_1276160] using wordTrace_append hprefix tailTrace_1276160
  have hstable : (prefixWord ++ tailWord_1276160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276160).length < 2 ^ (prefixWord ++ tailWord_1276160).sum := by decide
  have hdescent : baseEnd_1276160 < baseStart_1276160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276222 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1276222 : Nat := 118140960795 + 1276222 * 2 ^ 59
def prefixEnd_1276222 : Nat := 4983230072969 + 3 ^ 40 * 1276222 * 2
def baseEnd_1276222 : Nat := 291251247929960448558119

theorem tailTrace_1276222 : CollatzResearch.WordTrace tailWord_1276222 prefixEnd_1276222 291251247929960448558119 := by
  unfold tailWord_1276222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818455047809141276239865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31031760254982086806612613 5818455047809141276239865)
  ·
    refine ⟨4363841285856855957179899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5818455047809141276239865 4363841285856855957179899)
    ·
      refine ⟨6545761928785283935769849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363841285856855957179899 6545761928785283935769849)
      ·
        refine ⟨4909321446588962951827387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6545761928785283935769849 4909321446588962951827387)
        ·
          refine ⟨7363982169883444427741081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909321446588962951827387 7363982169883444427741081)
          ·
            refine ⟨5522986627412583320805811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7363982169883444427741081 5522986627412583320805811)
            ·
              refine ⟨8284479941118874981208717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522986627412583320805811 8284479941118874981208717)
              ·
                refine ⟨3106679977919578117953269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8284479941118874981208717 3106679977919578117953269)
                ·
                  refine ⟨291251247929960448558119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106679977919578117953269 291251247929960448558119)
                  ·
                    rfl

theorem cell21_1276222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1276222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276222 prefixEnd_1276222 := by exact prefixLift 1276222
  have htrace : WordTrace (prefixWord ++ tailWord_1276222) baseStart_1276222 baseEnd_1276222 := by
    simpa [prefixWord, tailWord_1276222, baseEnd_1276222] using wordTrace_append hprefix tailTrace_1276222
  have hstable : (prefixWord ++ tailWord_1276222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276222).length < 2 ^ (prefixWord ++ tailWord_1276222).sum := by decide
  have hdescent : baseEnd_1276222 < baseStart_1276222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276256 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_1276256 : Nat := 118140960795 + 1276256 * 2 ^ 59
def prefixEnd_1276256 : Nat := 4983230072969 + 3 ^ 40 * 1276256 * 2
def baseEnd_1276256 : Nat := 291259007193183944991383

theorem tailTrace_1276256 : CollatzResearch.WordTrace tailWord_1276256 prefixEnd_1276256 291259007193183944991383 := by
  unfold tailWord_1276256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23274440232174977008328311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31032586976233302677771081 23274440232174977008328311)
  ·
    refine ⟨34911660348262465512492467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23274440232174977008328311 34911660348262465512492467)
    ·
      refine ⟨52367490522393698268738701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34911660348262465512492467 52367490522393698268738701)
      ·
        refine ⟨19637808945897636850777013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52367490522393698268738701 19637808945897636850777013)
        ·
          refine ⟨1841044588677903454760345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19637808945897636850777013 1841044588677903454760345)
          ·
            refine ⟨1380783441508427591070259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841044588677903454760345 1380783441508427591070259)
            ·
              refine ⟨2071175162262641386605389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380783441508427591070259 2071175162262641386605389)
              ·
                refine ⟨776690685848490519977021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071175162262641386605389 776690685848490519977021)
                ·
                  refine ⟨291259007193183944991383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776690685848490519977021 291259007193183944991383)
                  ·
                    rfl

theorem cell21_1276256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_1276256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276256 prefixEnd_1276256 := by exact prefixLift 1276256
  have htrace : WordTrace (prefixWord ++ tailWord_1276256) baseStart_1276256 baseEnd_1276256 := by
    simpa [prefixWord, tailWord_1276256, baseEnd_1276256] using wordTrace_append hprefix tailTrace_1276256
  have hstable : (prefixWord ++ tailWord_1276256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276256).length < 2 ^ (prefixWord ++ tailWord_1276256).sum := by decide
  have hdescent : baseEnd_1276256 < baseStart_1276256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276343 : List Nat := [1, 1, 3, 1, 3, 5, 1, 6]
def baseStart_1276343 : Nat := 118140960795 + 1276343 * 2 ^ 59
def prefixEnd_1276343 : Nat := 4983230072969 + 3 ^ 40 * 1276343 * 2
def baseEnd_1276343 : Nat := 97092953926163709013735

theorem tailTrace_1276343 : CollatzResearch.WordTrace tailWord_1276343 prefixEnd_1276343 97092953926163709013735 := by
  unfold tailWord_1276343
  simp only [CollatzResearch.WordTrace]
  refine ⟨46552053615034767875073683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31034702410023178583382455 46552053615034767875073683)
  ·
    refine ⟨69828080422552151812610525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46552053615034767875073683 69828080422552151812610525)
    ·
      refine ⟨26185530158457056929728947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69828080422552151812610525 26185530158457056929728947)
      ·
        refine ⟨39278295237685585394593421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26185530158457056929728947 39278295237685585394593421)
        ·
          refine ⟨14729360714132094522972533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39278295237685585394593421 14729360714132094522972533)
          ·
            refine ⟨1380877566949883861528675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14729360714132094522972533 1380877566949883861528675)
            ·
              refine ⟨2071316350424825792293013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380877566949883861528675 2071316350424825792293013)
              ·
                refine ⟨97092953926163709013735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2071316350424825792293013 97092953926163709013735)
                ·
                  rfl

theorem cell21_1276343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 6].length) (baseStart_1276343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276343 prefixEnd_1276343 := by exact prefixLift 1276343
  have htrace : WordTrace (prefixWord ++ tailWord_1276343) baseStart_1276343 baseEnd_1276343 := by
    simpa [prefixWord, tailWord_1276343, baseEnd_1276343] using wordTrace_append hprefix tailTrace_1276343
  have hstable : (prefixWord ++ tailWord_1276343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276343).length < 2 ^ (prefixWord ++ tailWord_1276343).sum := by decide
  have hdescent : baseEnd_1276343 < baseStart_1276343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276374 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1276374 : Nat := 118140960795 + 1276374 * 2 ^ 59
def prefixEnd_1276374 : Nat := 4983230072969 + 3 ^ 40 * 1276374 * 2
def baseEnd_1276374 : Nat := 291285936400841962024475

theorem tailTrace_1276374 : CollatzResearch.WordTrace tailWord_1276374 prefixEnd_1276374 291285936400841962024475 := by
  unfold tailWord_1276374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909574017370153760590761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31035456185281640112968117 2909574017370153760590761)
  ·
    refine ⟨2182180513027615320443071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2909574017370153760590761 2182180513027615320443071)
    ·
      refine ⟨3273270769541422980664607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2182180513027615320443071 3273270769541422980664607)
      ·
        refine ⟨4909906154312134470996911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273270769541422980664607 4909906154312134470996911)
        ·
          refine ⟨7364859231468201706495367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909906154312134470996911 7364859231468201706495367)
          ·
            refine ⟨11047288847202302559743051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364859231468201706495367 11047288847202302559743051)
            ·
              refine ⟨16570933270803453839614577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047288847202302559743051 16570933270803453839614577)
              ·
                refine ⟨12428199953102590379710933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16570933270803453839614577 12428199953102590379710933)
                ·
                  refine ⟨291285936400841962024475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12428199953102590379710933 291285936400841962024475)
                  ·
                    rfl

theorem cell21_1276374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1276374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276374 prefixEnd_1276374 := by exact prefixLift 1276374
  have htrace : WordTrace (prefixWord ++ tailWord_1276374) baseStart_1276374 baseEnd_1276374 := by
    simpa [prefixWord, tailWord_1276374, baseEnd_1276374] using wordTrace_append hprefix tailTrace_1276374
  have hstable : (prefixWord ++ tailWord_1276374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276374).length < 2 ^ (prefixWord ++ tailWord_1276374).sum := by decide
  have hdescent : baseEnd_1276374 < baseStart_1276374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276436 : List Nat := [2, 4, 3, 1, 1, 3, 7]
def baseStart_1276436 : Nat := 118140960795 + 1276436 * 2 ^ 59
def prefixEnd_1276436 : Nat := 4983230072969 + 3 ^ 40 * 1276436 * 2
def baseEnd_1276436 : Nat := 32366676182838181332335

theorem tailTrace_1276436 : CollatzResearch.WordTrace tailWord_1276436 prefixEnd_1276436 32366676182838181332335 := by
  unfold tailWord_1276436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23277722801848922379104581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31036963735798563172139441 23277722801848922379104581)
  ·
    refine ⟨4364573025346672946082109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23277722801848922379104581 4364573025346672946082109)
    ·
      refine ⟨1636714884505002354780791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4364573025346672946082109 1636714884505002354780791)
      ·
        refine ⟨2455072326757503532171187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636714884505002354780791 2455072326757503532171187)
        ·
          refine ⟨3682608490136255298256781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455072326757503532171187 3682608490136255298256781)
          ·
            refine ⟨1380978183801095736846293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3682608490136255298256781 1380978183801095736846293)
            ·
              refine ⟨32366676182838181332335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1380978183801095736846293 32366676182838181332335)
              ·
                rfl

theorem cell21_1276436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 7].length) (baseStart_1276436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276436 prefixEnd_1276436 := by exact prefixLift 1276436
  have htrace : WordTrace (prefixWord ++ tailWord_1276436) baseStart_1276436 baseEnd_1276436 := by
    simpa [prefixWord, tailWord_1276436, baseEnd_1276436] using wordTrace_append hprefix tailTrace_1276436
  have hstable : (prefixWord ++ tailWord_1276436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276436).length < 2 ^ (prefixWord ++ tailWord_1276436).sum := by decide
  have hdescent : baseEnd_1276436 < baseStart_1276436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276526 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_1276526 : Nat := 118140960795 + 1276526 * 2 ^ 59
def prefixEnd_1276526 : Nat := 4983230072969 + 3 ^ 40 * 1276526 * 2
def baseEnd_1276526 : Nat := 291320624871723475490831

theorem tailTrace_1276526 : CollatzResearch.WordTrace tailWord_1276526 prefixEnd_1276526 291320624871723475490831 := by
  unfold tailWord_1276526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819841021671473766123179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31039152115581193419323621 5819841021671473766123179)
  ·
    refine ⟨8729761532507210649184769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5819841021671473766123179 8729761532507210649184769)
    ·
      refine ⟨6547321149380407986888577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8729761532507210649184769 6547321149380407986888577)
      ·
        refine ⟨4910490862035305990166433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6547321149380407986888577 4910490862035305990166433)
        ·
          refine ⟨3682868146526479492624825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4910490862035305990166433 3682868146526479492624825)
          ·
            refine ⟨2762151109894859619468619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3682868146526479492624825 2762151109894859619468619)
            ·
              refine ⟨4143226664842289429202929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762151109894859619468619 4143226664842289429202929)
              ·
                refine ⟨3107419998631717071902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143226664842289429202929 3107419998631717071902197)
                ·
                  refine ⟨291320624871723475490831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3107419998631717071902197 291320624871723475490831)
                  ·
                    rfl

theorem cell21_1276526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_1276526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276526 prefixEnd_1276526 := by exact prefixLift 1276526
  have htrace : WordTrace (prefixWord ++ tailWord_1276526) baseStart_1276526 baseEnd_1276526 := by
    simpa [prefixWord, tailWord_1276526, baseEnd_1276526] using wordTrace_append hprefix tailTrace_1276526
  have hstable : (prefixWord ++ tailWord_1276526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276526).length < 2 ^ (prefixWord ++ tailWord_1276526).sum := by decide
  have hdescent : baseEnd_1276526 < baseStart_1276526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276574 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1276574 : Nat := 118140960795 + 1276574 * 2 ^ 59
def prefixEnd_1276574 : Nat := 4983230072969 + 3 ^ 40 * 1276574 * 2
def baseEnd_1276574 : Nat := 291331579125686058690733

theorem tailTrace_1276574 : CollatzResearch.WordTrace tailWord_1276574 prefixEnd_1276574 291331579125686058690733 := by
  unfold tailWord_1276574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820059859649736790841597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31040319251465262884488517 5820059859649736790841597)
  ·
    refine ⟨2182522447368651296565599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5820059859649736790841597 2182522447368651296565599)
    ·
      refine ⟨3273783671052976944848399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2182522447368651296565599 3273783671052976944848399)
      ·
        refine ⟨4910675506579465417272599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273783671052976944848399 4910675506579465417272599)
        ·
          refine ⟨7366013259869198125908899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910675506579465417272599 7366013259869198125908899)
          ·
            refine ⟨11049019889803797188863349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366013259869198125908899 11049019889803797188863349)
            ·
              refine ⟨1035845614669105986455939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11049019889803797188863349 1035845614669105986455939)
              ·
                refine ⟨1553768422003658979683909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035845614669105986455939 1553768422003658979683909)
                ·
                  refine ⟨291331579125686058690733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553768422003658979683909 291331579125686058690733)
                  ·
                    rfl

theorem cell21_1276574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1276574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276574 prefixEnd_1276574 := by exact prefixLift 1276574
  have htrace : WordTrace (prefixWord ++ tailWord_1276574) baseStart_1276574 baseEnd_1276574 := by
    simpa [prefixWord, tailWord_1276574, baseEnd_1276574] using wordTrace_append hprefix tailTrace_1276574
  have hstable : (prefixWord ++ tailWord_1276574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276574).length < 2 ^ (prefixWord ++ tailWord_1276574).sum := by decide
  have hdescent : baseEnd_1276574 < baseStart_1276574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276771 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 3]
def baseStart_1276771 : Nat := 118140960795 + 1276771 * 2 ^ 59
def prefixEnd_1276771 : Nat := 4983230072969 + 3 ^ 40 * 1276771 * 2
def baseEnd_1276771 : Nat := 291376537209657493906997

theorem tailTrace_1276771 : CollatzResearch.WordTrace tailWord_1276771 prefixEnd_1276771 291376537209657493906997 := by
  unfold tailWord_1276771
  simp only [CollatzResearch.WordTrace]
  refine ⟨46567664057484196971654167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31045109371656131314436111 46567664057484196971654167)
  ·
    refine ⟨69851496086226295457481251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46567664057484196971654167 69851496086226295457481251)
    ·
      refine ⟨104777244129339443186221877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69851496086226295457481251 104777244129339443186221877)
      ·
        refine ⟨9822866637125572798708301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104777244129339443186221877 9822866637125572798708301)
        ·
          refine ⟨3683574988922089799515613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9822866637125572798708301 3683574988922089799515613)
          ·
            refine ⟨1381340620845783674818355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3683574988922089799515613 1381340620845783674818355)
            ·
              refine ⟨2072010931268675512227533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381340620845783674818355 2072010931268675512227533)
              ·
                refine ⟨777004099225753317085325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2072010931268675512227533 777004099225753317085325)
                ·
                  refine ⟨291376537209657493906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777004099225753317085325 291376537209657493906997)
                  ·
                    rfl

theorem cell21_1276771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3].length) (baseStart_1276771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276771 prefixEnd_1276771 := by exact prefixLift 1276771
  have htrace : WordTrace (prefixWord ++ tailWord_1276771) baseStart_1276771 baseEnd_1276771 := by
    simpa [prefixWord, tailWord_1276771, baseEnd_1276771] using wordTrace_append hprefix tailTrace_1276771
  have hstable : (prefixWord ++ tailWord_1276771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276771).length < 2 ^ (prefixWord ++ tailWord_1276771).sum := by decide
  have hdescent : baseEnd_1276771 < baseStart_1276771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276906 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_1276906 : Nat := 118140960795 + 1276906 * 2 ^ 59
def prefixEnd_1276906 : Nat := 4983230072969 + 3 ^ 40 * 1276906 * 2
def baseEnd_1276906 : Nat := 291407346048927259156721

theorem tailTrace_1276906 : CollatzResearch.WordTrace tailWord_1276906 prefixEnd_1276906 291407346048927259156721 := by
  unfold tailWord_1276906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643146977998778756954643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31048391941330076685212381 11643146977998778756954643)
  ·
    refine ⟨17464720466998168135431965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11643146977998778756954643 17464720466998168135431965)
    ·
      refine ⟨6549270175124313050786987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17464720466998168135431965 6549270175124313050786987)
      ·
        refine ⟨9823905262686469576180481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549270175124313050786987 9823905262686469576180481)
        ·
          refine ⟨7367928947014852182135361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9823905262686469576180481 7367928947014852182135361)
          ·
            refine ⟨5525946710261139136601521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7367928947014852182135361 5525946710261139136601521)
            ·
              refine ⟨4144460032695854352451141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5525946710261139136601521 4144460032695854352451141)
              ·
                refine ⟨777086256130472691084589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4144460032695854352451141 777086256130472691084589)
                ·
                  refine ⟨291407346048927259156721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777086256130472691084589 291407346048927259156721)
                  ·
                    rfl

theorem cell21_1276906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_1276906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1276906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1276906 prefixEnd_1276906 := by exact prefixLift 1276906
  have htrace : WordTrace (prefixWord ++ tailWord_1276906) baseStart_1276906 baseEnd_1276906 := by
    simpa [prefixWord, tailWord_1276906, baseEnd_1276906] using wordTrace_append hprefix tailTrace_1276906
  have hstable : (prefixWord ++ tailWord_1276906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276906).length < 2 ^ (prefixWord ++ tailWord_1276906).sum := by decide
  have hdescent : baseEnd_1276906 < baseStart_1276906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277024 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_1277024 : Nat := 118140960795 + 1277024 * 2 ^ 59
def prefixEnd_1277024 : Nat := 4983230072969 + 3 ^ 40 * 1277024 * 2
def baseEnd_1277024 : Nat := 291434275256585276189813

theorem tailTrace_1277024 : CollatzResearch.WordTrace tailWord_1277024 prefixEnd_1277024 291434275256585276189813 := by
  unfold tailWord_1277024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23288445862783810590307063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31051261150378414120409417 23288445862783810590307063)
  ·
    refine ⟨34932668794175715885460595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23288445862783810590307063 34932668794175715885460595)
    ·
      refine ⟨52399003191263573828190893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34932668794175715885460595 52399003191263573828190893)
      ·
        refine ⟨19649626196723840185571585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52399003191263573828190893 19649626196723840185571585)
        ·
          refine ⟨14737219647542880139178689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19649626196723840185571585 14737219647542880139178689)
          ·
            refine ⟨11052914735657160104384017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14737219647542880139178689 11052914735657160104384017)
            ·
              refine ⟨8289686051742870078288013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11052914735657160104384017 8289686051742870078288013)
              ·
                refine ⟨3108632269403576279358005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8289686051742870078288013 3108632269403576279358005)
                ·
                  refine ⟨291434275256585276189813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108632269403576279358005 291434275256585276189813)
                  ·
                    rfl

theorem cell21_1277024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_1277024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277024 prefixEnd_1277024 := by exact prefixLift 1277024
  have htrace : WordTrace (prefixWord ++ tailWord_1277024) baseStart_1277024 baseEnd_1277024 := by
    simpa [prefixWord, tailWord_1277024, baseEnd_1277024] using wordTrace_append hprefix tailTrace_1277024
  have hstable : (prefixWord ++ tailWord_1277024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277024).length < 2 ^ (prefixWord ++ tailWord_1277024).sum := by decide
  have hdescent : baseEnd_1277024 < baseStart_1277024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277126 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1277126 : Nat := 118140960795 + 1277126 * 2 ^ 59
def prefixEnd_1277126 : Nat := 4983230072969 + 3 ^ 40 * 1277126 * 2
def baseEnd_1277126 : Nat := 291457553046255765489605

theorem tailTrace_1277126 : CollatzResearch.WordTrace tailWord_1277126 prefixEnd_1277126 291457553046255765489605 := by
  unfold tailWord_1277126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455644124099940393775851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31053741314132061733884821 1455644124099940393775851)
  ·
    refine ⟨2183466186149910590663777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1455644124099940393775851 2183466186149910590663777)
    ·
      refine ⟨1637599639612432942997833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2183466186149910590663777 1637599639612432942997833)
      ·
        refine ⟨1228199729709324707248375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1637599639612432942997833 1228199729709324707248375)
        ·
          refine ⟨1842299594563987060872563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228199729709324707248375 1842299594563987060872563)
          ·
            refine ⟨2763449391845980591308845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842299594563987060872563 2763449391845980591308845)
            ·
              refine ⟨1036293521942242721740817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2763449391845980591308845 1036293521942242721740817)
              ·
                refine ⟨777220141456682041305613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036293521942242721740817 777220141456682041305613)
                ·
                  refine ⟨291457553046255765489605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777220141456682041305613 291457553046255765489605)
                  ·
                    rfl

theorem cell21_1277126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1277126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277126 prefixEnd_1277126 := by exact prefixLift 1277126
  have htrace : WordTrace (prefixWord ++ tailWord_1277126) baseStart_1277126 baseEnd_1277126 := by
    simpa [prefixWord, tailWord_1277126, baseEnd_1277126] using wordTrace_append hprefix tailTrace_1277126
  have hstable : (prefixWord ++ tailWord_1277126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277126).length < 2 ^ (prefixWord ++ tailWord_1277126).sum := by decide
  have hdescent : baseEnd_1277126 < baseStart_1277126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277134 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1277134 : Nat := 118140960795 + 1277134 * 2 ^ 59
def prefixEnd_1277134 : Nat := 4983230072969 + 3 ^ 40 * 1277134 * 2
def baseEnd_1277134 : Nat := 291459378755249529356255

theorem tailTrace_1277134 : CollatzResearch.WordTrace tailWord_1277134 prefixEnd_1277134 291459378755249529356255 := by
  unfold tailWord_1277134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822612969396138745889807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31053935836779406644745637 5822612969396138745889807)
  ·
    refine ⟨8733919454094208118834711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5822612969396138745889807 8733919454094208118834711)
    ·
      refine ⟨13100879181141312178252067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733919454094208118834711 13100879181141312178252067)
      ·
        refine ⟨19651318771711968267378101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13100879181141312178252067 19651318771711968267378101)
        ·
          refine ⟨1842311134847997025066697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19651318771711968267378101 1842311134847997025066697)
          ·
            refine ⟨1381733351135997768800023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842311134847997025066697 1381733351135997768800023)
            ·
              refine ⟨2072600026703996653200035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381733351135997768800023 2072600026703996653200035)
              ·
                refine ⟨3108900040055994979800053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072600026703996653200035 3108900040055994979800053)
                ·
                  refine ⟨291459378755249529356255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108900040055994979800053 291459378755249529356255)
                  ·
                    rfl

theorem cell21_1277134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1277134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277134 prefixEnd_1277134 := by exact prefixLift 1277134
  have htrace : WordTrace (prefixWord ++ tailWord_1277134) baseStart_1277134 baseEnd_1277134 := by
    simpa [prefixWord, tailWord_1277134, baseEnd_1277134] using wordTrace_append hprefix tailTrace_1277134
  have hstable : (prefixWord ++ tailWord_1277134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277134).length < 2 ^ (prefixWord ++ tailWord_1277134).sum := by decide
  have hdescent : baseEnd_1277134 < baseStart_1277134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277193 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 3]
def baseStart_1277193 : Nat := 118140960795 + 1277193 * 2 ^ 59
def prefixEnd_1277193 : Nat := 4983230072969 + 3 ^ 40 * 1277193 * 2
def baseEnd_1277193 : Nat := 291472843359078537872801

theorem tailTrace_1277193 : CollatzResearch.WordTrace tailWord_1277193 prefixEnd_1277193 291472843359078537872801 := by
  unfold tailWord_1277193
  simp only [CollatzResearch.WordTrace]
  refine ⟨46583055661955363043516233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31055370441303575362344155 46583055661955363043516233)
  ·
    refine ⟨34937291746466522282637175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46583055661955363043516233 34937291746466522282637175)
    ·
      refine ⟨52405937619699783423955763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34937291746466522282637175 52405937619699783423955763)
      ·
        refine ⟨78608906429549675135933645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52405937619699783423955763 78608906429549675135933645)
        ·
          refine ⟨29478339911081128175975117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78608906429549675135933645 29478339911081128175975117)
          ·
            refine ⟨11054377466655423065990669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29478339911081128175975117 11054377466655423065990669)
            ·
              refine ⟨4145391549995783649746501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11054377466655423065990669 4145391549995783649746501)
              ·
                refine ⟨777260915624209434327469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4145391549995783649746501 777260915624209434327469)
                ·
                  refine ⟨291472843359078537872801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777260915624209434327469 291472843359078537872801)
                  ·
                    rfl

theorem cell21_1277193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_1277193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277193 prefixEnd_1277193 := by exact prefixLift 1277193
  have htrace : WordTrace (prefixWord ++ tailWord_1277193) baseStart_1277193 baseEnd_1277193 := by
    simpa [prefixWord, tailWord_1277193, baseEnd_1277193] using wordTrace_append hprefix tailTrace_1277193
  have hstable : (prefixWord ++ tailWord_1277193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277193).length < 2 ^ (prefixWord ++ tailWord_1277193).sum := by decide
  have hdescent : baseEnd_1277193 < baseStart_1277193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277207 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_1277207 : Nat := 118140960795 + 1277207 * 2 ^ 59
def prefixEnd_1277207 : Nat := 4983230072969 + 3 ^ 40 * 1277207 * 2
def baseEnd_1277207 : Nat := 291476038349817624639439

theorem tailTrace_1277207 : CollatzResearch.WordTrace tailWord_1277207 prefixEnd_1277207 291476038349817624639439 := by
  unfold tailWord_1277207
  simp only [CollatzResearch.WordTrace]
  refine ⟨46583566283904643434525875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31055710855936428956350583 46583566283904643434525875)
  ·
    refine ⟨69875349425856965151788813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46583566283904643434525875 69875349425856965151788813)
    ·
      refine ⟨26203256034696361931920805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69875349425856965151788813 26203256034696361931920805)
      ·
        refine ⟨4913110506505567862235151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26203256034696361931920805 4913110506505567862235151)
        ·
          refine ⟨7369665759758351793352727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913110506505567862235151 7369665759758351793352727)
          ·
            refine ⟨11054498639637527690029091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7369665759758351793352727 11054498639637527690029091)
            ·
              refine ⟨16581747959456291535043637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11054498639637527690029091 16581747959456291535043637)
              ·
                refine ⟨1554538871199027331410341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16581747959456291535043637 1554538871199027331410341)
                ·
                  refine ⟨291476038349817624639439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554538871199027331410341 291476038349817624639439)
                  ·
                    rfl

theorem cell21_1277207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_1277207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277207 prefixEnd_1277207 := by exact prefixLift 1277207
  have htrace : WordTrace (prefixWord ++ tailWord_1277207) baseStart_1277207 baseEnd_1277207 := by
    simpa [prefixWord, tailWord_1277207, baseEnd_1277207] using wordTrace_append hprefix tailTrace_1277207
  have hstable : (prefixWord ++ tailWord_1277207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277207).length < 2 ^ (prefixWord ++ tailWord_1277207).sum := by decide
  have hdescent : baseEnd_1277207 < baseStart_1277207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277241 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 4]
def baseStart_1277241 : Nat := 118140960795 + 1277241 * 2 ^ 59
def prefixEnd_1277241 : Nat := 4983230072969 + 3 ^ 40 * 1277241 * 2
def baseEnd_1277241 : Nat := 291483797613041121072703

theorem tailTrace_1277241 : CollatzResearch.WordTrace tailWord_1277241 prefixEnd_1277241 291483797613041121072703 := by
  unfold tailWord_1277241
  simp only [CollatzResearch.WordTrace]
  refine ⟨46584806365781467241263577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31056537577187644827509051 46584806365781467241263577)
  ·
    refine ⟨34938604774336100430947683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46584806365781467241263577 34938604774336100430947683)
    ·
      refine ⟨52407907161504150646421525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34938604774336100430947683 52407907161504150646421525)
      ·
        refine ⟨2456620648195507061551009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52407907161504150646421525 2456620648195507061551009)
        ·
          refine ⟨1842465486146630296163257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2456620648195507061551009 1842465486146630296163257)
          ·
            refine ⟨1381849114609972722122443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842465486146630296163257 1381849114609972722122443)
            ·
              refine ⟨2072773671914959083183665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381849114609972722122443 2072773671914959083183665)
              ·
                refine ⟨1554580253936219312387749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072773671914959083183665 1554580253936219312387749)
                ·
                  refine ⟨291483797613041121072703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554580253936219312387749 291483797613041121072703)
                  ·
                    rfl

theorem cell21_1277241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_1277241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277241 prefixEnd_1277241 := by exact prefixLift 1277241
  have htrace : WordTrace (prefixWord ++ tailWord_1277241) baseStart_1277241 baseEnd_1277241 := by
    simpa [prefixWord, tailWord_1277241, baseEnd_1277241] using wordTrace_append hprefix tailTrace_1277241
  have hstable : (prefixWord ++ tailWord_1277241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277241).length < 2 ^ (prefixWord ++ tailWord_1277241).sum := by decide
  have hdescent : baseEnd_1277241 < baseStart_1277241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277387 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_1277387 : Nat := 118140960795 + 1277387 * 2 ^ 59
def prefixEnd_1277387 : Nat := 4983230072969 + 3 ^ 40 * 1277387 * 2
def baseEnd_1277387 : Nat := 291517116802177311639071

theorem tailTrace_1277387 : CollatzResearch.WordTrace tailWord_1277387 prefixEnd_1277387 291517116802177311639071 := by
  unfold tailWord_1277387
  simp only [CollatzResearch.WordTrace]
  refine ⟨46590131423252534176078415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31060087615501689450718943 46590131423252534176078415)
  ·
    refine ⟨69885197134878801264117623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46590131423252534176078415 69885197134878801264117623)
    ·
      refine ⟨104827795702318201896176435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69885197134878801264117623 104827795702318201896176435)
      ·
        refine ⟨157241693553477302844264653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104827795702318201896176435 157241693553477302844264653)
        ·
          refine ⟨58965635082553988566599245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157241693553477302844264653 58965635082553988566599245)
          ·
            refine ⟨22112113155957745712474717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58965635082553988566599245 22112113155957745712474717)
            ·
              refine ⟨8292042433484154642178019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22112113155957745712474717 8292042433484154642178019)
              ·
                refine ⟨12438063650226231963267029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8292042433484154642178019 12438063650226231963267029)
                ·
                  refine ⟨291517116802177311639071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438063650226231963267029 291517116802177311639071)
                  ·
                    rfl

theorem cell21_1277387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_1277387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277387 prefixEnd_1277387 := by exact prefixLift 1277387
  have htrace : WordTrace (prefixWord ++ tailWord_1277387) baseStart_1277387 baseEnd_1277387 := by
    simpa [prefixWord, tailWord_1277387, baseEnd_1277387] using wordTrace_append hprefix tailTrace_1277387
  have hstable : (prefixWord ++ tailWord_1277387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277387).length < 2 ^ (prefixWord ++ tailWord_1277387).sum := by decide
  have hdescent : baseEnd_1277387 < baseStart_1277387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277573 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 3]
def baseStart_1277573 : Nat := 118140960795 + 1277573 * 2 ^ 59
def prefixEnd_1277573 : Nat := 4983230072969 + 3 ^ 40 * 1277573 * 2
def baseEnd_1277573 : Nat := 291559564536282321538691

theorem tailTrace_1277573 : CollatzResearch.WordTrace tailWord_1277573 prefixEnd_1277573 291559564536282321538691 := by
  unfold tailWord_1277573
  simp only [CollatzResearch.WordTrace]
  refine ⟨46596915400578687942349373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31064610267052458628232915 46596915400578687942349373)
  ·
    refine ⟨17473843275217007978381015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46596915400578687942349373 17473843275217007978381015)
    ·
      refine ⟨26210764912825511967571523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17473843275217007978381015 26210764912825511967571523)
      ·
        refine ⟨39316147369238267951357285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26210764912825511967571523 39316147369238267951357285)
        ·
          refine ⟨7371777631732175240879491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39316147369238267951357285 7371777631732175240879491)
          ·
            refine ⟨11057666447598262861319237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371777631732175240879491 11057666447598262861319237)
            ·
              refine ⟨2073312458924674286497357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11057666447598262861319237 2073312458924674286497357)
              ·
                refine ⟨777492172096752857436509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2073312458924674286497357 777492172096752857436509)
                ·
                  refine ⟨291559564536282321538691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777492172096752857436509 291559564536282321538691)
                  ·
                    rfl

theorem cell21_1277573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_1277573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277573 prefixEnd_1277573 := by exact prefixLift 1277573
  have htrace : WordTrace (prefixWord ++ tailWord_1277573) baseStart_1277573 baseEnd_1277573 := by
    simpa [prefixWord, tailWord_1277573, baseEnd_1277573] using wordTrace_append hprefix tailTrace_1277573
  have hstable : (prefixWord ++ tailWord_1277573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277573).length < 2 ^ (prefixWord ++ tailWord_1277573).sum := by decide
  have hdescent : baseEnd_1277573 < baseStart_1277573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277604 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1277604 : Nat := 118140960795 + 1277604 * 2 ^ 59
def prefixEnd_1277604 : Nat := 4983230072969 + 3 ^ 40 * 1277604 * 2
def baseEnd_1277604 : Nat := 291566639158633156521961

theorem tailTrace_1277604 : CollatzResearch.WordTrace tailWord_1277604 prefixEnd_1277604 291566639158633156521961 := by
  unfold tailWord_1277604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299023031733190118363933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31065364042310920157818577 23299023031733190118363933)
  ·
    refine ⟨8737133636899946294386475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23299023031733190118363933 8737133636899946294386475)
    ·
      refine ⟨13105700455349919441579713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8737133636899946294386475 13105700455349919441579713)
      ·
        refine ⟨9829275341512439581184785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13105700455349919441579713 9829275341512439581184785)
        ·
          refine ⟨7371956506134329685888589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9829275341512439581184785 7371956506134329685888589)
          ·
            refine ⟨2764483689800373632208221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7371956506134329685888589 2764483689800373632208221)
            ·
              refine ⟨1036681383675140112078083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2764483689800373632208221 1036681383675140112078083)
              ·
                refine ⟨1555022075512710168117125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036681383675140112078083 1555022075512710168117125)
                ·
                  refine ⟨291566639158633156521961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555022075512710168117125 291566639158633156521961)
                  ·
                    rfl

theorem cell21_1277604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1277604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277604 prefixEnd_1277604 := by exact prefixLift 1277604
  have htrace : WordTrace (prefixWord ++ tailWord_1277604) baseStart_1277604 baseEnd_1277604 := by
    simpa [prefixWord, tailWord_1277604, baseEnd_1277604] using wordTrace_append hprefix tailTrace_1277604
  have hstable : (prefixWord ++ tailWord_1277604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277604).length < 2 ^ (prefixWord ++ tailWord_1277604).sum := by decide
  have hdescent : baseEnd_1277604 < baseStart_1277604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277615 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_1277615 : Nat := 118140960795 + 1277615 * 2 ^ 59
def prefixEnd_1277615 : Nat := 4983230072969 + 3 ^ 40 * 1277615 * 2
def baseEnd_1277615 : Nat := 291569149508499581838605

theorem tailTrace_1277615 : CollatzResearch.WordTrace tailWord_1277615 prefixEnd_1277615 291569149508499581838605 := by
  unfold tailWord_1277615
  simp only [CollatzResearch.WordTrace]
  refine ⟨46598447266426529115378299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31065631510951019410252199 46598447266426529115378299)
  ·
    refine ⟨69897670899639793673067449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46598447266426529115378299 69897670899639793673067449)
    ·
      refine ⟨52423253174729845254800587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69897670899639793673067449 52423253174729845254800587)
      ·
        refine ⟨78634879762094767882200881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52423253174729845254800587 78634879762094767882200881)
        ·
          refine ⟨58976159821571075911650661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78634879762094767882200881 58976159821571075911650661)
          ·
            refine ⟨11058029966544576733434499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58976159821571075911650661 11058029966544576733434499)
            ·
              refine ⟨16587044949816865100151749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11058029966544576733434499 16587044949816865100151749)
              ·
                refine ⟨3110070928090662206278453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16587044949816865100151749 3110070928090662206278453)
                ·
                  refine ⟨291569149508499581838605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3110070928090662206278453 291569149508499581838605)
                  ·
                    rfl

theorem cell21_1277615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_1277615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277615 prefixEnd_1277615 := by exact prefixLift 1277615
  have htrace : WordTrace (prefixWord ++ tailWord_1277615) baseStart_1277615 baseEnd_1277615 := by
    simpa [prefixWord, tailWord_1277615, baseEnd_1277615] using wordTrace_append hprefix tailTrace_1277615
  have hstable : (prefixWord ++ tailWord_1277615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277615).length < 2 ^ (prefixWord ++ tailWord_1277615).sum := by decide
  have hdescent : baseEnd_1277615 < baseStart_1277615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277646 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1277646 : Nat := 118140960795 + 1277646 * 2 ^ 59
def prefixEnd_1277646 : Nat := 4983230072969 + 3 ^ 40 * 1277646 * 2
def baseEnd_1277646 : Nat := 291576224130850416821875

theorem tailTrace_1277646 : CollatzResearch.WordTrace tailWord_1277646 prefixEnd_1277646 291576224130850416821875 := by
  unfold tailWord_1277646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824947241164277676219599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31066385286209480939837861 5824947241164277676219599)
  ·
    refine ⟨8737420861746416514329399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5824947241164277676219599 8737420861746416514329399)
    ·
      refine ⟨13106131292619624771494099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8737420861746416514329399 13106131292619624771494099)
      ·
        refine ⟨19659196938929437157241149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13106131292619624771494099 19659196938929437157241149)
        ·
          refine ⟨7372198852098538933965431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19659196938929437157241149 7372198852098538933965431)
          ·
            refine ⟨11058298278147808400948147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7372198852098538933965431 11058298278147808400948147)
            ·
              refine ⟨16587447417221712601422221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11058298278147808400948147 16587447417221712601422221)
              ·
                refine ⟨6220292781458142225533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16587447417221712601422221 6220292781458142225533333)
                ·
                  refine ⟨291576224130850416821875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6220292781458142225533333 291576224130850416821875)
                  ·
                    rfl

theorem cell21_1277646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1277646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277646 prefixEnd_1277646 := by exact prefixLift 1277646
  have htrace : WordTrace (prefixWord ++ tailWord_1277646) baseStart_1277646 baseEnd_1277646 := by
    simpa [prefixWord, tailWord_1277646, baseEnd_1277646] using wordTrace_append hprefix tailTrace_1277646
  have hstable : (prefixWord ++ tailWord_1277646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277646).length < 2 ^ (prefixWord ++ tailWord_1277646).sum := by decide
  have hdescent : baseEnd_1277646 < baseStart_1277646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277677 : List Nat := [1, 5, 1, 2, 1, 2, 2, 7]
def baseStart_1277677 : Nat := 118140960795 + 1277677 * 2 ^ 59
def prefixEnd_1277677 : Nat := 4983230072969 + 3 ^ 40 * 1277677 * 2
def baseEnd_1277677 : Nat := 97194432917733750601715

theorem tailTrace_1277677 : CollatzResearch.WordTrace tailWord_1277677 prefixEnd_1277677 97194432917733750601715 := by
  unfold tailWord_1277677
  simp only [CollatzResearch.WordTrace]
  refine ⟨46600708592201913704135285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31067139061467942469423523 46600708592201913704135285)
  ·
    refine ⟨4368816430518929409762683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46600708592201913704135285 4368816430518929409762683)
    ·
      refine ⟨6553224645778394114644025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4368816430518929409762683 6553224645778394114644025)
      ·
        refine ⟨4914918484333795585983019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6553224645778394114644025 4914918484333795585983019)
        ·
          refine ⟨7372377726500693378974529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914918484333795585983019 7372377726500693378974529)
          ·
            refine ⟨5529283294875520034230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7372377726500693378974529 5529283294875520034230897)
            ·
              refine ⟨4146962471156640025673173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5529283294875520034230897 4146962471156640025673173)
              ·
                refine ⟨97194432917733750601715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4146962471156640025673173 97194432917733750601715)
                ·
                  rfl

theorem cell21_1277677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_1277677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277677 prefixEnd_1277677 := by exact prefixLift 1277677
  have htrace : WordTrace (prefixWord ++ tailWord_1277677) baseStart_1277677 baseEnd_1277677 := by
    simpa [prefixWord, tailWord_1277677, baseEnd_1277677] using wordTrace_append hprefix tailTrace_1277677
  have hstable : (prefixWord ++ tailWord_1277677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277677).length < 2 ^ (prefixWord ++ tailWord_1277677).sum := by decide
  have hdescent : baseEnd_1277677 < baseStart_1277677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277694 : List Nat := [4, 2, 2, 1, 4, 8]
def baseStart_1277694 : Nat := 118140960795 + 1277694 * 2 ^ 59
def prefixEnd_1277694 : Nat := 4983230072969 + 3 ^ 40 * 1277694 * 2
def baseEnd_1277694 : Nat := 10799525125363444445251

theorem tailTrace_1277694 : CollatzResearch.WordTrace tailWord_1277694 prefixEnd_1277694 10799525125363444445251 := by
  unfold tailWord_1277694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825166079142540700938017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31067552422093550405002757 5825166079142540700938017)
  ·
    refine ⟨4368874559356905525703513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5825166079142540700938017 4368874559356905525703513)
    ·
      refine ⟨3276655919517679144277635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4368874559356905525703513 3276655919517679144277635)
      ·
        refine ⟨4914983879276518716416453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276655919517679144277635 4914983879276518716416453)
        ·
          refine ⟨921559477364347259328085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4914983879276518716416453 921559477364347259328085)
          ·
            refine ⟨10799525125363444445251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 921559477364347259328085 10799525125363444445251)
            ·
              rfl

theorem cell21_1277694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 8].length) (baseStart_1277694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277694 prefixEnd_1277694 := by exact prefixLift 1277694
  have htrace : WordTrace (prefixWord ++ tailWord_1277694) baseStart_1277694 baseEnd_1277694 := by
    simpa [prefixWord, tailWord_1277694, baseEnd_1277694] using wordTrace_append hprefix tailTrace_1277694
  have hstable : (prefixWord ++ tailWord_1277694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277694).length < 2 ^ (prefixWord ++ tailWord_1277694).sum := by decide
  have hdescent : baseEnd_1277694 < baseStart_1277694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277767 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_1277767 : Nat := 118140960795 + 1277767 * 2 ^ 59
def prefixEnd_1277767 : Nat := 4983230072969 + 3 ^ 40 * 1277767 * 2
def baseEnd_1277767 : Nat := 291603837979381095304961

theorem tailTrace_1277767 : CollatzResearch.WordTrace tailWord_1277767 prefixEnd_1277767 291603837979381095304961 := by
  unfold tailWord_1277767
  simp only [CollatzResearch.WordTrace]
  refine ⟨46603991161875859074911555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31069327441250572716607703 46603991161875859074911555)
  ·
    refine ⟨69905986742813788612367333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46603991161875859074911555 69905986742813788612367333)
    ·
      refine ⟨13107372514277585364818875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69905986742813788612367333 13107372514277585364818875)
      ·
        refine ⟨19661058771416378047228313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13107372514277585364818875 19661058771416378047228313)
        ·
          refine ⟨14745794078562283535421235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19661058771416378047228313 14745794078562283535421235)
          ·
            refine ⟨22118691117843425303131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745794078562283535421235 22118691117843425303131853)
            ·
              refine ⟨8294509169191284488674445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22118691117843425303131853 8294509169191284488674445)
              ·
                refine ⟨3110440938446731683252917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8294509169191284488674445 3110440938446731683252917)
                ·
                  refine ⟨291603837979381095304961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3110440938446731683252917 291603837979381095304961)
                  ·
                    rfl

theorem cell21_1277767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_1277767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277767 prefixEnd_1277767 := by exact prefixLift 1277767
  have htrace : WordTrace (prefixWord ++ tailWord_1277767) baseStart_1277767 baseEnd_1277767 := by
    simpa [prefixWord, tailWord_1277767, baseEnd_1277767] using wordTrace_append hprefix tailTrace_1277767
  have hstable : (prefixWord ++ tailWord_1277767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277767).length < 2 ^ (prefixWord ++ tailWord_1277767).sum := by decide
  have hdescent : baseEnd_1277767 < baseStart_1277767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277773 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1277773 : Nat := 118140960795 + 1277773 * 2 ^ 59
def prefixEnd_1277773 : Nat := 4983230072969 + 3 ^ 40 * 1277773 * 2
def baseEnd_1277773 : Nat := 291605207261126418204949

theorem tailTrace_1277773 : CollatzResearch.WordTrace tailWord_1277773 prefixEnd_1277773 291605207261126418204949 := by
  unfold tailWord_1277773
  simp only [CollatzResearch.WordTrace]
  refine ⟨46604209999854122099629973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31069473333236081399753315 46604209999854122099629973)
  ·
    refine ⟨2184572343743161973420155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46604209999854122099629973 2184572343743161973420155)
    ·
      refine ⟨3276858515614742960130233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184572343743161973420155 3276858515614742960130233)
      ·
        refine ⟨2457643886711057220097675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3276858515614742960130233 2457643886711057220097675)
        ·
          refine ⟨3686465830066585830146513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457643886711057220097675 3686465830066585830146513)
          ·
            refine ⟨2764849372549939372609885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3686465830066585830146513 2764849372549939372609885)
            ·
              refine ⟨1036818514706227264728707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2764849372549939372609885 1036818514706227264728707)
              ·
                refine ⟨1555227772059340897093061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036818514706227264728707 1555227772059340897093061)
                ·
                  refine ⟨291605207261126418204949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555227772059340897093061 291605207261126418204949)
                  ·
                    rfl

theorem cell21_1277773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1277773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277773 prefixEnd_1277773 := by exact prefixLift 1277773
  have htrace : WordTrace (prefixWord ++ tailWord_1277773) baseStart_1277773 baseEnd_1277773 := by
    simpa [prefixWord, tailWord_1277773, baseEnd_1277773] using wordTrace_append hprefix tailTrace_1277773
  have hstable : (prefixWord ++ tailWord_1277773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277773).length < 2 ^ (prefixWord ++ tailWord_1277773).sum := by decide
  have hdescent : baseEnd_1277773 < baseStart_1277773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277877 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1277877 : Nat := 118140960795 + 1277877 * 2 ^ 59
def prefixEnd_1277877 : Nat := 4983230072969 + 3 ^ 40 * 1277877 * 2
def baseEnd_1277877 : Nat := 291628941478045348471403

theorem tailTrace_1277877 : CollatzResearch.WordTrace tailWord_1277877 prefixEnd_1277877 291628941478045348471403 := by
  unfold tailWord_1277877
  simp only [CollatzResearch.WordTrace]
  refine ⟨46608003191477347861415885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31072002127651565240943923 46608003191477347861415885)
  ·
    refine ⟨17478001196804005448030957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46608003191477347861415885 17478001196804005448030957)
    ·
      refine ⟨6554250448801502043011609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17478001196804005448030957 6554250448801502043011609)
      ·
        refine ⟨4915687836601126532258707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6554250448801502043011609 4915687836601126532258707)
        ·
          refine ⟨7373531754901689798388061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915687836601126532258707 7373531754901689798388061)
          ·
            refine ⟨2765074408088133674395523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7373531754901689798388061 2765074408088133674395523)
            ·
              refine ⟨4147611612132200511593285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765074408088133674395523 4147611612132200511593285)
              ·
                refine ⟨777677177274787595923741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4147611612132200511593285 777677177274787595923741)
                ·
                  refine ⟨291628941478045348471403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777677177274787595923741 291628941478045348471403)
                  ·
                    rfl

theorem cell21_1277877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1277877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277877 prefixEnd_1277877 := by exact prefixLift 1277877
  have htrace : WordTrace (prefixWord ++ tailWord_1277877) baseStart_1277877 baseEnd_1277877 := by
    simpa [prefixWord, tailWord_1277877, baseEnd_1277877] using wordTrace_append hprefix tailTrace_1277877
  have hstable : (prefixWord ++ tailWord_1277877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277877).length < 2 ^ (prefixWord ++ tailWord_1277877).sum := by decide
  have hdescent : baseEnd_1277877 < baseStart_1277877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277922 : List Nat := [3, 3, 3, 1, 2, 1, 8]
def baseStart_1277922 : Nat := 118140960795 + 1277922 * 2 ^ 59
def prefixEnd_1277922 : Nat := 4983230072969 + 3 ^ 40 * 1277922 * 2
def baseEnd_1277922 : Nat := 32404356787903918913479

theorem tailTrace_1277922 : CollatzResearch.WordTrace tailWord_1277922 prefixEnd_1277922 32404356787903918913479 := by
  unfold tailWord_1277922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652411119078580136701005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31073096317542880364536013 11652411119078580136701005)
  ·
    refine ⟨4369654169654467551262877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11652411119078580136701005 4369654169654467551262877)
    ·
      refine ⟨1638620313620425331723579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4369654169654467551262877 1638620313620425331723579)
      ·
        refine ⟨2457930470430637997585369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638620313620425331723579 2457930470430637997585369)
        ·
          refine ⟨1843447852822978498189027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457930470430637997585369 1843447852822978498189027)
          ·
            refine ⟨2765171779234467747283541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843447852822978498189027 2765171779234467747283541)
            ·
              refine ⟨32404356787903918913479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2765171779234467747283541 32404356787903918913479)
              ·
                rfl

theorem cell21_1277922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 8].length) (baseStart_1277922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277922 prefixEnd_1277922 := by exact prefixLift 1277922
  have htrace : WordTrace (prefixWord ++ tailWord_1277922) baseStart_1277922 baseEnd_1277922 := by
    simpa [prefixWord, tailWord_1277922, baseEnd_1277922] using wordTrace_append hprefix tailTrace_1277922
  have hstable : (prefixWord ++ tailWord_1277922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277922).length < 2 ^ (prefixWord ++ tailWord_1277922).sum := by decide
  have hdescent : baseEnd_1277922 < baseStart_1277922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277936 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_1277936 : Nat := 118140960795 + 1277936 * 2 ^ 59
def prefixEnd_1277936 : Nat := 4983230072969 + 3 ^ 40 * 1277936 * 2
def baseEnd_1277936 : Nat := 291642406081874356987949

theorem tailTrace_1277936 : CollatzResearch.WordTrace tailWord_1277936 prefixEnd_1277936 291642406081874356987949 := by
  unfold tailWord_1277936
  simp only [CollatzResearch.WordTrace]
  refine ⟨23305077549131800468906831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31073436732175733958542441 23305077549131800468906831)
  ·
    refine ⟨34957616323697700703360247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23305077549131800468906831 34957616323697700703360247)
    ·
      refine ⟨52436424485546551055040371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34957616323697700703360247 52436424485546551055040371)
      ·
        refine ⟨78654636728319826582560557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52436424485546551055040371 78654636728319826582560557)
        ·
          refine ⟨29495488773119934968460209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78654636728319826582560557 29495488773119934968460209)
          ·
            refine ⟨22121616579839951226345157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29495488773119934968460209 22121616579839951226345157)
            ·
              refine ⟨4147803108719990854939717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22121616579839951226345157 4147803108719990854939717)
              ·
                refine ⟨777713082884998285301197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4147803108719990854939717 777713082884998285301197)
                ·
                  refine ⟨291642406081874356987949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777713082884998285301197 291642406081874356987949)
                  ·
                    rfl

theorem cell21_1277936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_1277936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277936 prefixEnd_1277936 := by exact prefixLift 1277936
  have htrace : WordTrace (prefixWord ++ tailWord_1277936) baseStart_1277936 baseEnd_1277936 := by
    simpa [prefixWord, tailWord_1277936, baseEnd_1277936] using wordTrace_append hprefix tailTrace_1277936
  have hstable : (prefixWord ++ tailWord_1277936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277936).length < 2 ^ (prefixWord ++ tailWord_1277936).sum := by decide
  have hdescent : baseEnd_1277936 < baseStart_1277936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277956 : List Nat := [2, 3, 2, 4, 2, 1, 2, 5]
def baseStart_1277956 : Nat := 118140960795 + 1277956 * 2 ^ 59
def prefixEnd_1277956 : Nat := 4983230072969 + 3 ^ 40 * 1277956 * 2
def baseEnd_1277956 : Nat := 97215656784786255551525

theorem tailTrace_1277956 : CollatzResearch.WordTrace tailWord_1277956 prefixEnd_1277956 97215656784786255551525 := by
  unfold tailWord_1277956
  simp only [CollatzResearch.WordTrace]
  refine ⟨23305442279095572176770861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31073923038794096235694481 23305442279095572176770861)
  ·
    refine ⟨8739540854660839566289073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23305442279095572176770861 8739540854660839566289073)
    ·
      refine ⟨6554655640995629674716805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8739540854660839566289073 6554655640995629674716805)
      ·
        refine ⟨1228997932686680564009401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6554655640995629674716805 1228997932686680564009401)
        ·
          refine ⟨921748449515010423007051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1228997932686680564009401 921748449515010423007051)
          ·
            refine ⟨1382622674272515634510577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921748449515010423007051 1382622674272515634510577)
            ·
              refine ⟨1036967005704386725882933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382622674272515634510577 1036967005704386725882933)
              ·
                refine ⟨97215656784786255551525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1036967005704386725882933 97215656784786255551525)
                ·
                  rfl

theorem cell21_1277956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_1277956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277956 prefixEnd_1277956 := by exact prefixLift 1277956
  have htrace : WordTrace (prefixWord ++ tailWord_1277956) baseStart_1277956 baseEnd_1277956 := by
    simpa [prefixWord, tailWord_1277956, baseEnd_1277956] using wordTrace_append hprefix tailTrace_1277956
  have hstable : (prefixWord ++ tailWord_1277956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277956).length < 2 ^ (prefixWord ++ tailWord_1277956).sum := by decide
  have hdescent : baseEnd_1277956 < baseStart_1277956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277964 : List Nat := [2, 2, 1, 2, 3, 1, 3, 7]
def baseStart_1277964 : Nat := 118140960795 + 1277964 * 2 ^ 59
def prefixEnd_1277964 : Nat := 4983230072969 + 3 ^ 40 * 1277964 * 2
def baseEnd_1277964 : Nat := 97216265354450843507075

theorem tailTrace_1277964 : CollatzResearch.WordTrace tailWord_1277964 prefixEnd_1277964 97216265354450843507075 := by
  unfold tailWord_1277964
  simp only [CollatzResearch.WordTrace]
  refine ⟨23305588171081080859916473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31074117561441441146555297 23305588171081080859916473)
  ·
    refine ⟨17479191128310810644937355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23305588171081080859916473 17479191128310810644937355)
    ·
      refine ⟨26218786692466215967406033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17479191128310810644937355 26218786692466215967406033)
      ·
        refine ⟨19664090019349661975554525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26218786692466215967406033 19664090019349661975554525)
        ·
          refine ⟨7374033757256123240832947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19664090019349661975554525 7374033757256123240832947)
          ·
            refine ⟨11061050635884184861249421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7374033757256123240832947 11061050635884184861249421)
            ·
              refine ⟨4147893988456569322968533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11061050635884184861249421 4147893988456569322968533)
              ·
                refine ⟨97216265354450843507075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4147893988456569322968533 97216265354450843507075)
                ·
                  rfl

theorem cell21_1277964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_1277964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277964 prefixEnd_1277964 := by exact prefixLift 1277964
  have htrace : WordTrace (prefixWord ++ tailWord_1277964) baseStart_1277964 baseEnd_1277964 := by
    simpa [prefixWord, tailWord_1277964, baseEnd_1277964] using wordTrace_append hprefix tailTrace_1277964
  have hstable : (prefixWord ++ tailWord_1277964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277964).length < 2 ^ (prefixWord ++ tailWord_1277964).sum := by decide
  have hdescent : baseEnd_1277964 < baseStart_1277964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277981 : List Nat := [1, 4, 2, 2, 2, 3, 7]
def baseStart_1277981 : Nat := 118140960795 + 1277981 * 2 ^ 59
def prefixEnd_1277981 : Nat := 4983230072969 + 3 ^ 40 * 1277981 * 2
def baseEnd_1277981 : Nat := 32405852854996030970873

theorem tailTrace_1277981 : CollatzResearch.WordTrace tailWord_1277981 prefixEnd_1277981 32405852854996030970873 := by
  unfold tailWord_1277981
  simp only [CollatzResearch.WordTrace]
  refine ⟨46611796383100573623201797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31074530922067049082134531 46611796383100573623201797)
  ·
    refine ⟨8739711821831357554350337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46611796383100573623201797 8739711821831357554350337)
    ·
      refine ⟨6554783866373518165762753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8739711821831357554350337 6554783866373518165762753)
      ·
        refine ⟨4916087899780138624322065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6554783866373518165762753 4916087899780138624322065)
        ·
          refine ⟨3687065924835103968241549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4916087899780138624322065 3687065924835103968241549)
          ·
            refine ⟨1382649721813163988090581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3687065924835103968241549 1382649721813163988090581)
            ·
              refine ⟨32405852854996030970873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1382649721813163988090581 32405852854996030970873)
              ·
                rfl

theorem cell21_1277981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 7].length) (baseStart_1277981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1277981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1277981 prefixEnd_1277981 := by exact prefixLift 1277981
  have htrace : WordTrace (prefixWord ++ tailWord_1277981) baseStart_1277981 baseEnd_1277981 := by
    simpa [prefixWord, tailWord_1277981, baseEnd_1277981] using wordTrace_append hprefix tailTrace_1277981
  have hstable : (prefixWord ++ tailWord_1277981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277981).length < 2 ^ (prefixWord ++ tailWord_1277981).sum := by decide
  have hdescent : baseEnd_1277981 < baseStart_1277981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278029 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1278029 : Nat := 118140960795 + 1278029 * 2 ^ 59
def prefixEnd_1278029 : Nat := 4983230072969 + 3 ^ 40 * 1278029 * 2
def baseEnd_1278029 : Nat := 291663629948926861937759

theorem tailTrace_1278029 : CollatzResearch.WordTrace tailWord_1278029 prefixEnd_1278029 291663629948926861937759 := by
  unfold tailWord_1278029
  simp only [CollatzResearch.WordTrace]
  refine ⟨46613547086926677820949141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31075698057951118547299427 46613547086926677820949141)
  ·
    refine ⟨2185010019699688022856991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46613547086926677820949141 2185010019699688022856991)
    ·
      refine ⟨3277515029549532034285487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2185010019699688022856991 3277515029549532034285487)
      ·
        refine ⟨4916272544324298051428231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277515029549532034285487 4916272544324298051428231)
        ·
          refine ⟨7374408816486447077142347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916272544324298051428231 7374408816486447077142347)
          ·
            refine ⟨11061613224729670615713521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7374408816486447077142347 11061613224729670615713521)
            ·
              refine ⟨8296209918547252961785141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11061613224729670615713521 8296209918547252961785141)
              ·
                refine ⟨777769679863804965167357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8296209918547252961785141 777769679863804965167357)
                ·
                  refine ⟨291663629948926861937759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777769679863804965167357 291663629948926861937759)
                  ·
                    rfl

theorem cell21_1278029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1278029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278029 prefixEnd_1278029 := by exact prefixLift 1278029
  have htrace : WordTrace (prefixWord ++ tailWord_1278029) baseStart_1278029 baseEnd_1278029 := by
    simpa [prefixWord, tailWord_1278029, baseEnd_1278029] using wordTrace_append hprefix tailTrace_1278029
  have hstable : (prefixWord ++ tailWord_1278029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278029).length < 2 ^ (prefixWord ++ tailWord_1278029).sum := by decide
  have hdescent : baseEnd_1278029 < baseStart_1278029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278071 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_1278071 : Nat := 118140960795 + 1278071 * 2 ^ 59
def prefixEnd_1278071 : Nat := 4983230072969 + 3 ^ 40 * 1278071 * 2
def baseEnd_1278071 : Nat := 291673214921144122237673

theorem tailTrace_1278071 : CollatzResearch.WordTrace tailWord_1278071 prefixEnd_1278071 291673214921144122237673 := by
  unfold tailWord_1278071
  simp only [CollatzResearch.WordTrace]
  refine ⟨46615078952774518993978067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31076719301849679329318711 46615078952774518993978067)
  ·
    refine ⟨69922618429161778490967101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46615078952774518993978067 69922618429161778490967101)
    ·
      refine ⟨26220981910935666934112663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69922618429161778490967101 26220981910935666934112663)
      ·
        refine ⟨39331472866403500401168995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26220981910935666934112663 39331472866403500401168995)
        ·
          refine ⟨58997209299605250601753493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39331472866403500401168995 58997209299605250601753493)
          ·
            refine ⟨2765494185918996121957195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58997209299605250601753493 2765494185918996121957195)
            ·
              refine ⟨4148241278878494182935793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765494185918996121957195 4148241278878494182935793)
              ·
                refine ⟨3111180959158870637201845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4148241278878494182935793 3111180959158870637201845)
                ·
                  refine ⟨291673214921144122237673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3111180959158870637201845 291673214921144122237673)
                  ·
                    rfl

theorem cell21_1278071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_1278071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278071 prefixEnd_1278071 := by exact prefixLift 1278071
  have htrace : WordTrace (prefixWord ++ tailWord_1278071) baseStart_1278071 baseEnd_1278071 := by
    simpa [prefixWord, tailWord_1278071, baseEnd_1278071] using wordTrace_append hprefix tailTrace_1278071
  have hstable : (prefixWord ++ tailWord_1278071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278071).length < 2 ^ (prefixWord ++ tailWord_1278071).sum := by decide
  have hdescent : baseEnd_1278071 < baseStart_1278071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278161 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_1278161 : Nat := 118140960795 + 1278161 * 2 ^ 59
def prefixEnd_1278161 : Nat := 4983230072969 + 3 ^ 40 * 1278161 * 2
def baseEnd_1278161 : Nat := 291693754147323965737489

theorem tailTrace_1278161 : CollatzResearch.WordTrace tailWord_1278161 prefixEnd_1278161 291693754147323965737489 := by
  unfold tailWord_1278161
  simp only [CollatzResearch.WordTrace]
  refine ⟨46618361522448464364754337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31078907681632309576502891 46618361522448464364754337)
  ·
    refine ⟨34963771141836348273565753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46618361522448464364754337 34963771141836348273565753)
    ·
      refine ⟨26222828356377261205174315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34963771141836348273565753 26222828356377261205174315)
      ·
        refine ⟨39334242534565891807761473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26222828356377261205174315 39334242534565891807761473)
        ·
          refine ⟨29500681900924418855821105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39334242534565891807761473 29500681900924418855821105)
          ·
            refine ⟨22125511425693314141865829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29500681900924418855821105 22125511425693314141865829)
            ·
              refine ⟨4148533392317496401599843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22125511425693314141865829 4148533392317496401599843)
              ·
                refine ⟨6222800088476244602399765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148533392317496401599843 6222800088476244602399765)
                ·
                  refine ⟨291693754147323965737489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6222800088476244602399765 291693754147323965737489)
                  ·
                    rfl

theorem cell21_1278161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_1278161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278161 prefixEnd_1278161 := by exact prefixLift 1278161
  have htrace : WordTrace (prefixWord ++ tailWord_1278161) baseStart_1278161 baseEnd_1278161 := by
    simpa [prefixWord, tailWord_1278161, baseEnd_1278161] using wordTrace_append hprefix tailTrace_1278161
  have hstable : (prefixWord ++ tailWord_1278161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278161).length < 2 ^ (prefixWord ++ tailWord_1278161).sum := by decide
  have hdescent : baseEnd_1278161 < baseStart_1278161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278215 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 3]
def baseStart_1278215 : Nat := 118140960795 + 1278215 * 2 ^ 59
def prefixEnd_1278215 : Nat := 4983230072969 + 3 ^ 40 * 1278215 * 2
def baseEnd_1278215 : Nat := 291706077683031871837379

theorem tailTrace_1278215 : CollatzResearch.WordTrace tailWord_1278215 prefixEnd_1278215 291706077683031871837379 := by
  unfold tailWord_1278215
  simp only [CollatzResearch.WordTrace]
  refine ⟨46620331064252831587220099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31080220709501887724813399 46620331064252831587220099)
  ·
    refine ⟨69930496596379247380830149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46620331064252831587220099 69930496596379247380830149)
    ·
      refine ⟨13111968111821108883905653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69930496596379247380830149 13111968111821108883905653)
      ·
        refine ⟨1229247010483228957866155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13111968111821108883905653 1229247010483228957866155)
        ·
          refine ⟨1843870515724843436799233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229247010483228957866155 1843870515724843436799233)
          ·
            refine ⟨1382902886793632577599425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843870515724843436799233 1382902886793632577599425)
            ·
              refine ⟨1037177165095224433199569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382902886793632577599425 1037177165095224433199569)
              ·
                refine ⟨777882873821418324899677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037177165095224433199569 777882873821418324899677)
                ·
                  refine ⟨291706077683031871837379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777882873821418324899677 291706077683031871837379)
                  ·
                    rfl

theorem cell21_1278215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3].length) (baseStart_1278215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278215 prefixEnd_1278215 := by exact prefixLift 1278215
  have htrace : WordTrace (prefixWord ++ tailWord_1278215) baseStart_1278215 baseEnd_1278215 := by
    simpa [prefixWord, tailWord_1278215, baseEnd_1278215] using wordTrace_append hprefix tailTrace_1278215
  have hstable : (prefixWord ++ tailWord_1278215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278215).length < 2 ^ (prefixWord ++ tailWord_1278215).sum := by decide
  have hdescent : baseEnd_1278215 < baseStart_1278215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278257 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 3]
def baseStart_1278257 : Nat := 118140960795 + 1278257 * 2 ^ 59
def prefixEnd_1278257 : Nat := 4983230072969 + 3 ^ 40 * 1278257 * 2
def baseEnd_1278257 : Nat := 291715662655249132137293

theorem tailTrace_1278257 : CollatzResearch.WordTrace tailWord_1278257 prefixEnd_1278257 291715662655249132137293 := by
  unfold tailWord_1278257
  simp only [CollatzResearch.WordTrace]
  refine ⟨46621862930100672760249025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31081241953400448506832683 46621862930100672760249025)
  ·
    refine ⟨34966397197575504570186769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46621862930100672760249025 34966397197575504570186769)
    ·
      refine ⟨26224797898181628427640077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34966397197575504570186769 26224797898181628427640077)
      ·
        refine ⟨9834299211818110660365029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26224797898181628427640077 9834299211818110660365029)
        ·
          refine ⟨1843931102215895748818443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9834299211818110660365029 1843931102215895748818443)
          ·
            refine ⟨2765896653323843623227665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843931102215895748818443 2765896653323843623227665)
            ·
              refine ⟨2074422489992882717420749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765896653323843623227665 2074422489992882717420749)
              ·
                refine ⟨777908433747331019032781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074422489992882717420749 777908433747331019032781)
                ·
                  refine ⟨291715662655249132137293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777908433747331019032781 291715662655249132137293)
                  ·
                    rfl

theorem cell21_1278257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_1278257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278257 prefixEnd_1278257 := by exact prefixLift 1278257
  have htrace : WordTrace (prefixWord ++ tailWord_1278257) baseStart_1278257 baseEnd_1278257 := by
    simpa [prefixWord, tailWord_1278257, baseEnd_1278257] using wordTrace_append hprefix tailTrace_1278257
  have hstable : (prefixWord ++ tailWord_1278257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278257).length < 2 ^ (prefixWord ++ tailWord_1278257).sum := by decide
  have hdescent : baseEnd_1278257 < baseStart_1278257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278333 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1278333 : Nat := 118140960795 + 1278333 * 2 ^ 59
def prefixEnd_1278333 : Nat := 4983230072969 + 3 ^ 40 * 1278333 * 2
def baseEnd_1278333 : Nat := 291733006890689888870471

theorem tailTrace_1278333 : CollatzResearch.WordTrace tailWord_1278333 prefixEnd_1278333 291733006890689888870471 := by
  unfold tailWord_1278333
  simp only [CollatzResearch.WordTrace]
  refine ⟨46624634877825337740015653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31083089918550225160010435 46624634877825337740015653)
  ·
    refine ⟨8742119039592250826252935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46624634877825337740015653 8742119039592250826252935)
    ·
      refine ⟨13113178559388376239379403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742119039592250826252935 13113178559388376239379403)
      ·
        refine ⟨19669767839082564359069105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13113178559388376239379403 19669767839082564359069105)
        ·
          refine ⟨14752325879311923269301829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19669767839082564359069105 14752325879311923269301829)
          ·
            refine ⟨2766061102370985612994093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14752325879311923269301829 2766061102370985612994093)
            ·
              refine ⟨1037272913389119604872785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2766061102370985612994093 1037272913389119604872785)
              ·
                refine ⟨777954685041839703654589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037272913389119604872785 777954685041839703654589)
                ·
                  refine ⟨291733006890689888870471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777954685041839703654589 291733006890689888870471)
                  ·
                    rfl

theorem cell21_1278333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1278333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278333 prefixEnd_1278333 := by exact prefixLift 1278333
  have htrace : WordTrace (prefixWord ++ tailWord_1278333) baseStart_1278333 baseEnd_1278333 := by
    simpa [prefixWord, tailWord_1278333, baseEnd_1278333] using wordTrace_append hprefix tailTrace_1278333
  have hstable : (prefixWord ++ tailWord_1278333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278333).length < 2 ^ (prefixWord ++ tailWord_1278333).sum := by decide
  have hdescent : baseEnd_1278333 < baseStart_1278333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278344 : List Nat := [2, 1, 3, 3, 1, 1, 4, 6]
def baseStart_1278344 : Nat := 118140960795 + 1278344 * 2 ^ 59
def prefixEnd_1278344 : Nat := 4983230072969 + 3 ^ 40 * 1278344 * 2
def baseEnd_1278344 : Nat := 97245172413518771395705

theorem tailTrace_1278344 : CollatzResearch.WordTrace tailWord_1278344 prefixEnd_1278344 97245172413518771395705 := by
  unfold tailWord_1278344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23312518040392743309333043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31083357387190324412444057 23312518040392743309333043)
  ·
    refine ⟨34968777060589114963999565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23312518040392743309333043 34968777060589114963999565)
    ·
      refine ⟨13113291397720918111499837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34968777060589114963999565 13113291397720918111499837)
      ·
        refine ⟨4917484274145344291812439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13113291397720918111499837 4917484274145344291812439)
        ·
          refine ⟨7376226411218016437718659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917484274145344291812439 7376226411218016437718659)
          ·
            refine ⟨11064339616827024656577989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7376226411218016437718659 11064339616827024656577989)
            ·
              refine ⟨2074563678155067123108373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11064339616827024656577989 2074563678155067123108373)
              ·
                refine ⟨97245172413518771395705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2074563678155067123108373 97245172413518771395705)
                ·
                  rfl

theorem cell21_1278344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_1278344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278344 prefixEnd_1278344 := by exact prefixLift 1278344
  have htrace : WordTrace (prefixWord ++ tailWord_1278344) baseStart_1278344 baseEnd_1278344 := by
    simpa [prefixWord, tailWord_1278344, baseEnd_1278344] using wordTrace_append hprefix tailTrace_1278344
  have hstable : (prefixWord ++ tailWord_1278344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278344).length < 2 ^ (prefixWord ++ tailWord_1278344).sum := by decide
  have hdescent : baseEnd_1278344 < baseStart_1278344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278347 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 4]
def baseStart_1278347 : Nat := 118140960795 + 1278347 * 2 ^ 59
def prefixEnd_1278347 : Nat := 4983230072969 + 3 ^ 40 * 1278347 * 2
def baseEnd_1278347 : Nat := 291736201881428975637109

theorem tailTrace_1278347 : CollatzResearch.WordTrace tailWord_1278347 prefixEnd_1278347 291736201881428975637109 := by
  unfold tailWord_1278347
  simp only [CollatzResearch.WordTrace]
  refine ⟨46625145499774618131025295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31083430333183078754016863 46625145499774618131025295)
  ·
    refine ⟨69937718249661927196537943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46625145499774618131025295 69937718249661927196537943)
    ·
      refine ⟨104906577374492890794806915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69937718249661927196537943 104906577374492890794806915)
      ·
        refine ⟨157359866061739336192210373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104906577374492890794806915 157359866061739336192210373)
        ·
          refine ⟨29504974886576125536039445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157359866061739336192210373 29504974886576125536039445)
          ·
            refine ⟨1383045697808255884501849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29504974886576125536039445 1383045697808255884501849)
            ·
              refine ⟨1037284273356191913376387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383045697808255884501849 1037284273356191913376387)
              ·
                refine ⟨1555926410034287870064581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037284273356191913376387 1555926410034287870064581)
                ·
                  refine ⟨291736201881428975637109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555926410034287870064581 291736201881428975637109)
                  ·
                    rfl

theorem cell21_1278347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4].length) (baseStart_1278347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278347 prefixEnd_1278347 := by exact prefixLift 1278347
  have htrace : WordTrace (prefixWord ++ tailWord_1278347) baseStart_1278347 baseEnd_1278347 := by
    simpa [prefixWord, tailWord_1278347, baseEnd_1278347] using wordTrace_append hprefix tailTrace_1278347
  have hstable : (prefixWord ++ tailWord_1278347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278347).length < 2 ^ (prefixWord ++ tailWord_1278347).sum := by decide
  have hdescent : baseEnd_1278347 < baseStart_1278347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278378 : List Nat := [3, 1, 6, 1, 1, 9]
def baseStart_1278378 : Nat := 118140960795 + 1278378 * 2 ^ 59
def prefixEnd_1278378 : Nat := 4983230072969 + 3 ^ 40 * 1278378 * 2
def baseEnd_1278378 : Nat := 10805306537177030022977

theorem tailTrace_1278378 : CollatzResearch.WordTrace tailWord_1278378 prefixEnd_1278378 10805306537177030022977 := by
  unfold tailWord_1278378
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656569040665577606350947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31084184108441540283602525 11656569040665577606350947)
  ·
    refine ⟨17484853560998366409526421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11656569040665577606350947 17484853560998366409526421)
    ·
      refine ⟨819602510671798425446551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17484853560998366409526421 819602510671798425446551)
      ·
        refine ⟨1229403766007697638169827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819602510671798425446551 1229403766007697638169827)
        ·
          refine ⟨1844105649011546457254741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229403766007697638169827 1844105649011546457254741)
          ·
            refine ⟨10805306537177030022977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1844105649011546457254741 10805306537177030022977)
            ·
              rfl

theorem cell21_1278378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 9].length) (baseStart_1278378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278378 prefixEnd_1278378 := by exact prefixLift 1278378
  have htrace : WordTrace (prefixWord ++ tailWord_1278378) baseStart_1278378 baseEnd_1278378 := by
    simpa [prefixWord, tailWord_1278378, baseEnd_1278378] using wordTrace_append hprefix tailTrace_1278378
  have hstable : (prefixWord ++ tailWord_1278378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278378).length < 2 ^ (prefixWord ++ tailWord_1278378).sum := by decide
  have hdescent : baseEnd_1278378 < baseStart_1278378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278451 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 3]
def baseStart_1278451 : Nat := 118140960795 + 1278451 * 2 ^ 59
def prefixEnd_1278451 : Nat := 4983230072969 + 3 ^ 40 * 1278451 * 2
def baseEnd_1278451 : Nat := 291759936098347905903563

theorem tailTrace_1278451 : CollatzResearch.WordTrace tailWord_1278451 prefixEnd_1278451 291759936098347905903563 := by
  unfold tailWord_1278451
  simp only [CollatzResearch.WordTrace]
  refine ⟨46628938691397843892811207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31085959127598562595207471 46628938691397843892811207)
  ·
    refine ⟨69943408037096765839216811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46628938691397843892811207 69943408037096765839216811)
    ·
      refine ⟨104915112055645148758825217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69943408037096765839216811 104915112055645148758825217)
      ·
        refine ⟨78686334041733861569118913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104915112055645148758825217 78686334041733861569118913)
        ·
          refine ⟨59014750531300396176839185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78686334041733861569118913 59014750531300396176839185)
          ·
            refine ⟨44261062898475297132629389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59014750531300396176839185 44261062898475297132629389)
            ·
              refine ⟨16597898586928236424736021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44261062898475297132629389 16597898586928236424736021)
              ·
                refine ⟨778026496262261082409501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16597898586928236424736021 778026496262261082409501)
                ·
                  refine ⟨291759936098347905903563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778026496262261082409501 291759936098347905903563)
                  ·
                    rfl

theorem cell21_1278451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3].length) (baseStart_1278451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278451 prefixEnd_1278451 := by exact prefixLift 1278451
  have htrace : WordTrace (prefixWord ++ tailWord_1278451) baseStart_1278451 baseEnd_1278451 := by
    simpa [prefixWord, tailWord_1278451, baseEnd_1278451] using wordTrace_append hprefix tailTrace_1278451
  have hstable : (prefixWord ++ tailWord_1278451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278451).length < 2 ^ (prefixWord ++ tailWord_1278451).sum := by decide
  have hdescent : baseEnd_1278451 < baseStart_1278451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278516 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1278516 : Nat := 118140960795 + 1278516 * 2 ^ 59
def prefixEnd_1278516 : Nat := 4983230072969 + 3 ^ 40 * 1278516 * 2
def baseEnd_1278516 : Nat := 291774769983922237320097

theorem tailTrace_1278516 : CollatzResearch.WordTrace tailWord_1278516 prefixEnd_1278516 291774769983922237320097 := by
  unfold tailWord_1278516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315654718081179996963701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31087539624108239995951601 23315654718081179996963701)
  ·
    refine ⟨2185842629820110624715347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23315654718081179996963701 2185842629820110624715347)
    ·
      refine ⟨3278763944730165937073021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2185842629820110624715347 3278763944730165937073021)
      ·
        refine ⟨1229536479273812226402383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3278763944730165937073021 1229536479273812226402383)
        ·
          refine ⟨1844304718910718339603575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229536479273812226402383 1844304718910718339603575)
          ·
            refine ⟨2766457078366077509405363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844304718910718339603575 2766457078366077509405363)
            ·
              refine ⟨4149685617549116264108045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766457078366077509405363 4149685617549116264108045)
              ·
                refine ⟨1556132106580918599040517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4149685617549116264108045 1556132106580918599040517)
                ·
                  refine ⟨291774769983922237320097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556132106580918599040517 291774769983922237320097)
                  ·
                    rfl

theorem cell21_1278516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1278516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278516 prefixEnd_1278516 := by exact prefixLift 1278516
  have htrace : WordTrace (prefixWord ++ tailWord_1278516) baseStart_1278516 baseEnd_1278516 := by
    simpa [prefixWord, tailWord_1278516, baseEnd_1278516] using wordTrace_append hprefix tailTrace_1278516
  have hstable : (prefixWord ++ tailWord_1278516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278516).length < 2 ^ (prefixWord ++ tailWord_1278516).sum := by decide
  have hdescent : baseEnd_1278516 < baseStart_1278516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278561 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 3]
def baseStart_1278561 : Nat := 118140960795 + 1278561 * 2 ^ 59
def prefixEnd_1278561 : Nat := 4983230072969 + 3 ^ 40 * 1278561 * 2
def baseEnd_1278561 : Nat := 291785039597012159070005

theorem tailTrace_1278561 : CollatzResearch.WordTrace tailWord_1278561 prefixEnd_1278561 291785039597012159070005 := by
  unfold tailWord_1278561
  simp only [CollatzResearch.WordTrace]
  refine ⟨46632950720999332679315537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31088633813999555119543691 46632950720999332679315537)
  ·
    refine ⟨34974713040749499509486653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46632950720999332679315537 34974713040749499509486653)
    ·
      refine ⟨13115517390281062316057495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34974713040749499509486653 13115517390281062316057495)
      ·
        refine ⟨19673276085421593474086243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115517390281062316057495 19673276085421593474086243)
        ·
          refine ⟨29509914128132390211129365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19673276085421593474086243 29509914128132390211129365)
          ·
            refine ⟨1383277224756205791146689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29509914128132390211129365 1383277224756205791146689)
            ·
              refine ⟨1037457918567154343360017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383277224756205791146689 1037457918567154343360017)
              ·
                refine ⟨778093438925365757520013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037457918567154343360017 778093438925365757520013)
                ·
                  refine ⟨291785039597012159070005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778093438925365757520013 291785039597012159070005)
                  ·
                    rfl

theorem cell21_1278561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_1278561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278561 prefixEnd_1278561 := by exact prefixLift 1278561
  have htrace : WordTrace (prefixWord ++ tailWord_1278561) baseStart_1278561 baseEnd_1278561 := by
    simpa [prefixWord, tailWord_1278561, baseEnd_1278561] using wordTrace_append hprefix tailTrace_1278561
  have hstable : (prefixWord ++ tailWord_1278561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278561).length < 2 ^ (prefixWord ++ tailWord_1278561).sum := by decide
  have hdescent : baseEnd_1278561 < baseStart_1278561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278589 : List Nat := [1, 4, 1, 1, 5, 1, 3, 5]
def baseStart_1278589 : Nat := 118140960795 + 1278589 * 2 ^ 59
def prefixEnd_1278589 : Nat := 4983230072969 + 3 ^ 40 * 1278589 * 2
def baseEnd_1278589 : Nat := 97263809859496777534427

theorem tailTrace_1278589 : CollatzResearch.WordTrace tailWord_1278589 prefixEnd_1278589 97263809859496777534427 := by
  unfold tailWord_1278589
  simp only [CollatzResearch.WordTrace]
  refine ⟨46633971964897893461334821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31089314643265262307556547 46633971964897893461334821)
  ·
    refine ⟨8743869743418355024000279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46633971964897893461334821 8743869743418355024000279)
    ·
      refine ⟨13115804615127532536000419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743869743418355024000279 13115804615127532536000419)
      ·
        refine ⟨19673706922691298804000629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115804615127532536000419 19673706922691298804000629)
        ·
          refine ⟨1844410024002309262875059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19673706922691298804000629 1844410024002309262875059)
          ·
            refine ⟨2766615036003463894312589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844410024002309262875059 2766615036003463894312589)
            ·
              refine ⟨1037480638501298960367221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2766615036003463894312589 1037480638501298960367221)
              ·
                refine ⟨97263809859496777534427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1037480638501298960367221 97263809859496777534427)
                ·
                  rfl

theorem cell21_1278589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 5].length) (baseStart_1278589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278589 prefixEnd_1278589 := by exact prefixLift 1278589
  have htrace : WordTrace (prefixWord ++ tailWord_1278589) baseStart_1278589 baseEnd_1278589 := by
    simpa [prefixWord, tailWord_1278589, baseEnd_1278589] using wordTrace_append hprefix tailTrace_1278589
  have hstable : (prefixWord ++ tailWord_1278589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278589).length < 2 ^ (prefixWord ++ tailWord_1278589).sum := by decide
  have hdescent : baseEnd_1278589 < baseStart_1278589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278620 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_1278620 : Nat := 118140960795 + 1278620 * 2 ^ 59
def prefixEnd_1278620 : Nat := 4983230072969 + 3 ^ 40 * 1278620 * 2
def baseEnd_1278620 : Nat := 291798504200841167586551

theorem tailTrace_1278620 : CollatzResearch.WordTrace tailWord_1278620 prefixEnd_1278620 291798504200841167586551 := by
  unfold tailWord_1278620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317551313892792877856657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31090068418523723837142209 23317551313892792877856657)
  ·
    refine ⟨17488163485419594658392493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23317551313892792877856657 17488163485419594658392493)
    ·
      refine ⟨6558061307032347996897185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17488163485419594658392493 6558061307032347996897185)
      ·
        refine ⟨4918545980274260997672889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6558061307032347996897185 4918545980274260997672889)
        ·
          refine ⟨3688909485205695748254667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4918545980274260997672889 3688909485205695748254667)
          ·
            refine ⟨5533364227808543622382001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688909485205695748254667 5533364227808543622382001)
            ·
              refine ⟨4150023170856407716786501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5533364227808543622382001 4150023170856407716786501)
              ·
                refine ⟨778129344535576446897469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4150023170856407716786501 778129344535576446897469)
                ·
                  refine ⟨291798504200841167586551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778129344535576446897469 291798504200841167586551)
                  ·
                    rfl

theorem cell21_1278620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_1278620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278620 prefixEnd_1278620 := by exact prefixLift 1278620
  have htrace : WordTrace (prefixWord ++ tailWord_1278620) baseStart_1278620 baseEnd_1278620 := by
    simpa [prefixWord, tailWord_1278620, baseEnd_1278620] using wordTrace_append hprefix tailTrace_1278620
  have hstable : (prefixWord ++ tailWord_1278620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278620).length < 2 ^ (prefixWord ++ tailWord_1278620).sum := by decide
  have hdescent : baseEnd_1278620 < baseStart_1278620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278679 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 5]
def baseStart_1278679 : Nat := 118140960795 + 1278679 * 2 ^ 59
def prefixEnd_1278679 : Nat := 4983230072969 + 3 ^ 40 * 1278679 * 2
def baseEnd_1278679 : Nat := 291811968804670176103097

theorem tailTrace_1278679 : CollatzResearch.WordTrace tailWord_1278679 prefixEnd_1278679 291811968804670176103097 := by
  unfold tailWord_1278679
  simp only [CollatzResearch.WordTrace]
  refine ⟨46637254534571838832111091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31091503023047892554740727 46637254534571838832111091)
  ·
    refine ⟨69955881801857758248166637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46637254534571838832111091 69955881801857758248166637)
    ·
      refine ⟨26233455675696659343062489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69955881801857758248166637 26233455675696659343062489)
      ·
        refine ⟨19675091756772494507296867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26233455675696659343062489 19675091756772494507296867)
        ·
          refine ⟨29512637635158741760945301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19675091756772494507296867 29512637635158741760945301)
          ·
            refine ⟨1383404889148066020044311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29512637635158741760945301 1383404889148066020044311)
            ·
              refine ⟨2075107333722099030066467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383404889148066020044311 2075107333722099030066467)
              ·
                refine ⟨3112661000583148545099701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075107333722099030066467 3112661000583148545099701)
                ·
                  refine ⟨291811968804670176103097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3112661000583148545099701 291811968804670176103097)
                  ·
                    rfl

theorem cell21_1278679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_1278679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278679 prefixEnd_1278679 := by exact prefixLift 1278679
  have htrace : WordTrace (prefixWord ++ tailWord_1278679) baseStart_1278679 baseEnd_1278679 := by
    simpa [prefixWord, tailWord_1278679, baseEnd_1278679] using wordTrace_append hprefix tailTrace_1278679
  have hstable : (prefixWord ++ tailWord_1278679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278679).length < 2 ^ (prefixWord ++ tailWord_1278679).sum := by decide
  have hdescent : baseEnd_1278679 < baseStart_1278679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278783 : List Nat := [1, 1, 2, 2, 5, 2, 8]
def baseStart_1278783 : Nat := 118140960795 + 1278783 * 2 ^ 59
def prefixEnd_1278783 : Nat := 4983230072969 + 3 ^ 40 * 1278783 * 2
def baseEnd_1278783 : Nat := 32426189224621011818839

theorem tailTrace_1278783 : CollatzResearch.WordTrace tailWord_1278783 prefixEnd_1278783 32426189224621011818839 := by
  unfold tailWord_1278783
  simp only [CollatzResearch.WordTrace]
  refine ⟨46641047726195064593897003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31094031817463376395931335 46641047726195064593897003)
  ·
    refine ⟨69961571589292596890845505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46641047726195064593897003 69961571589292596890845505)
    ·
      refine ⟨52471178691969447668134129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69961571589292596890845505 52471178691969447668134129)
      ·
        refine ⟨39353384018977085751100597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52471178691969447668134129 39353384018977085751100597)
        ·
          refine ⟨3689379751779101789165681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39353384018977085751100597 3689379751779101789165681)
          ·
            refine ⟨2767034813834326341874261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3689379751779101789165681 2767034813834326341874261)
            ·
              refine ⟨32426189224621011818839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2767034813834326341874261 32426189224621011818839)
              ·
                rfl

theorem cell21_1278783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 8].length) (baseStart_1278783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278783 prefixEnd_1278783 := by exact prefixLift 1278783
  have htrace : WordTrace (prefixWord ++ tailWord_1278783) baseStart_1278783 baseEnd_1278783 := by
    simpa [prefixWord, tailWord_1278783, baseEnd_1278783] using wordTrace_append hprefix tailTrace_1278783
  have hstable : (prefixWord ++ tailWord_1278783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278783).length < 2 ^ (prefixWord ++ tailWord_1278783).sum := by decide
  have hdescent : baseEnd_1278783 < baseStart_1278783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278828 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1278828 : Nat := 118140960795 + 1278828 * 2 ^ 59
def prefixEnd_1278828 : Nat := 4983230072969 + 3 ^ 40 * 1278828 * 2
def baseEnd_1278828 : Nat := 291845972634679028119459

theorem tailTrace_1278828 : CollatzResearch.WordTrace tailWord_1278828 prefixEnd_1278828 291845972634679028119459 := by
  unfold tailWord_1278828
  simp only [CollatzResearch.WordTrace]
  refine ⟨23321344505516018639642569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31095126007354691519523425 23321344505516018639642569)
  ·
    refine ⟨17491008379137013979731927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23321344505516018639642569 17491008379137013979731927)
    ·
      refine ⟨26236512568705520969597891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17491008379137013979731927 26236512568705520969597891)
      ·
        refine ⟨39354768853058281454396837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26236512568705520969597891 39354768853058281454396837)
        ·
          refine ⟨7379019159948427772699407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39354768853058281454396837 7379019159948427772699407)
          ·
            refine ⟨11068528739922641659049111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379019159948427772699407 11068528739922641659049111)
            ·
              refine ⟨16602793109883962488573667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068528739922641659049111 16602793109883962488573667)
              ·
                refine ⟨24904189664825943732860501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16602793109883962488573667 24904189664825943732860501)
                ·
                  refine ⟨291845972634679028119459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24904189664825943732860501 291845972634679028119459)
                  ·
                    rfl

theorem cell21_1278828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1278828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278828 prefixEnd_1278828 := by exact prefixLift 1278828
  have htrace : WordTrace (prefixWord ++ tailWord_1278828) baseStart_1278828 baseEnd_1278828 := by
    simpa [prefixWord, tailWord_1278828, baseEnd_1278828] using wordTrace_append hprefix tailTrace_1278828
  have hstable : (prefixWord ++ tailWord_1278828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278828).length < 2 ^ (prefixWord ++ tailWord_1278828).sum := by decide
  have hdescent : baseEnd_1278828 < baseStart_1278828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278873 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_1278873 : Nat := 118140960795 + 1278873 * 2 ^ 59
def prefixEnd_1278873 : Nat := 4983230072969 + 3 ^ 40 * 1278873 * 2
def baseEnd_1278873 : Nat := 291856242247768949869367

theorem tailTrace_1278873 : CollatzResearch.WordTrace tailWord_1278873 prefixEnd_1278873 291856242247768949869367 := by
  unfold tailWord_1278873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46644330295869009964673273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31096220197246006643115515 46644330295869009964673273)
  ·
    refine ⟨34983247721901757473504955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46644330295869009964673273 34983247721901757473504955)
    ·
      refine ⟨52474871582852636210257433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34983247721901757473504955 52474871582852636210257433)
      ·
        refine ⟨39356153687139477157693075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52474871582852636210257433 39356153687139477157693075)
        ·
          refine ⟨59034230530709215736539613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39356153687139477157693075 59034230530709215736539613)
          ·
            refine ⟨22137836449015955901202355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59034230530709215736539613 22137836449015955901202355)
            ·
              refine ⟨33206754673523933851803533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22137836449015955901202355 33206754673523933851803533)
              ·
                refine ⟨12452533002571475194426325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33206754673523933851803533 12452533002571475194426325)
                ·
                  refine ⟨291856242247768949869367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12452533002571475194426325 291856242247768949869367)
                  ·
                    rfl

theorem cell21_1278873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_1278873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278873 prefixEnd_1278873 := by exact prefixLift 1278873
  have htrace : WordTrace (prefixWord ++ tailWord_1278873) baseStart_1278873 baseEnd_1278873 := by
    simpa [prefixWord, tailWord_1278873, baseEnd_1278873] using wordTrace_append hprefix tailTrace_1278873
  have hstable : (prefixWord ++ tailWord_1278873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278873).length < 2 ^ (prefixWord ++ tailWord_1278873).sum := by decide
  have hdescent : baseEnd_1278873 < baseStart_1278873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278893 : List Nat := [1, 5, 2, 3, 2, 8]
def baseStart_1278893 : Nat := 118140960795 + 1278893 * 2 ^ 59
def prefixEnd_1278893 : Nat := 4983230072969 + 3 ^ 40 * 1278893 * 2
def baseEnd_1278893 : Nat := 10809659500750124427259

theorem tailTrace_1278893 : CollatzResearch.WordTrace tailWord_1278893 prefixEnd_1278893 10809659500750124427259 := by
  unfold tailWord_1278893
  simp only [CollatzResearch.WordTrace]
  refine ⟨46645059755796553380401333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31096706503864368920267555 46645059755796553380401333)
  ·
    refine ⟨4372974352105926879412625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46645059755796553380401333 4372974352105926879412625)
    ·
      refine ⟨3279730764079445159559469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4372974352105926879412625 3279730764079445159559469)
      ·
        refine ⟨1229899036529791934834801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3279730764079445159559469 1229899036529791934834801)
        ·
          refine ⟨922424277397343951126101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229899036529791934834801 922424277397343951126101)
          ·
            refine ⟨10809659500750124427259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 922424277397343951126101 10809659500750124427259)
            ·
              rfl

theorem cell21_1278893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 8].length) (baseStart_1278893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1278893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1278893 prefixEnd_1278893 := by exact prefixLift 1278893
  have htrace : WordTrace (prefixWord ++ tailWord_1278893) baseStart_1278893 baseEnd_1278893 := by
    simpa [prefixWord, tailWord_1278893, baseEnd_1278893] using wordTrace_append hprefix tailTrace_1278893
  have hstable : (prefixWord ++ tailWord_1278893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278893).length < 2 ^ (prefixWord ++ tailWord_1278893).sum := by decide
  have hdescent : baseEnd_1278893 < baseStart_1278893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279000 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_1279000 : Nat := 118140960795 + 1279000 * 2 ^ 59
def prefixEnd_1279000 : Nat := 4983230072969 + 3 ^ 40 * 1279000 * 2
def baseEnd_1279000 : Nat := 291885225378044951252441

theorem tailTrace_1279000 : CollatzResearch.WordTrace tailWord_1279000 prefixEnd_1279000 291885225378044951252441 := by
  unfold tailWord_1279000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23324481183204455327273227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31099308244272607103030969 23324481183204455327273227)
  ·
    refine ⟨34986721774806682990909841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23324481183204455327273227 34986721774806682990909841)
    ·
      refine ⟨26240041331105012243182381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34986721774806682990909841 26240041331105012243182381)
      ·
        refine ⟨9840015499164379591193393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26240041331105012243182381 9840015499164379591193393)
        ·
          refine ⟨7380011624373284693395045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9840015499164379591193393 7380011624373284693395045)
          ·
            refine ⟨1383752179569990880011571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7380011624373284693395045 1383752179569990880011571)
            ·
              refine ⟨2075628269354986320017357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383752179569990880011571 2075628269354986320017357)
              ·
                refine ⟨778360601008119870006509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2075628269354986320017357 778360601008119870006509)
                ·
                  refine ⟨291885225378044951252441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778360601008119870006509 291885225378044951252441)
                  ·
                    rfl

theorem cell21_1279000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_1279000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279000 prefixEnd_1279000 := by exact prefixLift 1279000
  have htrace : WordTrace (prefixWord ++ tailWord_1279000) baseStart_1279000 baseEnd_1279000 := by
    simpa [prefixWord, tailWord_1279000, baseEnd_1279000] using wordTrace_append hprefix tailTrace_1279000
  have hstable : (prefixWord ++ tailWord_1279000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279000).length < 2 ^ (prefixWord ++ tailWord_1279000).sum := by decide
  have hdescent : baseEnd_1279000 < baseStart_1279000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279011 : List Nat := [1, 1, 1, 4, 3, 4, 7]
def baseStart_1279011 : Nat := 118140960795 + 1279011 * 2 ^ 59
def prefixEnd_1279011 : Nat := 4983230072969 + 3 ^ 40 * 1279011 * 2
def baseEnd_1279011 : Nat := 32431970636434597396565

theorem tailTrace_1279011 : CollatzResearch.WordTrace tailWord_1279011 prefixEnd_1279011 32431970636434597396565 := by
  unfold tailWord_1279011
  simp only [CollatzResearch.WordTrace]
  refine ⟨46649363569369059533196887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31099575712912706355464591 46649363569369059533196887)
  ·
    refine ⟨69974045354053589299795331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46649363569369059533196887 69974045354053589299795331)
    ·
      refine ⟨104961068031080383949692997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69974045354053589299795331 104961068031080383949692997)
      ·
        refine ⟨19680200255827571990567437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104961068031080383949692997 19680200255827571990567437)
        ·
          refine ⟨7380075095935339496462789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19680200255827571990567437 7380075095935339496462789)
          ·
            refine ⟨1383764080487876155586773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7380075095935339496462789 1383764080487876155586773)
            ·
              refine ⟨32431970636434597396565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1383764080487876155586773 32431970636434597396565)
              ·
                rfl

theorem cell21_1279011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 7].length) (baseStart_1279011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279011 prefixEnd_1279011 := by exact prefixLift 1279011
  have htrace : WordTrace (prefixWord ++ tailWord_1279011) baseStart_1279011 baseEnd_1279011 := by
    simpa [prefixWord, tailWord_1279011, baseEnd_1279011] using wordTrace_append hprefix tailTrace_1279011
  have hstable : (prefixWord ++ tailWord_1279011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279011).length < 2 ^ (prefixWord ++ tailWord_1279011).sum := by decide
  have hdescent : baseEnd_1279011 < baseStart_1279011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279028 : List Nat := [2, 5, 1, 2, 1, 1, 1, 8]
def baseStart_1279028 : Nat := 118140960795 + 1279028 * 2 ^ 59
def prefixEnd_1279028 : Nat := 4983230072969 + 3 ^ 40 * 1279028 * 2
def baseEnd_1279028 : Nat := 97297205119841041595239

theorem tailTrace_1279028 : CollatzResearch.WordTrace tailWord_1279028 prefixEnd_1279028 97297205119841041595239 := by
  unfold tailWord_1279028
  simp only [CollatzResearch.WordTrace]
  refine ⟨23324991805153735718282869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31099989073538314291043825 23324991805153735718282869)
  ·
    refine ⟨2186717981733162723589019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23324991805153735718282869 2186717981733162723589019)
    ·
      refine ⟨3280076972599744085383529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2186717981733162723589019 3280076972599744085383529)
      ·
        refine ⟨2460057729449808064037647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3280076972599744085383529 2460057729449808064037647)
        ·
          refine ⟨3690086594174712096056471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460057729449808064037647 3690086594174712096056471)
          ·
            refine ⟨5535129891262068144084707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690086594174712096056471 5535129891262068144084707)
            ·
              refine ⟨8302694836893102216127061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535129891262068144084707 8302694836893102216127061)
              ·
                refine ⟨97297205119841041595239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8302694836893102216127061 97297205119841041595239)
                ·
                  rfl

theorem cell21_1279028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_1279028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279028 prefixEnd_1279028 := by exact prefixLift 1279028
  have htrace : WordTrace (prefixWord ++ tailWord_1279028) baseStart_1279028 baseEnd_1279028 := by
    simpa [prefixWord, tailWord_1279028, baseEnd_1279028] using wordTrace_append hprefix tailTrace_1279028
  have hstable : (prefixWord ++ tailWord_1279028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279028).length < 2 ^ (prefixWord ++ tailWord_1279028).sum := by decide
  have hdescent : baseEnd_1279028 < baseStart_1279028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279135 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_1279135 : Nat := 118140960795 + 1279135 * 2 ^ 59
def prefixEnd_1279135 : Nat := 4983230072969 + 3 ^ 40 * 1279135 * 2
def baseEnd_1279135 : Nat := 291916034217314716502165

theorem tailTrace_1279135 : CollatzResearch.WordTrace tailWord_1279135 prefixEnd_1279135 291916034217314716502165 := by
  unfold tailWord_1279135
  simp only [CollatzResearch.WordTrace]
  refine ⟨46653886220919828710710859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31102590813946552473807239 46653886220919828710710859)
  ·
    refine ⟨69980829331379743066066289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46653886220919828710710859 69980829331379743066066289)
    ·
      refine ⟨52485621998534807299549717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69980829331379743066066289 52485621998534807299549717)
      ·
        refine ⟨2460263531181319092166393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52485621998534807299549717 2460263531181319092166393)
        ·
          refine ⟨1845197648385989319124795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460263531181319092166393 1845197648385989319124795)
          ·
            refine ⟨2767796472578983978687193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845197648385989319124795 2767796472578983978687193)
            ·
              refine ⟨2075847354434237984015395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767796472578983978687193 2075847354434237984015395)
              ·
                refine ⟨3113771031651356976023093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075847354434237984015395 3113771031651356976023093)
                ·
                  refine ⟨291916034217314716502165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3113771031651356976023093 291916034217314716502165)
                  ·
                    rfl

theorem cell21_1279135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_1279135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279135 prefixEnd_1279135 := by exact prefixLift 1279135
  have htrace : WordTrace (prefixWord ++ tailWord_1279135) baseStart_1279135 baseEnd_1279135 := by
    simpa [prefixWord, tailWord_1279135, baseEnd_1279135] using wordTrace_append hprefix tailTrace_1279135
  have hstable : (prefixWord ++ tailWord_1279135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279135).length < 2 ^ (prefixWord ++ tailWord_1279135).sum := by decide
  have hdescent : baseEnd_1279135 < baseStart_1279135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279169 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 3]
def baseStart_1279169 : Nat := 118140960795 + 1279169 * 2 ^ 59
def prefixEnd_1279169 : Nat := 4983230072969 + 3 ^ 40 * 1279169 * 2
def baseEnd_1279169 : Nat := 291923793480538212935429

theorem tailTrace_1279169 : CollatzResearch.WordTrace tailWord_1279169 prefixEnd_1279169 291923793480538212935429 := by
  unfold tailWord_1279169
  simp only [CollatzResearch.WordTrace]
  refine ⟨46655126302796652517448561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31103417535197768344965707 46655126302796652517448561)
  ·
    refine ⟨34991344727097489388086421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46655126302796652517448561 34991344727097489388086421)
    ·
      refine ⟨1640219284082694815066551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34991344727097489388086421 1640219284082694815066551)
      ·
        refine ⟨2460328926124042222599827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640219284082694815066551 2460328926124042222599827)
        ·
          refine ⟨3690493389186063333899741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460328926124042222599827 3690493389186063333899741)
          ·
            refine ⟨1383935020944773750212403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3690493389186063333899741 1383935020944773750212403)
            ·
              refine ⟨2075902531417160625318605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383935020944773750212403 2075902531417160625318605)
              ·
                refine ⟨778463449281435234494477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2075902531417160625318605 778463449281435234494477)
                ·
                  refine ⟨291923793480538212935429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778463449281435234494477 291923793480538212935429)
                  ·
                    rfl

theorem cell21_1279169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_1279169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279169 prefixEnd_1279169 := by exact prefixLift 1279169
  have htrace : WordTrace (prefixWord ++ tailWord_1279169) baseStart_1279169 baseEnd_1279169 := by
    simpa [prefixWord, tailWord_1279169, baseEnd_1279169] using wordTrace_append hprefix tailTrace_1279169
  have hstable : (prefixWord ++ tailWord_1279169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279169).length < 2 ^ (prefixWord ++ tailWord_1279169).sum := by decide
  have hdescent : baseEnd_1279169 < baseStart_1279169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279253 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_1279253 : Nat := 118140960795 + 1279253 * 2 ^ 59
def prefixEnd_1279253 : Nat := 4983230072969 + 3 ^ 40 * 1279253 * 2
def baseEnd_1279253 : Nat := 291942963424972733535257

theorem tailTrace_1279253 : CollatzResearch.WordTrace tailWord_1279253 prefixEnd_1279253 291942963424972733535257 := by
  unfold tailWord_1279253
  simp only [CollatzResearch.WordTrace]
  refine ⟨46658190034492334863506413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31105460022994889909004275 46658190034492334863506413)
  ·
    refine ⟨17496821262934625573814905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46658190034492334863506413 17496821262934625573814905)
    ·
      refine ⟨13122615947200969180361179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17496821262934625573814905 13122615947200969180361179)
      ·
        refine ⟨19683923920801453770541769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13122615947200969180361179 19683923920801453770541769)
        ·
          refine ⟨14762942940601090327906327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19683923920801453770541769 14762942940601090327906327)
          ·
            refine ⟨22144414410901635491859491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14762942940601090327906327 22144414410901635491859491)
            ·
              refine ⟨33216621616352453237789237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22144414410901635491859491 33216621616352453237789237)
              ·
                refine ⟨3114058276533042491042741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33216621616352453237789237 3114058276533042491042741)
                ·
                  refine ⟨291942963424972733535257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3114058276533042491042741 291942963424972733535257)
                  ·
                    rfl

theorem cell21_1279253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_1279253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279253 prefixEnd_1279253 := by exact prefixLift 1279253
  have htrace : WordTrace (prefixWord ++ tailWord_1279253) baseStart_1279253 baseEnd_1279253 := by
    simpa [prefixWord, tailWord_1279253, baseEnd_1279253] using wordTrace_append hprefix tailTrace_1279253
  have hstable : (prefixWord ++ tailWord_1279253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279253).length < 2 ^ (prefixWord ++ tailWord_1279253).sum := by decide
  have hdescent : baseEnd_1279253 < baseStart_1279253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279332 : List Nat := [2, 3, 1, 1, 3, 4, 2, 5]
def baseStart_1279332 : Nat := 118140960795 + 1279332 * 2 ^ 59
def prefixEnd_1279332 : Nat := 4983230072969 + 3 ^ 40 * 1279332 * 2
def baseEnd_1279332 : Nat := 97320330767095383906143

theorem tailTrace_1279332 : CollatzResearch.WordTrace tailWord_1279332 prefixEnd_1279332 97320330767095383906143 := by
  unfold tailWord_1279332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330535700603065677816125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31107380934137420903754833 23330535700603065677816125)
  ·
    refine ⟨8748950887726149629181047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23330535700603065677816125 8748950887726149629181047)
    ·
      refine ⟨13123426331589224443771571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8748950887726149629181047 13123426331589224443771571)
      ·
        refine ⟨19685139497383836665657357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13123426331589224443771571 19685139497383836665657357)
        ·
          refine ⟨7381927311518938749621509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19685139497383836665657357 7381927311518938749621509)
          ·
            refine ⟨1384111370909801015554033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7381927311518938749621509 1384111370909801015554033)
            ·
              refine ⟨1038083528182350761665525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384111370909801015554033 1038083528182350761665525)
              ·
                refine ⟨97320330767095383906143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1038083528182350761665525 97320330767095383906143)
                ·
                  rfl

theorem cell21_1279332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_1279332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279332 prefixEnd_1279332 := by exact prefixLift 1279332
  have htrace : WordTrace (prefixWord ++ tailWord_1279332) baseStart_1279332 baseEnd_1279332 := by
    simpa [prefixWord, tailWord_1279332, baseEnd_1279332] using wordTrace_append hprefix tailTrace_1279332
  have hstable : (prefixWord ++ tailWord_1279332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279332).length < 2 ^ (prefixWord ++ tailWord_1279332).sum := by decide
  have hdescent : baseEnd_1279332 < baseStart_1279332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279343 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_1279343 : Nat := 118140960795 + 1279343 * 2 ^ 59
def prefixEnd_1279343 : Nat := 4983230072969 + 3 ^ 40 * 1279343 * 2
def baseEnd_1279343 : Nat := 291963502651152577035073

theorem tailTrace_1279343 : CollatzResearch.WordTrace tailWord_1279343 prefixEnd_1279343 291963502651152577035073 := by
  unfold tailWord_1279343
  simp only [CollatzResearch.WordTrace]
  refine ⟨46661472604166280234282683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31107648402777520156188455 46661472604166280234282683)
  ·
    refine ⟨69992208906249420351424025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46661472604166280234282683 69992208906249420351424025)
    ·
      refine ⟨52494156679687065263568019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69992208906249420351424025 52494156679687065263568019)
      ·
        refine ⟨78741235019530597895352029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52494156679687065263568019 78741235019530597895352029)
        ·
          refine ⟨29527963132323974210757011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78741235019530597895352029 29527963132323974210757011)
          ·
            refine ⟨44291944698485961316135517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29527963132323974210757011 44291944698485961316135517)
            ·
              refine ⟨16609479261932235493550819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44291944698485961316135517 16609479261932235493550819)
              ·
                refine ⟨24914218892898353240326229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16609479261932235493550819 24914218892898353240326229)
                ·
                  refine ⟨291963502651152577035073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24914218892898353240326229 291963502651152577035073)
                  ·
                    rfl

theorem cell21_1279343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_1279343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279343 prefixEnd_1279343 := by exact prefixLift 1279343
  have htrace : WordTrace (prefixWord ++ tailWord_1279343) baseStart_1279343 baseEnd_1279343 := by
    simpa [prefixWord, tailWord_1279343, baseEnd_1279343] using wordTrace_append hprefix tailTrace_1279343
  have hstable : (prefixWord ++ tailWord_1279343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279343).length < 2 ^ (prefixWord ++ tailWord_1279343).sum := by decide
  have hdescent : baseEnd_1279343 < baseStart_1279343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279501 : List Nat := [1, 7, 1, 1, 2, 1, 1, 7]
def baseStart_1279501 : Nat := 118140960795 + 1279501 * 2 ^ 59
def prefixEnd_1279501 : Nat := 4983230072969 + 3 ^ 40 * 1279501 * 2
def baseEnd_1279501 : Nat := 97333186801259804467139

theorem tailTrace_1279501 : CollatzResearch.WordTrace tailWord_1279501 prefixEnd_1279501 97333186801259804467139 := by
  unfold tailWord_1279501
  simp only [CollatzResearch.WordTrace]
  refine ⟨46667235337593873218534357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31111490225062582145689571 46667235337593873218534357)
  ·
    refine ⟨1093763328224856403559399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46667235337593873218534357 1093763328224856403559399)
    ·
      refine ⟨1640644992337284605339099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093763328224856403559399 1640644992337284605339099)
      ·
        refine ⟨2460967488505926908008649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640644992337284605339099 2460967488505926908008649)
        ·
          refine ⟨1845725616379445181006487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460967488505926908008649 1845725616379445181006487)
          ·
            refine ⟨2768588424569167771509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845725616379445181006487 2768588424569167771509731)
            ·
              refine ⟨4152882636853751657264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768588424569167771509731 4152882636853751657264597)
              ·
                refine ⟨97333186801259804467139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4152882636853751657264597 97333186801259804467139)
                ·
                  rfl

theorem cell21_1279501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 7].length) (baseStart_1279501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279501 prefixEnd_1279501 := by exact prefixLift 1279501
  have htrace : WordTrace (prefixWord ++ tailWord_1279501) baseStart_1279501 baseEnd_1279501 := by
    simpa [prefixWord, tailWord_1279501, baseEnd_1279501] using wordTrace_append hprefix tailTrace_1279501
  have hstable : (prefixWord ++ tailWord_1279501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279501).length < 2 ^ (prefixWord ++ tailWord_1279501).sum := by decide
  have hdescent : baseEnd_1279501 < baseStart_1279501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279518 : List Nat := [4, 3, 3, 1, 1, 2, 7]
def baseStart_1279518 : Nat := 118140960795 + 1279518 * 2 ^ 59
def prefixEnd_1279518 : Nat := 4983230072969 + 3 ^ 40 * 1279518 * 2
def baseEnd_1279518 : Nat := 32444826670599017957561

theorem tailTrace_1279518 : CollatzResearch.WordTrace tailWord_1279518 prefixEnd_1279518 32444826670599017957561 := by
  unfold tailWord_1279518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833481922316535640237901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31111903585688190081268805 5833481922316535640237901)
  ·
    refine ⟨2187555720868700865089213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5833481922316535640237901 2187555720868700865089213)
    ·
      refine ⟨820333395325762824408455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2187555720868700865089213 820333395325762824408455)
      ·
        refine ⟨1230500092988644236612683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820333395325762824408455 1230500092988644236612683)
        ·
          refine ⟨1845750139482966354919025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230500092988644236612683 1845750139482966354919025)
          ·
            refine ⟨1384312604612224766189269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845750139482966354919025 1384312604612224766189269)
            ·
              refine ⟨32444826670599017957561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1384312604612224766189269 32444826670599017957561)
              ·
                rfl

theorem cell21_1279518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 7].length) (baseStart_1279518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279518 prefixEnd_1279518 := by exact prefixLift 1279518
  have htrace : WordTrace (prefixWord ++ tailWord_1279518) baseStart_1279518 baseEnd_1279518 := by
    simpa [prefixWord, tailWord_1279518, baseEnd_1279518] using wordTrace_append hprefix tailTrace_1279518
  have hstable : (prefixWord ++ tailWord_1279518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279518).length < 2 ^ (prefixWord ++ tailWord_1279518).sum := by decide
  have hdescent : baseEnd_1279518 < baseStart_1279518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279588 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1279588 : Nat := 118140960795 + 1279588 * 2 ^ 59
def prefixEnd_1279588 : Nat := 4983230072969 + 3 ^ 40 * 1279588 * 2
def baseEnd_1279588 : Nat := 292019414989086595451239

theorem tailTrace_1279588 : CollatzResearch.WordTrace tailWord_1279588 prefixEnd_1279588 292019414989086595451239 := by
  unfold tailWord_1279588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23335204244139343538475709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31113605658852458051300945 23335204244139343538475709)
  ·
    refine ⟨8750701591552253826928391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23335204244139343538475709 8750701591552253826928391)
    ·
      refine ⟨13126052387328380740392587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8750701591552253826928391 13126052387328380740392587)
      ·
        refine ⟨19689078580992571110588881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13126052387328380740392587 19689078580992571110588881)
        ·
          refine ⟨14766808935744428332941661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19689078580992571110588881 14766808935744428332941661)
          ·
            refine ⟨5537553350904160624853123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14766808935744428332941661 5537553350904160624853123)
            ·
              refine ⟨8306330026356240937279685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537553350904160624853123 8306330026356240937279685)
              ·
                refine ⟨1557436879941795175739941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8306330026356240937279685 1557436879941795175739941)
                ·
                  refine ⟨292019414989086595451239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557436879941795175739941 292019414989086595451239)
                  ·
                    rfl

theorem cell21_1279588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1279588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279588 prefixEnd_1279588 := by exact prefixLift 1279588
  have htrace : WordTrace (prefixWord ++ tailWord_1279588) baseStart_1279588 baseEnd_1279588 := by
    simpa [prefixWord, tailWord_1279588, baseEnd_1279588] using wordTrace_append hprefix tailTrace_1279588
  have hstable : (prefixWord ++ tailWord_1279588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279588).length < 2 ^ (prefixWord ++ tailWord_1279588).sum := by decide
  have hdescent : baseEnd_1279588 < baseStart_1279588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279591 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 3]
def baseStart_1279591 : Nat := 118140960795 + 1279591 * 2 ^ 59
def prefixEnd_1279591 : Nat := 4983230072969 + 3 ^ 40 * 1279591 * 2
def baseEnd_1279591 : Nat := 292020099629959256901233

theorem tailTrace_1279591 : CollatzResearch.WordTrace tailWord_1279591 prefixEnd_1279591 292020099629959256901233 := by
  unfold tailWord_1279591
  simp only [CollatzResearch.WordTrace]
  refine ⟨46670517907267818589310627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31113678604845212392873751 46670517907267818589310627)
  ·
    refine ⟨70005776860901727883965941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46670517907267818589310627 70005776860901727883965941)
    ·
      refine ⟨6563041580709536989121807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70005776860901727883965941 6563041580709536989121807)
      ·
        refine ⟨9844562371064305483682711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563041580709536989121807 9844562371064305483682711)
        ·
          refine ⟨14766843556596458225524067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9844562371064305483682711 14766843556596458225524067)
          ·
            refine ⟨22150265334894687338286101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14766843556596458225524067 22150265334894687338286101)
            ·
              refine ⟨1038293687573188468982161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22150265334894687338286101 1038293687573188468982161)
              ·
                refine ⟨778720265679891351736621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038293687573188468982161 778720265679891351736621)
                ·
                  refine ⟨292020099629959256901233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778720265679891351736621 292020099629959256901233)
                  ·
                    rfl

theorem cell21_1279591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3].length) (baseStart_1279591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279591 prefixEnd_1279591 := by exact prefixLift 1279591
  have htrace : WordTrace (prefixWord ++ tailWord_1279591) baseStart_1279591 baseEnd_1279591 := by
    simpa [prefixWord, tailWord_1279591, baseEnd_1279591] using wordTrace_append hprefix tailTrace_1279591
  have hstable : (prefixWord ++ tailWord_1279591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279591).length < 2 ^ (prefixWord ++ tailWord_1279591).sum := by decide
  have hdescent : baseEnd_1279591 < baseStart_1279591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279605 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1279605 : Nat := 118140960795 + 1279605 * 2 ^ 59
def prefixEnd_1279605 : Nat := 4983230072969 + 3 ^ 40 * 1279605 * 2
def baseEnd_1279605 : Nat := 292023294620698343667871

theorem tailTrace_1279605 : CollatzResearch.WordTrace tailWord_1279605 prefixEnd_1279605 292023294620698343667871 := by
  unfold tailWord_1279605
  simp only [CollatzResearch.WordTrace]
  refine ⟨46671028529217098980320269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31114019019478065986880179 46671028529217098980320269)
  ·
    refine ⟨17501635698456412117620101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46671028529217098980320269 17501635698456412117620101)
    ·
      refine ⟨3281556693460577272053769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17501635698456412117620101 3281556693460577272053769)
      ·
        refine ⟨2461167520095432954040327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3281556693460577272053769 2461167520095432954040327)
        ·
          refine ⟨3691751280143149431060491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461167520095432954040327 3691751280143149431060491)
          ·
            refine ⟨5537626920214724146590737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691751280143149431060491 5537626920214724146590737)
            ·
              refine ⟨4153220190161043109943053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537626920214724146590737 4153220190161043109943053)
              ·
                refine ⟨1557457571310391166228645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4153220190161043109943053 1557457571310391166228645)
                ·
                  refine ⟨292023294620698343667871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557457571310391166228645 292023294620698343667871)
                  ·
                    rfl

theorem cell21_1279605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1279605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279605 prefixEnd_1279605 := by exact prefixLift 1279605
  have htrace : WordTrace (prefixWord ++ tailWord_1279605) baseStart_1279605 baseEnd_1279605 := by
    simpa [prefixWord, tailWord_1279605, baseEnd_1279605] using wordTrace_append hprefix tailTrace_1279605
  have hstable : (prefixWord ++ tailWord_1279605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279605).length < 2 ^ (prefixWord ++ tailWord_1279605).sum := by decide
  have hdescent : baseEnd_1279605 < baseStart_1279605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279656 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_1279656 : Nat := 118140960795 + 1279656 * 2 ^ 59
def prefixEnd_1279656 : Nat := 4983230072969 + 3 ^ 40 * 1279656 * 2
def baseEnd_1279656 : Nat := 292034933515533588317767

theorem tailTrace_1279656 : CollatzResearch.WordTrace tailWord_1279656 prefixEnd_1279656 292034933515533588317767 := by
  unfold tailWord_1279656
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336444326016167345213411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31115259101354889793617881 23336444326016167345213411)
  ·
    refine ⟨35004666489024251017820117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23336444326016167345213411 35004666489024251017820117)
    ·
      refine ⟨820421870836505883230159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35004666489024251017820117 820421870836505883230159)
      ·
        refine ⟨1230632806254758824845239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820421870836505883230159 1230632806254758824845239)
        ·
          refine ⟨1845949209382138237267859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230632806254758824845239 1845949209382138237267859)
          ·
            refine ⟨2768923814073207355901789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845949209382138237267859 2768923814073207355901789)
            ·
              refine ⟨1038346430277452758463171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2768923814073207355901789 1038346430277452758463171)
              ·
                refine ⟨1557519645416179137694757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038346430277452758463171 1557519645416179137694757)
                ·
                  refine ⟨292034933515533588317767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557519645416179137694757 292034933515533588317767)
                  ·
                    rfl

theorem cell21_1279656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_1279656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279656 prefixEnd_1279656 := by exact prefixLift 1279656
  have htrace : WordTrace (prefixWord ++ tailWord_1279656) baseStart_1279656 baseEnd_1279656 := by
    simpa [prefixWord, tailWord_1279656, baseEnd_1279656] using wordTrace_append hprefix tailTrace_1279656
  have hstable : (prefixWord ++ tailWord_1279656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279656).length < 2 ^ (prefixWord ++ tailWord_1279656).sum := by decide
  have hdescent : baseEnd_1279656 < baseStart_1279656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279715 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 4]
def baseStart_1279715 : Nat := 118140960795 + 1279715 * 2 ^ 59
def prefixEnd_1279715 : Nat := 4983230072969 + 3 ^ 40 * 1279715 * 2
def baseEnd_1279715 : Nat := 292048398119362596834313

theorem tailTrace_1279715 : CollatzResearch.WordTrace tailWord_1279715 prefixEnd_1279715 292048398119362596834313 := by
  unfold tailWord_1279715
  simp only [CollatzResearch.WordTrace]
  refine ⟨46675040558818587766824599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31116693705879058511216399 46675040558818587766824599)
  ·
    refine ⟨70012560838227881650236899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46675040558818587766824599 70012560838227881650236899)
    ·
      refine ⟨105018841257341822475355349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70012560838227881650236899 105018841257341822475355349)
      ·
        refine ⟨2461379091968948964266141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 105018841257341822475355349 2461379091968948964266141)
        ·
          refine ⟨923017159488355861599803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2461379091968948964266141 923017159488355861599803)
          ·
            refine ⟨1384525739232533792399705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923017159488355861599803 1384525739232533792399705)
            ·
              refine ⟨1038394304424400344299779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384525739232533792399705 1038394304424400344299779)
              ·
                refine ⟨1557591456636600516449669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038394304424400344299779 1557591456636600516449669)
                ·
                  refine ⟨292048398119362596834313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557591456636600516449669 292048398119362596834313)
                  ·
                    rfl

theorem cell21_1279715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4].length) (baseStart_1279715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279715 prefixEnd_1279715 := by exact prefixLift 1279715
  have htrace : WordTrace (prefixWord ++ tailWord_1279715) baseStart_1279715 baseEnd_1279715 := by
    simpa [prefixWord, tailWord_1279715, baseEnd_1279715] using wordTrace_append hprefix tailTrace_1279715
  have hstable : (prefixWord ++ tailWord_1279715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279715).length < 2 ^ (prefixWord ++ tailWord_1279715).sum := by decide
  have hdescent : baseEnd_1279715 < baseStart_1279715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279802 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_1279802 : Nat := 118140960795 + 1279802 * 2 ^ 59
def prefixEnd_1279802 : Nat := 4983230072969 + 3 ^ 40 * 1279802 * 2
def baseEnd_1279802 : Nat := 292068252704669778884135

theorem tailTrace_1279802 : CollatzResearch.WordTrace tailWord_1279802 prefixEnd_1279802 292068252704669778884135 := by
  unfold tailWord_1279802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11669553427375850406310415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31118809139668934416827773 11669553427375850406310415)
  ·
    refine ⟨17504330141063775609465623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11669553427375850406310415 17504330141063775609465623)
    ·
      refine ⟨26256495211595663414198435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17504330141063775609465623 26256495211595663414198435)
      ·
        refine ⟨39384742817393495121297653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26256495211595663414198435 39384742817393495121297653)
        ·
          refine ⟨3692319639130640167621655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39384742817393495121297653 3692319639130640167621655)
          ·
            refine ⟨5538479458695960251432483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692319639130640167621655 5538479458695960251432483)
            ·
              refine ⟨8307719188043940377148725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538479458695960251432483 8307719188043940377148725)
              ·
                refine ⟨778848673879119410357693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8307719188043940377148725 778848673879119410357693)
                ·
                  refine ⟨292068252704669778884135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778848673879119410357693 292068252704669778884135)
                  ·
                    rfl

theorem cell21_1279802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_1279802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279802 prefixEnd_1279802 := by exact prefixLift 1279802
  have htrace : WordTrace (prefixWord ++ tailWord_1279802) baseStart_1279802 baseEnd_1279802 := by
    simpa [prefixWord, tailWord_1279802, baseEnd_1279802] using wordTrace_append hprefix tailTrace_1279802
  have hstable : (prefixWord ++ tailWord_1279802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279802).length < 2 ^ (prefixWord ++ tailWord_1279802).sum := by decide
  have hdescent : baseEnd_1279802 < baseStart_1279802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279813 : List Nat := [1, 3, 1, 1, 1, 2, 12]
def baseStart_1279813 : Nat := 118140960795 + 1279813 * 2 ^ 59
def prefixEnd_1279813 : Nat := 4983230072969 + 3 ^ 40 * 1279813 * 2
def baseEnd_1279813 : Nat := 32452307006059578244531

theorem tailTrace_1279813 : CollatzResearch.WordTrace tailWord_1279813 prefixEnd_1279813 32452307006059578244531 := by
  unfold tailWord_1279813
  simp only [CollatzResearch.WordTrace]
  refine ⟨46678614912463550503892093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31119076608309033669261395 46678614912463550503892093)
  ·
    refine ⟨17504480592173831438959535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46678614912463550503892093 17504480592173831438959535)
    ·
      refine ⟨26256720888260747158439303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17504480592173831438959535 26256720888260747158439303)
      ·
        refine ⟨39385081332391120737658955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26256720888260747158439303 39385081332391120737658955)
        ·
          refine ⟨59077621998586681106488433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39385081332391120737658955 59077621998586681106488433)
          ·
            refine ⟨44308216498940010829866325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59077621998586681106488433 44308216498940010829866325)
            ·
              refine ⟨32452307006059578244531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44308216498940010829866325 32452307006059578244531)
              ·
                rfl

theorem cell21_1279813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 12].length) (baseStart_1279813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279813 prefixEnd_1279813 := by exact prefixLift 1279813
  have htrace : WordTrace (prefixWord ++ tailWord_1279813) baseStart_1279813 baseEnd_1279813 := by
    simpa [prefixWord, tailWord_1279813, baseEnd_1279813] using wordTrace_append hprefix tailTrace_1279813
  have hstable : (prefixWord ++ tailWord_1279813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279813).length < 2 ^ (prefixWord ++ tailWord_1279813).sum := by decide
  have hdescent : baseEnd_1279813 < baseStart_1279813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279816 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_1279816 : Nat := 118140960795 + 1279816 * 2 ^ 59
def prefixEnd_1279816 : Nat := 4983230072969 + 3 ^ 40 * 1279816 * 2
def baseEnd_1279816 : Nat := 292071447695408865650773

theorem tailTrace_1279816 : CollatzResearch.WordTrace tailWord_1279816 prefixEnd_1279816 292071447695408865650773 := by
  unfold tailWord_1279816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23339362165726341008125651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31119149554301788010834201 23339362165726341008125651)
  ·
    refine ⟨35009043248589511512188477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23339362165726341008125651 35009043248589511512188477)
    ·
      refine ⟨13128391218221066817070679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35009043248589511512188477 13128391218221066817070679)
      ·
        refine ⟨19692586827331600225606019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13128391218221066817070679 19692586827331600225606019)
        ·
          refine ⟨29538880240997400338409029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19692586827331600225606019 29538880240997400338409029)
          ·
            refine ⟨5538540045187012563451693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29538880240997400338409029 5538540045187012563451693)
            ·
              refine ⟨2076952516945129711294385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5538540045187012563451693 2076952516945129711294385)
              ·
                refine ⟨1557714387708847283470789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076952516945129711294385 1557714387708847283470789)
                ·
                  refine ⟨292071447695408865650773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557714387708847283470789 292071447695408865650773)
                  ·
                    rfl

theorem cell21_1279816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_1279816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279816 prefixEnd_1279816 := by exact prefixLift 1279816
  have htrace : WordTrace (prefixWord ++ tailWord_1279816) baseStart_1279816 baseEnd_1279816 := by
    simpa [prefixWord, tailWord_1279816, baseEnd_1279816] using wordTrace_append hprefix tailTrace_1279816
  have hstable : (prefixWord ++ tailWord_1279816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279816).length < 2 ^ (prefixWord ++ tailWord_1279816).sum := by decide
  have hdescent : baseEnd_1279816 < baseStart_1279816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279875 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_1279875 : Nat := 118140960795 + 1279875 * 2 ^ 59
def prefixEnd_1279875 : Nat := 4983230072969 + 3 ^ 40 * 1279875 * 2
def baseEnd_1279875 : Nat := 292084912299237874167319

theorem tailTrace_1279875 : CollatzResearch.WordTrace tailWord_1279875 prefixEnd_1279875 292084912299237874167319 := by
  unfold tailWord_1279875
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680876238238935092649079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31120584158825956728432719 46680876238238935092649079)
  ·
    refine ⟨70021314357358402638973619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46680876238238935092649079 70021314357358402638973619)
    ·
      refine ⟨105031971536037603958460429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70021314357358402638973619 105031971536037603958460429)
      ·
        refine ⟨39386989326014101484422661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105031971536037603958460429 39386989326014101484422661)
        ·
          refine ⟨7385060498627644028329249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39386989326014101484422661 7385060498627644028329249)
          ·
            refine ⟨5538795373970733021246937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385060498627644028329249 5538795373970733021246937)
            ·
              refine ⟨4154096530478049765935203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538795373970733021246937 4154096530478049765935203)
              ·
                refine ⟨6231144795717074648902805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154096530478049765935203 6231144795717074648902805)
                ·
                  refine ⟨292084912299237874167319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6231144795717074648902805 292084912299237874167319)
                  ·
                    rfl

theorem cell21_1279875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_1279875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279875 prefixEnd_1279875 := by exact prefixLift 1279875
  have htrace : WordTrace (prefixWord ++ tailWord_1279875) baseStart_1279875 baseEnd_1279875 := by
    simpa [prefixWord, tailWord_1279875, baseEnd_1279875] using wordTrace_append hprefix tailTrace_1279875
  have hstable : (prefixWord ++ tailWord_1279875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279875).length < 2 ^ (prefixWord ++ tailWord_1279875).sum := by decide
  have hdescent : baseEnd_1279875 < baseStart_1279875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279889 : List Nat := [1, 2, 2, 1, 1, 1, 5, 8]
def baseStart_1279889 : Nat := 118140960795 + 1279889 * 2 ^ 59
def prefixEnd_1279889 : Nat := 4983230072969 + 3 ^ 40 * 1279889 * 2
def baseEnd_1279889 : Nat := 97362702429992320311319

theorem tailTrace_1279889 : CollatzResearch.WordTrace tailWord_1279889 prefixEnd_1279889 97362702429992320311319 := by
  unfold tailWord_1279889
  simp only [CollatzResearch.WordTrace]
  refine ⟨46681386860188215483658721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31120924573458810322439147 46681386860188215483658721)
  ·
    refine ⟨35011040145141161612744041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46681386860188215483658721 35011040145141161612744041)
    ·
      refine ⟨26258280108855871209558031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35011040145141161612744041 26258280108855871209558031)
      ·
        refine ⟨39387420163283806814337047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26258280108855871209558031 39387420163283806814337047)
        ·
          refine ⟨59081130244925710221505571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39387420163283806814337047 59081130244925710221505571)
          ·
            refine ⟨88621695367388565332258357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59081130244925710221505571 88621695367388565332258357)
            ·
              refine ⟨8308283940692677999899221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88621695367388565332258357 8308283940692677999899221)
              ·
                refine ⟨97362702429992320311319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8308283940692677999899221 97362702429992320311319)
                ·
                  rfl

theorem cell21_1279889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_1279889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279889 prefixEnd_1279889 := by exact prefixLift 1279889
  have htrace : WordTrace (prefixWord ++ tailWord_1279889) baseStart_1279889 baseEnd_1279889 := by
    simpa [prefixWord, tailWord_1279889, baseEnd_1279889] using wordTrace_append hprefix tailTrace_1279889
  have hstable : (prefixWord ++ tailWord_1279889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279889).length < 2 ^ (prefixWord ++ tailWord_1279889).sum := by decide
  have hdescent : baseEnd_1279889 < baseStart_1279889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279951 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_1279951 : Nat := 118140960795 + 1279951 * 2 ^ 59
def prefixEnd_1279951 : Nat := 4983230072969 + 3 ^ 40 * 1279951 * 2
def baseEnd_1279951 : Nat := 292102256534678630900497

theorem tailTrace_1279951 : CollatzResearch.WordTrace tailWord_1279951 prefixEnd_1279951 292102256534678630900497 := by
  unfold tailWord_1279951
  simp only [CollatzResearch.WordTrace]
  refine ⟨46683648185963600072415707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31122432123975733381610471 46683648185963600072415707)
  ·
    refine ⟨70025472278945400108623561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46683648185963600072415707 70025472278945400108623561)
    ·
      refine ⟨52519104209209050081467671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70025472278945400108623561 52519104209209050081467671)
      ·
        refine ⟨78778656313813575122201507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52519104209209050081467671 78778656313813575122201507)
        ·
          refine ⟨118167984470720362683302261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78778656313813575122201507 118167984470720362683302261)
          ·
            refine ⟨11078248544130034001559587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118167984470720362683302261 11078248544130034001559587)
            ·
              refine ⟨16617372816195051002339381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11078248544130034001559587 16617372816195051002339381)
              ·
                refine ⟨1557878701518286031469317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16617372816195051002339381 1557878701518286031469317)
                ·
                  refine ⟨292102256534678630900497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557878701518286031469317 292102256534678630900497)
                  ·
                    rfl

theorem cell21_1279951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_1279951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279951 prefixEnd_1279951 := by exact prefixLift 1279951
  have htrace : WordTrace (prefixWord ++ tailWord_1279951) baseStart_1279951 baseEnd_1279951 := by
    simpa [prefixWord, tailWord_1279951, baseEnd_1279951] using wordTrace_append hprefix tailTrace_1279951
  have hstable : (prefixWord ++ tailWord_1279951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279951).length < 2 ^ (prefixWord ++ tailWord_1279951).sum := by decide
  have hdescent : baseEnd_1279951 < baseStart_1279951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279954 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1279954 : Nat := 118140960795 + 1279954 * 2 ^ 59
def prefixEnd_1279954 : Nat := 4983230072969 + 3 ^ 40 * 1279954 * 2
def baseEnd_1279954 : Nat := 292102941175551292350491

theorem tailTrace_1279954 : CollatzResearch.WordTrace tailWord_1279954 prefixEnd_1279954 292102941175551292350491 := by
  unfold tailWord_1279954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11670939401238182896193729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31122505069968487723183277 11670939401238182896193729)
  ·
    refine ⟨8753204550928637172145297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11670939401238182896193729 8753204550928637172145297)
    ·
      refine ⟨6564903413196477879108973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8753204550928637172145297 6564903413196477879108973)
      ·
        refine ⟨2461838779948679204665865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6564903413196477879108973 2461838779948679204665865)
        ·
          refine ⟨1846379084961509403499399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2461838779948679204665865 1846379084961509403499399)
          ·
            refine ⟨2769568627442264105249099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846379084961509403499399 2769568627442264105249099)
            ·
              refine ⟨4154352941163396157873649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769568627442264105249099 4154352941163396157873649)
              ·
                refine ⟨3115764705872547118405237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154352941163396157873649 3115764705872547118405237)
                ·
                  refine ⟨292102941175551292350491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3115764705872547118405237 292102941175551292350491)
                  ·
                    rfl

theorem cell21_1279954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1279954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279954 prefixEnd_1279954 := by exact prefixLift 1279954
  have htrace : WordTrace (prefixWord ++ tailWord_1279954) baseStart_1279954 baseEnd_1279954 := by
    simpa [prefixWord, tailWord_1279954, baseEnd_1279954] using wordTrace_append hprefix tailTrace_1279954
  have hstable : (prefixWord ++ tailWord_1279954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279954).length < 2 ^ (prefixWord ++ tailWord_1279954).sum := by decide
  have hdescent : baseEnd_1279954 < baseStart_1279954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279982 : List Nat := [4, 1, 2, 1, 3, 2, 8]
def baseStart_1279982 : Nat := 118140960795 + 1279982 * 2 ^ 59
def prefixEnd_1279982 : Nat := 4983230072969 + 3 ^ 40 * 1279982 * 2
def baseEnd_1279982 : Nat := 32456592350781051764863

theorem tailTrace_1279982 : CollatzResearch.WordTrace tailWord_1279982 prefixEnd_1279982 32456592350781051764863 := by
  unfold tailWord_1279982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835597356106411545849275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31123185899234194911196133 5835597356106411545849275)
  ·
    refine ⟨8753396034159617318773913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835597356106411545849275 8753396034159617318773913)
    ·
      refine ⟨6565047025619712989080435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8753396034159617318773913 6565047025619712989080435)
      ·
        refine ⟨9847570538429569483620653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565047025619712989080435 9847570538429569483620653)
        ·
          refine ⟨3692838951911088556357745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9847570538429569483620653 3692838951911088556357745)
          ·
            refine ⟨2769629213933316417268309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692838951911088556357745 2769629213933316417268309)
            ·
              refine ⟨32456592350781051764863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2769629213933316417268309 32456592350781051764863)
              ·
                rfl

theorem cell21_1279982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 8].length) (baseStart_1279982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279982 prefixEnd_1279982 := by exact prefixLift 1279982
  have htrace : WordTrace (prefixWord ++ tailWord_1279982) baseStart_1279982 baseEnd_1279982 := by
    simpa [prefixWord, tailWord_1279982, baseEnd_1279982] using wordTrace_append hprefix tailTrace_1279982
  have hstable : (prefixWord ++ tailWord_1279982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279982).length < 2 ^ (prefixWord ++ tailWord_1279982).sum := by decide
  have hdescent : baseEnd_1279982 < baseStart_1279982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279985 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 4]
def baseStart_1279985 : Nat := 118140960795 + 1279985 * 2 ^ 59
def prefixEnd_1279985 : Nat := 4983230072969 + 3 ^ 40 * 1279985 * 2
def baseEnd_1279985 : Nat := 292110015797902127333761

theorem tailTrace_1279985 : CollatzResearch.WordTrace tailWord_1279985 prefixEnd_1279985 292110015797902127333761 := by
  unfold tailWord_1279985
  simp only [CollatzResearch.WordTrace]
  refine ⟨46684888267840423879153409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31123258845226949252768939 46684888267840423879153409)
  ·
    refine ⟨35013666200880317909365057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46684888267840423879153409 35013666200880317909365057)
    ·
      refine ⟨26260249650660238432023793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35013666200880317909365057 26260249650660238432023793)
      ·
        refine ⟨19695187237995178824017845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26260249650660238432023793 19695187237995178824017845)
        ·
          refine ⟨1846423803562048014751673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19695187237995178824017845 1846423803562048014751673)
          ·
            refine ⟨1384817852671536011063755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1846423803562048014751673 1384817852671536011063755)
            ·
              refine ⟨2077226779007304016595633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384817852671536011063755 2077226779007304016595633)
              ·
                refine ⟨1557920084255478012446725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077226779007304016595633 1557920084255478012446725)
                ·
                  refine ⟨292110015797902127333761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557920084255478012446725 292110015797902127333761)
                  ·
                    rfl

theorem cell21_1279985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_1279985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1279985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1279985 prefixEnd_1279985 := by exact prefixLift 1279985
  have htrace : WordTrace (prefixWord ++ tailWord_1279985) baseStart_1279985 baseEnd_1279985 := by
    simpa [prefixWord, tailWord_1279985, baseEnd_1279985] using wordTrace_append hprefix tailTrace_1279985
  have hstable : (prefixWord ++ tailWord_1279985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279985).length < 2 ^ (prefixWord ++ tailWord_1279985).sum := by decide
  have hdescent : baseEnd_1279985 < baseStart_1279985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280089 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 3]
def baseStart_1280089 : Nat := 118140960795 + 1280089 * 2 ^ 59
def prefixEnd_1280089 : Nat := 4983230072969 + 3 ^ 40 * 1280089 * 2
def baseEnd_1280089 : Nat := 292133750014821057600215

theorem tailTrace_1280089 : CollatzResearch.WordTrace tailWord_1280089 prefixEnd_1280089 292133750014821057600215 := by
  unfold tailWord_1280089
  simp only [CollatzResearch.WordTrace]
  refine ⟨46688681459463649640939321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31125787639642433093959547 46688681459463649640939321)
  ·
    refine ⟨35016511094597737230704491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46688681459463649640939321 35016511094597737230704491)
    ·
      refine ⟨52524766641896605846056737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35016511094597737230704491 52524766641896605846056737)
      ·
        refine ⟨39393574981422454384542553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52524766641896605846056737 39393574981422454384542553)
        ·
          refine ⟨29545181236066840788406915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39393574981422454384542553 29545181236066840788406915)
          ·
            refine ⟨44317771854100261182610373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29545181236066840788406915 44317771854100261182610373)
            ·
              refine ⟨8309582222643798971739445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44317771854100261182610373 8309582222643798971739445)
              ·
                refine ⟨779023333372856153600573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8309582222643798971739445 779023333372856153600573)
                ·
                  refine ⟨292133750014821057600215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779023333372856153600573 292133750014821057600215)
                  ·
                    rfl

theorem cell21_1280089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_1280089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280089 prefixEnd_1280089 := by exact prefixLift 1280089
  have htrace : WordTrace (prefixWord ++ tailWord_1280089) baseStart_1280089 baseEnd_1280089 := by
    simpa [prefixWord, tailWord_1280089, baseEnd_1280089] using wordTrace_append hprefix tailTrace_1280089
  have hstable : (prefixWord ++ tailWord_1280089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280089).length < 2 ^ (prefixWord ++ tailWord_1280089).sum := by decide
  have hdescent : baseEnd_1280089 < baseStart_1280089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280154 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_1280154 : Nat := 118140960795 + 1280154 * 2 ^ 59
def prefixEnd_1280154 : Nat := 4983230072969 + 3 ^ 40 * 1280154 * 2
def baseEnd_1280154 : Nat := 292148583900395389016749

theorem tailTrace_1280154 : CollatzResearch.WordTrace tailWord_1280154 prefixEnd_1280154 292148583900395389016749 := by
  unfold tailWord_1280154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672763051057041435513879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31127368136152110494703677 11672763051057041435513879)
  ·
    refine ⟨17509144576585562153270819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11672763051057041435513879 17509144576585562153270819)
    ·
      refine ⟨26263716864878343229906229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17509144576585562153270819 26263716864878343229906229)
      ·
        refine ⟨2462223456082344677803709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26263716864878343229906229 2462223456082344677803709)
        ·
          refine ⟨923333796030879254176391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2462223456082344677803709 923333796030879254176391)
          ·
            refine ⟨1385000694046318881264587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923333796030879254176391 1385000694046318881264587)
            ·
              refine ⟨2077501041069478321896881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385000694046318881264587 2077501041069478321896881)
              ·
                refine ⟨1558125780802108741422661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077501041069478321896881 1558125780802108741422661)
                ·
                  refine ⟨292148583900395389016749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558125780802108741422661 292148583900395389016749)
                  ·
                    rfl

theorem cell21_1280154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_1280154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280154 prefixEnd_1280154 := by exact prefixLift 1280154
  have htrace : WordTrace (prefixWord ++ tailWord_1280154) baseStart_1280154 baseEnd_1280154 := by
    simpa [prefixWord, tailWord_1280154, baseEnd_1280154] using wordTrace_append hprefix tailTrace_1280154
  have hstable : (prefixWord ++ tailWord_1280154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280154).length < 2 ^ (prefixWord ++ tailWord_1280154).sum := by decide
  have hdescent : baseEnd_1280154 < baseStart_1280154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280165 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 3]
def baseStart_1280165 : Nat := 118140960795 + 1280165 * 2 ^ 59
def prefixEnd_1280165 : Nat := 4983230072969 + 3 ^ 40 * 1280165 * 2
def baseEnd_1280165 : Nat := 292151094250261814333393

theorem tailTrace_1280165 : CollatzResearch.WordTrace tailWord_1280165 prefixEnd_1280165 292151094250261814333393 := by
  unfold tailWord_1280165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46691453407188314620705949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31127635604792209747137299 46691453407188314620705949)
  ·
    refine ⟨17509295027695617982764731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46691453407188314620705949 17509295027695617982764731)
    ·
      refine ⟨26263942541543426974147097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17509295027695617982764731 26263942541543426974147097)
      ·
        refine ⟨19697956906157570230610323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26263942541543426974147097 19697956906157570230610323)
        ·
          refine ⟨29546935359236355345915485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19697956906157570230610323 29546935359236355345915485)
          ·
            refine ⟨11080100759713633254718307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29546935359236355345915485 11080100759713633254718307)
            ·
              refine ⟨16620151139570449882077461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11080100759713633254718307 16620151139570449882077461)
              ·
                refine ⟨779069584667364838222381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16620151139570449882077461 779069584667364838222381)
                ·
                  refine ⟨292151094250261814333393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779069584667364838222381 292151094250261814333393)
                  ·
                    rfl

theorem cell21_1280165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_1280165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280165 prefixEnd_1280165 := by exact prefixLift 1280165
  have htrace : WordTrace (prefixWord ++ tailWord_1280165) baseStart_1280165 baseEnd_1280165 := by
    simpa [prefixWord, tailWord_1280165, baseEnd_1280165] using wordTrace_append hprefix tailTrace_1280165
  have hstable : (prefixWord ++ tailWord_1280165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280165).length < 2 ^ (prefixWord ++ tailWord_1280165).sum := by decide
  have hdescent : baseEnd_1280165 < baseStart_1280165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280210 : List Nat := [3, 2, 2, 2, 1, 4, 7]
def baseStart_1280210 : Nat := 118140960795 + 1280210 * 2 ^ 59
def prefixEnd_1280210 : Nat := 4983230072969 + 3 ^ 40 * 1280210 * 2
def baseEnd_1280210 : Nat := 32462373762594637342589

theorem tailTrace_1280210 : CollatzResearch.WordTrace tailWord_1280210 prefixEnd_1280210 32462373762594637342589 := by
  unfold tailWord_1280210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673273673006321826523521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31128729794683524870729389 11673273673006321826523521)
  ·
    refine ⟨8754955254754741369892641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11673273673006321826523521 8754955254754741369892641)
    ·
      refine ⟨6566216441066056027419481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8754955254754741369892641 6566216441066056027419481)
      ·
        refine ⟨4924662330799542020564611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6566216441066056027419481 4924662330799542020564611)
        ·
          refine ⟨7386993496199313030846917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924662330799542020564611 7386993496199313030846917)
          ·
            refine ⟨1385061280537371193283797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7386993496199313030846917 1385061280537371193283797)
            ·
              refine ⟨32462373762594637342589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1385061280537371193283797 32462373762594637342589)
              ·
                rfl

theorem cell21_1280210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 7].length) (baseStart_1280210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280210 prefixEnd_1280210 := by exact prefixLift 1280210
  have htrace : WordTrace (prefixWord ++ tailWord_1280210) baseStart_1280210 baseEnd_1280210 := by
    simpa [prefixWord, tailWord_1280210, baseEnd_1280210] using wordTrace_append hprefix tailTrace_1280210
  have hstable : (prefixWord ++ tailWord_1280210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280210).length < 2 ^ (prefixWord ++ tailWord_1280210).sum := by decide
  have hdescent : baseEnd_1280210 < baseStart_1280210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280227 : List Nat := [1, 1, 1, 8, 1, 1, 2, 6]
def baseStart_1280227 : Nat := 118140960795 + 1280227 * 2 ^ 59
def prefixEnd_1280227 : Nat := 4983230072969 + 3 ^ 40 * 1280227 * 2
def baseEnd_1280227 : Nat := 97388414498321161433311

theorem tailTrace_1280227 : CollatzResearch.WordTrace tailWord_1280227 prefixEnd_1280227 97388414498321161433311 := by
  unfold tailWord_1280227
  simp only [CollatzResearch.WordTrace]
  refine ⟨46693714732963699209462935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31129143155309132806308623 46693714732963699209462935)
  ·
    refine ⟨70040572099445548814194403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46693714732963699209462935 70040572099445548814194403)
    ·
      refine ⟨105060858149168323221291605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70040572099445548814194403 105060858149168323221291605)
      ·
        refine ⟨1231181931435566287749511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 105060858149168323221291605 1231181931435566287749511)
        ·
          refine ⟨1846772897153349431624267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231181931435566287749511 1846772897153349431624267)
          ·
            refine ⟨2770159345730024147436401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846772897153349431624267 2770159345730024147436401)
            ·
              refine ⟨2077619509297518110577301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770159345730024147436401 2077619509297518110577301)
              ·
                refine ⟨97388414498321161433311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2077619509297518110577301 97388414498321161433311)
                ·
                  rfl

theorem cell21_1280227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 6].length) (baseStart_1280227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280227 prefixEnd_1280227 := by exact prefixLift 1280227
  have htrace : WordTrace (prefixWord ++ tailWord_1280227) baseStart_1280227 baseEnd_1280227 := by
    simpa [prefixWord, tailWord_1280227, baseEnd_1280227] using wordTrace_append hprefix tailTrace_1280227
  have hstable : (prefixWord ++ tailWord_1280227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280227).length < 2 ^ (prefixWord ++ tailWord_1280227).sum := by decide
  have hdescent : baseEnd_1280227 < baseStart_1280227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280362 : List Nat := [3, 1, 3, 3, 1, 2, 1, 7]
def baseStart_1280362 : Nat := 118140960795 + 1280362 * 2 ^ 59
def prefixEnd_1280362 : Nat := 4983230072969 + 3 ^ 40 * 1280362 * 2
def baseEnd_1280362 : Nat := 97398684111411083183219

theorem tailTrace_1280362 : CollatzResearch.WordTrace tailWord_1280362 prefixEnd_1280362 97398684111411083183219 := by
  unfold tailWord_1280362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674659646868654316406835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31132425724983078177084893 11674659646868654316406835)
  ·
    refine ⟨17511989470302981474610253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11674659646868654316406835 17511989470302981474610253)
    ·
      refine ⟨6566996051363618052978845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17511989470302981474610253 6566996051363618052978845)
      ·
        refine ⟨2462623519261356769867067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6566996051363618052978845 2462623519261356769867067)
        ·
          refine ⟨3693935278892035154800601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462623519261356769867067 3693935278892035154800601)
          ·
            refine ⟨2770451459169026366100451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3693935278892035154800601 2770451459169026366100451)
            ·
              refine ⟨4155677188753539549150677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770451459169026366100451 4155677188753539549150677)
              ·
                refine ⟨97398684111411083183219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4155677188753539549150677 97398684111411083183219)
                ·
                  rfl

theorem cell21_1280362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_1280362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280362 prefixEnd_1280362 := by exact prefixLift 1280362
  have htrace : WordTrace (prefixWord ++ tailWord_1280362) baseStart_1280362 baseEnd_1280362 := by
    simpa [prefixWord, tailWord_1280362, baseEnd_1280362] using wordTrace_append hprefix tailTrace_1280362
  have hstable : (prefixWord ++ tailWord_1280362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280362).length < 2 ^ (prefixWord ++ tailWord_1280362).sum := by decide
  have hdescent : baseEnd_1280362 < baseStart_1280362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280393 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 5]
def baseStart_1280393 : Nat := 118140960795 + 1280393 * 2 ^ 59
def prefixEnd_1280393 : Nat := 4983230072969 + 3 ^ 40 * 1280393 * 2
def baseEnd_1280393 : Nat := 292203126956584084532927

theorem tailTrace_1280393 : CollatzResearch.WordTrace tailWord_1280393 prefixEnd_1280393 292203126956584084532927 := by
  unfold tailWord_1280393
  simp only [CollatzResearch.WordTrace]
  refine ⟨46699769250362309560005833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31133179500241539706670555 46699769250362309560005833)
  ·
    refine ⟨35024826937771732170004375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46699769250362309560005833 35024826937771732170004375)
    ·
      refine ⟨52537240406657598255006563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35024826937771732170004375 52537240406657598255006563)
      ·
        refine ⟨78805860609986397382509845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52537240406657598255006563 78805860609986397382509845)
        ·
          refine ⟨3694024716093112377305149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78805860609986397382509845 3694024716093112377305149)
          ·
            refine ⟨1385259268534917141489431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3694024716093112377305149 1385259268534917141489431)
            ·
              refine ⟨2077888902802375712234147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385259268534917141489431 2077888902802375712234147)
              ·
                refine ⟨3116833354203563568351221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077888902802375712234147 3116833354203563568351221)
                ·
                  refine ⟨292203126956584084532927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3116833354203563568351221 292203126956584084532927)
                  ·
                    rfl

theorem cell21_1280393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_1280393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280393 prefixEnd_1280393 := by exact prefixLift 1280393
  have htrace : WordTrace (prefixWord ++ tailWord_1280393) baseStart_1280393 baseEnd_1280393 := by
    simpa [prefixWord, tailWord_1280393, baseEnd_1280393] using wordTrace_append hprefix tailTrace_1280393
  have hstable : (prefixWord ++ tailWord_1280393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280393).length < 2 ^ (prefixWord ++ tailWord_1280393).sum := by decide
  have hdescent : baseEnd_1280393 < baseStart_1280393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280573 : List Nat := [1, 4, 1, 3, 2, 1, 1, 8]
def baseStart_1280573 : Nat := 118140960795 + 1280573 * 2 ^ 59
def prefixEnd_1280573 : Nat := 4983230072969 + 3 ^ 40 * 1280573 * 2
def baseEnd_1280573 : Nat := 97414735136314590510853

theorem tailTrace_1280573 : CollatzResearch.WordTrace tailWord_1280573 prefixEnd_1280573 97414735136314590510853 := by
  unfold tailWord_1280573
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706334389710200301558373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31137556259806800201038915 46706334389710200301558373)
  ·
    refine ⟨8757437698070662556542195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46706334389710200301558373 8757437698070662556542195)
    ·
      refine ⟨13136156547105993834813293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8757437698070662556542195 13136156547105993834813293)
      ·
        refine ⟨4926058705164747688054985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13136156547105993834813293 4926058705164747688054985)
        ·
          refine ⟨3694544028873560766041239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4926058705164747688054985 3694544028873560766041239)
          ·
            refine ⟨5541816043310341149061859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694544028873560766041239 5541816043310341149061859)
            ·
              refine ⟨8312724064965511723592789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541816043310341149061859 8312724064965511723592789)
              ·
                refine ⟨97414735136314590510853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8312724064965511723592789 97414735136314590510853)
                ·
                  rfl

theorem cell21_1280573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_1280573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280573 prefixEnd_1280573 := by exact prefixLift 1280573
  have htrace : WordTrace (prefixWord ++ tailWord_1280573) baseStart_1280573 baseEnd_1280573 := by
    simpa [prefixWord, tailWord_1280573, baseEnd_1280573] using wordTrace_append hprefix tailTrace_1280573
  have hstable : (prefixWord ++ tailWord_1280573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280573).length < 2 ^ (prefixWord ++ tailWord_1280573).sum := by decide
  have hdescent : baseEnd_1280573 < baseStart_1280573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280587 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_1280587 : Nat := 118140960795 + 1280587 * 2 ^ 59
def prefixEnd_1280587 : Nat := 4983230072969 + 3 ^ 40 * 1280587 * 2
def baseEnd_1280587 : Nat := 292247400399682858299197

theorem tailTrace_1280587 : CollatzResearch.WordTrace tailWord_1280587 prefixEnd_1280587 292247400399682858299197 := by
  unfold tailWord_1280587
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706845011659480692568015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31137896674439653795045343 46706845011659480692568015)
  ·
    refine ⟨70060267517489221038852023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46706845011659480692568015 70060267517489221038852023)
    ·
      refine ⟨105090401276233831558278035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70060267517489221038852023 105090401276233831558278035)
      ·
        refine ⟨157635601914350747337417053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105090401276233831558278035 157635601914350747337417053)
        ·
          refine ⟨59113350717881530251531395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157635601914350747337417053 59113350717881530251531395)
          ·
            refine ⟨88670026076822295377297093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59113350717881530251531395 88670026076822295377297093)
            ·
              refine ⟨16625629889404180383243205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88670026076822295377297093 16625629889404180383243205)
              ·
                refine ⟨3117305604263283821858101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16625629889404180383243205 3117305604263283821858101)
                ·
                  refine ⟨292247400399682858299197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117305604263283821858101 292247400399682858299197)
                  ·
                    rfl

theorem cell21_1280587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_1280587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280587 prefixEnd_1280587 := by exact prefixLift 1280587
  have htrace : WordTrace (prefixWord ++ tailWord_1280587) baseStart_1280587 baseEnd_1280587 := by
    simpa [prefixWord, tailWord_1280587, baseEnd_1280587] using wordTrace_append hprefix tailTrace_1280587
  have hstable : (prefixWord ++ tailWord_1280587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280587).length < 2 ^ (prefixWord ++ tailWord_1280587).sum := by decide
  have hdescent : baseEnd_1280587 < baseStart_1280587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280663 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_1280663 : Nat := 118140960795 + 1280663 * 2 ^ 59
def prefixEnd_1280663 : Nat := 4983230072969 + 3 ^ 40 * 1280663 * 2
def baseEnd_1280663 : Nat := 292264744635123615032375

theorem tailTrace_1280663 : CollatzResearch.WordTrace tailWord_1280663 prefixEnd_1280663 292264744635123615032375 := by
  unfold tailWord_1280663
  simp only [CollatzResearch.WordTrace]
  refine ⟨46709616959384145672334643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31139744639589430448223095 46709616959384145672334643)
  ·
    refine ⟨70064425439076218508501965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46709616959384145672334643 70064425439076218508501965)
    ·
      refine ⟨26274159539653581940688237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70064425439076218508501965 26274159539653581940688237)
      ·
        refine ⟨9852809827370093227758089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26274159539653581940688237 9852809827370093227758089)
        ·
          refine ⟨7389607370527569920818567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9852809827370093227758089 7389607370527569920818567)
          ·
            refine ⟨11084411055791354881227851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7389607370527569920818567 11084411055791354881227851)
            ·
              refine ⟨16626616583687032321841777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11084411055791354881227851 16626616583687032321841777)
              ·
                refine ⟨12469962437765274241381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16626616583687032321841777 12469962437765274241381333)
                ·
                  refine ⟨292264744635123615032375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12469962437765274241381333 292264744635123615032375)
                  ·
                    rfl

theorem cell21_1280663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_1280663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280663 prefixEnd_1280663 := by exact prefixLift 1280663
  have htrace : WordTrace (prefixWord ++ tailWord_1280663) baseStart_1280663 baseEnd_1280663 := by
    simpa [prefixWord, tailWord_1280663, baseEnd_1280663] using wordTrace_append hprefix tailTrace_1280663
  have hstable : (prefixWord ++ tailWord_1280663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280663).length < 2 ^ (prefixWord ++ tailWord_1280663).sum := by decide
  have hdescent : baseEnd_1280663 < baseStart_1280663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280666 : List Nat := [3, 1, 1, 6, 1, 1, 8]
def baseStart_1280666 : Nat := 118140960795 + 1280666 * 2 ^ 59
def prefixEnd_1280666 : Nat := 4983230072969 + 3 ^ 40 * 1280666 * 2
def baseEnd_1280666 : Nat := 32473936586221808498041

theorem tailTrace_1280666 : CollatzResearch.WordTrace tailWord_1280666 prefixEnd_1280666 32473936586221808498041 := by
  unfold tailWord_1280666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677431594593319296173463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31139817585582184789795901 11677431594593319296173463)
  ·
    refine ⟨17516147391889978944260195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11677431594593319296173463 17516147391889978944260195)
    ·
      refine ⟨26274221087834968416390293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17516147391889978944260195 26274221087834968416390293)
      ·
        refine ⟨1231604113492264144518295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26274221087834968416390293 1231604113492264144518295)
        ·
          refine ⟨1847406170238396216777443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231604113492264144518295 1847406170238396216777443)
          ·
            refine ⟨2771109255357594325166165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847406170238396216777443 2771109255357594325166165)
            ·
              refine ⟨32473936586221808498041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2771109255357594325166165 32473936586221808498041)
              ·
                rfl

theorem cell21_1280666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 8].length) (baseStart_1280666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280666 prefixEnd_1280666 := by exact prefixLift 1280666
  have htrace : WordTrace (prefixWord ++ tailWord_1280666) baseStart_1280666 baseEnd_1280666 := by
    simpa [prefixWord, tailWord_1280666, baseEnd_1280666] using wordTrace_append hprefix tailTrace_1280666
  have hstable : (prefixWord ++ tailWord_1280666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280666).length < 2 ^ (prefixWord ++ tailWord_1280666).sum := by decide
  have hdescent : baseEnd_1280666 < baseStart_1280666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280714 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_1280714 : Nat := 118140960795 + 1280714 * 2 ^ 59
def prefixEnd_1280714 : Nat := 4983230072969 + 3 ^ 40 * 1280714 * 2
def baseEnd_1280714 : Nat := 292276383529958859682271

theorem tailTrace_1280714 : CollatzResearch.WordTrace tailWord_1280714 prefixEnd_1280714 292276383529958859682271 := by
  unfold tailWord_1280714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677869270549845345610299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31140984721466254254960797 11677869270549845345610299)
  ·
    refine ⟨17516803905824768018415449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11677869270549845345610299 17516803905824768018415449)
    ·
      refine ⟨13137602929368576013811587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17516803905824768018415449 13137602929368576013811587)
      ·
        refine ⟨19706404394052864020717381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13137602929368576013811587 19706404394052864020717381)
        ·
          refine ⟨3694950823884912003884509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19706404394052864020717381 3694950823884912003884509)
          ·
            refine ⟨1385606558956842001456691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3694950823884912003884509 1385606558956842001456691)
            ·
              refine ⟨2078409838435263002185037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385606558956842001456691 2078409838435263002185037)
              ·
                refine ⟨779403689413223625819389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2078409838435263002185037 779403689413223625819389)
                ·
                  refine ⟨292276383529958859682271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779403689413223625819389 292276383529958859682271)
                  ·
                    rfl

theorem cell21_1280714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_1280714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280714 prefixEnd_1280714 := by exact prefixLift 1280714
  have htrace : WordTrace (prefixWord ++ tailWord_1280714) baseStart_1280714 baseEnd_1280714 := by
    simpa [prefixWord, tailWord_1280714, baseEnd_1280714] using wordTrace_append hprefix tailTrace_1280714
  have hstable : (prefixWord ++ tailWord_1280714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280714).length < 2 ^ (prefixWord ++ tailWord_1280714).sum := by decide
  have hdescent : baseEnd_1280714 < baseStart_1280714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280838 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1280838 : Nat := 118140960795 + 1280838 * 2 ^ 59
def prefixEnd_1280838 : Nat := 4983230072969 + 3 ^ 40 * 1280838 * 2
def baseEnd_1280838 : Nat := 292304682019362199615351

theorem tailTrace_1280838 : CollatzResearch.WordTrace tailWord_1280838 prefixEnd_1280838 292304682019362199615351 := by
  unfold tailWord_1280838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459874991679692204998599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31143999822500100373303445 1459874991679692204998599)
  ·
    refine ⟨2189812487519538307497899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1459874991679692204998599 2189812487519538307497899)
    ·
      refine ⟨3284718731279307461246849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189812487519538307497899 3284718731279307461246849)
      ·
        refine ⟨2463539048459480595935137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284718731279307461246849 2463539048459480595935137)
        ·
          refine ⟨1847654286344610446951353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463539048459480595935137 1847654286344610446951353)
          ·
            refine ⟨1385740714758457835213515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847654286344610446951353 1385740714758457835213515)
            ·
              refine ⟨2078611072137686752820273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385740714758457835213515 2078611072137686752820273)
              ·
                refine ⟨1558958304103265064615205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078611072137686752820273 1558958304103265064615205)
                ·
                  refine ⟨292304682019362199615351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558958304103265064615205 292304682019362199615351)
                  ·
                    rfl

theorem cell21_1280838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1280838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280838 prefixEnd_1280838 := by exact prefixLift 1280838
  have htrace : WordTrace (prefixWord ++ tailWord_1280838) baseStart_1280838 baseEnd_1280838 := by
    simpa [prefixWord, tailWord_1280838, baseEnd_1280838] using wordTrace_append hprefix tailTrace_1280838
  have hstable : (prefixWord ++ tailWord_1280838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280838).length < 2 ^ (prefixWord ++ tailWord_1280838).sum := by decide
  have hdescent : baseEnd_1280838 < baseStart_1280838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280863 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 4]
def baseStart_1280863 : Nat := 118140960795 + 1280863 * 2 ^ 59
def prefixEnd_1280863 : Nat := 4983230072969 + 3 ^ 40 * 1280863 * 2
def baseEnd_1280863 : Nat := 292310387359967711698633

theorem tailTrace_1280863 : CollatzResearch.WordTrace tailWord_1280863 prefixEnd_1280863 292310387359967711698633 := by
  unfold tailWord_1280863
  simp only [CollatzResearch.WordTrace]
  refine ⟨46716911558659579829615243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31144607705773053219743495 46716911558659579829615243)
  ·
    refine ⟨70075367337989369744422865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46716911558659579829615243 70075367337989369744422865)
    ·
      refine ⟨52556525503492027308317149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70075367337989369744422865 52556525503492027308317149)
      ·
        refine ⟨19708697063809510240618931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52556525503492027308317149 19708697063809510240618931)
        ·
          refine ⟨29563045595714265360928397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19708697063809510240618931 29563045595714265360928397)
          ·
            refine ⟨11086142098392849510348149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29563045595714265360928397 11086142098392849510348149)
            ·
              refine ⟨1039325821724329641595139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11086142098392849510348149 1039325821724329641595139)
              ·
                refine ⟨1558988732586494462392709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039325821724329641595139 1558988732586494462392709)
                ·
                  refine ⟨292310387359967711698633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558988732586494462392709 292310387359967711698633)
                  ·
                    rfl

theorem cell21_1280863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4].length) (baseStart_1280863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280863 prefixEnd_1280863 := by exact prefixLift 1280863
  have htrace : WordTrace (prefixWord ++ tailWord_1280863) baseStart_1280863 baseEnd_1280863 := by
    simpa [prefixWord, tailWord_1280863, baseEnd_1280863] using wordTrace_append hprefix tailTrace_1280863
  have hstable : (prefixWord ++ tailWord_1280863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280863).length < 2 ^ (prefixWord ++ tailWord_1280863).sum := by decide
  have hdescent : baseEnd_1280863 < baseStart_1280863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280908 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_1280908 : Nat := 118140960795 + 1280908 * 2 ^ 59
def prefixEnd_1280908 : Nat := 4983230072969 + 3 ^ 40 * 1280908 * 2
def baseEnd_1280908 : Nat := 292320656973057633448541

theorem tailTrace_1280908 : CollatzResearch.WordTrace tailWord_1280908 prefixEnd_1280908 292320656973057633448541 := by
  unfold tailWord_1280908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23359276421748276257501689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31145701895664368343335585 23359276421748276257501689)
  ·
    refine ⟨17519457316311207193126267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23359276421748276257501689 17519457316311207193126267)
    ·
      refine ⟨26279185974466810789689401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17519457316311207193126267 26279185974466810789689401)
      ·
        refine ⟨19709389480850108092267051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26279185974466810789689401 19709389480850108092267051)
        ·
          refine ⟨29564084221275162138400577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709389480850108092267051 29564084221275162138400577)
          ·
            refine ⟨22173063165956371603800433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29564084221275162138400577 22173063165956371603800433)
            ·
              refine ⟨16629797374467278702850325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22173063165956371603800433 16629797374467278702850325)
              ·
                refine ⟨779521751928153689196109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16629797374467278702850325 779521751928153689196109)
                ·
                  refine ⟨292320656973057633448541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779521751928153689196109 292320656973057633448541)
                  ·
                    rfl

theorem cell21_1280908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_1280908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280908 prefixEnd_1280908 := by exact prefixLift 1280908
  have htrace : WordTrace (prefixWord ++ tailWord_1280908) baseStart_1280908 baseEnd_1280908 := by
    simpa [prefixWord, tailWord_1280908, baseEnd_1280908] using wordTrace_append hprefix tailTrace_1280908
  have hstable : (prefixWord ++ tailWord_1280908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280908).length < 2 ^ (prefixWord ++ tailWord_1280908).sum := by decide
  have hdescent : baseEnd_1280908 < baseStart_1280908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280914 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_1280914 : Nat := 118140960795 + 1280914 * 2 ^ 59
def prefixEnd_1280914 : Nat := 4983230072969 + 3 ^ 40 * 1280914 * 2
def baseEnd_1280914 : Nat := 292322026254802956348529

theorem tailTrace_1280914 : CollatzResearch.WordTrace tailWord_1280914 prefixEnd_1280914 292322026254802956348529 := by
  unfold tailWord_1280914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11679692920368703884930449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31145847787649877026481197 11679692920368703884930449)
  ·
    refine ⟨8759769690276527913697837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11679692920368703884930449 8759769690276527913697837)
    ·
      refine ⟨3284913633853697967636689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8759769690276527913697837 3284913633853697967636689)
      ·
        refine ⟨2463685225390273475727517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284913633853697967636689 2463685225390273475727517)
        ·
          refine ⟨923881959521352553397819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2463685225390273475727517 923881959521352553397819)
          ·
            refine ⟨1385822939282028830096729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923881959521352553397819 1385822939282028830096729)
            ·
              refine ⟨1039367204461521622572547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385822939282028830096729 1039367204461521622572547)
              ·
                refine ⟨1559050806692282433858821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039367204461521622572547 1559050806692282433858821)
                ·
                  refine ⟨292322026254802956348529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559050806692282433858821 292322026254802956348529)
                  ·
                    rfl

theorem cell21_1280914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_1280914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1280914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1280914 prefixEnd_1280914 := by exact prefixLift 1280914
  have htrace : WordTrace (prefixWord ++ tailWord_1280914) baseStart_1280914 baseEnd_1280914 := by
    simpa [prefixWord, tailWord_1280914, baseEnd_1280914] using wordTrace_append hprefix tailTrace_1280914
  have hstable : (prefixWord ++ tailWord_1280914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280914).length < 2 ^ (prefixWord ++ tailWord_1280914).sum := by decide
  have hdescent : baseEnd_1280914 < baseStart_1280914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281074 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1281074 : Nat := 118140960795 + 1281074 * 2 ^ 59
def prefixEnd_1281074 : Nat := 4983230072969 + 3 ^ 40 * 1281074 * 2
def baseEnd_1281074 : Nat := 292358540434678233681535

theorem tailTrace_1281074 : CollatzResearch.WordTrace tailWord_1281074 prefixEnd_1281074 292358540434678233681535 := by
  unfold tailWord_1281074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681151840223790716386569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31149738240596775243697517 11681151840223790716386569)
  ·
    refine ⟨8760863880167843037289927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11681151840223790716386569 8760863880167843037289927)
    ·
      refine ⟨13141295820251764555934891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8760863880167843037289927 13141295820251764555934891)
      ·
        refine ⟨19711943730377646833902337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13141295820251764555934891 19711943730377646833902337)
        ·
          refine ⟨14783957797783235125426753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19711943730377646833902337 14783957797783235125426753)
          ·
            refine ⟨11087968348337426344070065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14783957797783235125426753 11087968348337426344070065)
            ·
              refine ⟨8315976261253069758052549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11087968348337426344070065 8315976261253069758052549)
              ·
                refine ⟨1559245548984950579634853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8315976261253069758052549 1559245548984950579634853)
                ·
                  refine ⟨292358540434678233681535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559245548984950579634853 292358540434678233681535)
                  ·
                    rfl

theorem cell21_1281074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1281074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281074 prefixEnd_1281074 := by exact prefixLift 1281074
  have htrace : WordTrace (prefixWord ++ tailWord_1281074) baseStart_1281074 baseEnd_1281074 := by
    simpa [prefixWord, tailWord_1281074, baseEnd_1281074] using wordTrace_append hprefix tailTrace_1281074
  have hstable : (prefixWord ++ tailWord_1281074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281074).length < 2 ^ (prefixWord ++ tailWord_1281074).sum := by decide
  have hdescent : baseEnd_1281074 < baseStart_1281074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281088 : List Nat := [2, 1, 1, 2, 2, 3, 4, 6]
def baseStart_1281088 : Nat := 118140960795 + 1281088 * 2 ^ 59
def prefixEnd_1281088 : Nat := 4983230072969 + 3 ^ 40 * 1281088 * 2
def baseEnd_1281088 : Nat := 97453911808472440149391

theorem tailTrace_1281088 : CollatzResearch.WordTrace tailWord_1281088 prefixEnd_1281088 97453911808472440149391 := by
  unfold tailWord_1281088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23362558991422221628277959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31150078655229628837703945 23362558991422221628277959)
  ·
    refine ⟨35043838487133332442416939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23362558991422221628277959 35043838487133332442416939)
    ·
      refine ⟨52565757730699998663625409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35043838487133332442416939 52565757730699998663625409)
      ·
        refine ⟨39424318298024998997719057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52565757730699998663625409 39424318298024998997719057)
        ·
          refine ⟨29568238723518749248289293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39424318298024998997719057 29568238723518749248289293)
          ·
            refine ⟨11088089521319530968108485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29568238723518749248289293 11088089521319530968108485)
            ·
              refine ⟨2079016785247412056520341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11088089521319530968108485 2079016785247412056520341)
              ·
                refine ⟨97453911808472440149391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2079016785247412056520341 97453911808472440149391)
                ·
                  rfl

theorem cell21_1281088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_1281088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281088 prefixEnd_1281088 := by exact prefixLift 1281088
  have htrace : WordTrace (prefixWord ++ tailWord_1281088) baseStart_1281088 baseEnd_1281088 := by
    simpa [prefixWord, tailWord_1281088, baseEnd_1281088] using wordTrace_append hprefix tailTrace_1281088
  have hstable : (prefixWord ++ tailWord_1281088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281088).length < 2 ^ (prefixWord ++ tailWord_1281088).sum := by decide
  have hdescent : baseEnd_1281088 < baseStart_1281088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281128 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_1281128 : Nat := 118140960795 + 1281128 * 2 ^ 59
def prefixEnd_1281128 : Nat := 4983230072969 + 3 ^ 40 * 1281128 * 2
def baseEnd_1281128 : Nat := 292370863970386139781425

theorem tailTrace_1281128 : CollatzResearch.WordTrace tailWord_1281128 prefixEnd_1281128 292370863970386139781425 := by
  unfold tailWord_1281128
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363288451349765044006019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31151051268466353392008025 23363288451349765044006019)
  ·
    refine ⟨35044932677024647566009029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23363288451349765044006019 35044932677024647566009029)
    ·
      refine ⟨6570924876942121418626693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35044932677024647566009029 6570924876942121418626693)
      ·
        refine ⟨1232048414426647765992505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6570924876942121418626693 1232048414426647765992505)
        ·
          refine ⟨924036310819985824494379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232048414426647765992505 924036310819985824494379)
          ·
            refine ⟨1386054466229978736741569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924036310819985824494379 1386054466229978736741569)
            ·
              refine ⟨1039540849672484052556177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386054466229978736741569 1039540849672484052556177)
              ·
                refine ⟨779655637254363039417133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039540849672484052556177 779655637254363039417133)
                ·
                  refine ⟨292370863970386139781425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779655637254363039417133 292370863970386139781425)
                  ·
                    rfl

theorem cell21_1281128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_1281128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281128 prefixEnd_1281128 := by exact prefixLift 1281128
  have htrace : WordTrace (prefixWord ++ tailWord_1281128) baseStart_1281128 baseEnd_1281128 := by
    simpa [prefixWord, tailWord_1281128, baseEnd_1281128] using wordTrace_append hprefix tailTrace_1281128
  have hstable : (prefixWord ++ tailWord_1281128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281128).length < 2 ^ (prefixWord ++ tailWord_1281128).sum := by decide
  have hdescent : baseEnd_1281128 < baseStart_1281128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281136 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_1281136 : Nat := 118140960795 + 1281136 * 2 ^ 59
def prefixEnd_1281136 : Nat := 4983230072969 + 3 ^ 40 * 1281136 * 2
def baseEnd_1281136 : Nat := 292372689679379903648075

theorem tailTrace_1281136 : CollatzResearch.WordTrace tailWord_1281136 prefixEnd_1281136 292372689679379903648075 := by
  unfold tailWord_1281136
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363434343335273727151631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31151245791113698302868841 23363434343335273727151631)
  ·
    refine ⟨35045151515002910590727447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23363434343335273727151631 35045151515002910590727447)
    ·
      refine ⟨52567727272504365886091171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35045151515002910590727447 52567727272504365886091171)
      ·
        refine ⟨78851590908756548829136757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52567727272504365886091171 78851590908756548829136757)
        ·
          refine ⟨7392336647695926452731571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78851590908756548829136757 7392336647695926452731571)
          ·
            refine ⟨11088504971543889679097357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392336647695926452731571 11088504971543889679097357)
            ·
              refine ⟨4158189364328958629661509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11088504971543889679097357 4158189364328958629661509)
              ·
                refine ⟨779660505811679743061533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4158189364328958629661509 779660505811679743061533)
                ·
                  refine ⟨292372689679379903648075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779660505811679743061533 292372689679379903648075)
                  ·
                    rfl

theorem cell21_1281136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_1281136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281136 prefixEnd_1281136 := by exact prefixLift 1281136
  have htrace : WordTrace (prefixWord ++ tailWord_1281136) baseStart_1281136 baseEnd_1281136 := by
    simpa [prefixWord, tailWord_1281136, baseEnd_1281136] using wordTrace_append hprefix tailTrace_1281136
  have hstable : (prefixWord ++ tailWord_1281136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281136).length < 2 ^ (prefixWord ++ tailWord_1281136).sum := by decide
  have hdescent : baseEnd_1281136 < baseStart_1281136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281333 : List Nat := [1, 3, 3, 1, 2, 3, 3, 5]
def baseStart_1281333 : Nat := 118140960795 + 1281333 * 2 ^ 59
def prefixEnd_1281333 : Nat := 4983230072969 + 3 ^ 40 * 1281333 * 2
def baseEnd_1281333 : Nat := 97472549254450446288113

theorem tailTrace_1281333 : CollatzResearch.WordTrace tailWord_1281333 prefixEnd_1281333 97472549254450446288113 := by
  unfold tailWord_1281333
  simp only [CollatzResearch.WordTrace]
  refine ⟨46734053866956850099224653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31156035911304566732816435 46734053866956850099224653)
  ·
    refine ⟨17525270200108818787209245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46734053866956850099224653 17525270200108818787209245)
    ·
      refine ⟨6571976325040807045203467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17525270200108818787209245 6571976325040807045203467)
      ·
        refine ⟨9857964487561210567805201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571976325040807045203467 9857964487561210567805201)
        ·
          refine ⟨7393473365670907925853901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9857964487561210567805201 7393473365670907925853901)
          ·
            refine ⟨2772552512126590472195213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7393473365670907925853901 2772552512126590472195213)
            ·
              refine ⟨1039707192047471427073205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2772552512126590472195213 1039707192047471427073205)
              ·
                refine ⟨97472549254450446288113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1039707192047471427073205 97472549254450446288113)
                ·
                  rfl

theorem cell21_1281333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 5].length) (baseStart_1281333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281333 prefixEnd_1281333 := by exact prefixLift 1281333
  have htrace : WordTrace (prefixWord ++ tailWord_1281333) baseStart_1281333 baseEnd_1281333 := by
    simpa [prefixWord, tailWord_1281333, baseEnd_1281333] using wordTrace_append hprefix tailTrace_1281333
  have hstable : (prefixWord ++ tailWord_1281333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281333).length < 2 ^ (prefixWord ++ tailWord_1281333).sum := by decide
  have hdescent : baseEnd_1281333 < baseStart_1281333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281361 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_1281361 : Nat := 118140960795 + 1281361 * 2 ^ 59
def prefixEnd_1281361 : Nat := 4983230072969 + 3 ^ 40 * 1281361 * 2
def baseEnd_1281361 : Nat := 292424037744829512397615

theorem tailTrace_1281361 : CollatzResearch.WordTrace tailWord_1281361 prefixEnd_1281361 292424037744829512397615 := by
  unfold tailWord_1281361
  simp only [CollatzResearch.WordTrace]
  refine ⟨46735075110855410881243937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31156716740570273920829291 46735075110855410881243937)
  ·
    refine ⟨35051306333141558160932953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46735075110855410881243937 35051306333141558160932953)
    ·
      refine ⟨26288479749856168620699715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35051306333141558160932953 26288479749856168620699715)
      ·
        refine ⟨39432719624784252931049573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26288479749856168620699715 39432719624784252931049573)
        ·
          refine ⟨7393634929647047424571795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39432719624784252931049573 7393634929647047424571795)
          ·
            refine ⟨11090452394470571136857693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393634929647047424571795 11090452394470571136857693)
            ·
              refine ⟨4158919647926464176321635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11090452394470571136857693 4158919647926464176321635)
              ·
                refine ⟨6238379471889696264482453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158919647926464176321635 6238379471889696264482453)
                ·
                  refine ⟨292424037744829512397615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6238379471889696264482453 292424037744829512397615)
                  ·
                    rfl

theorem cell21_1281361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_1281361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281361 prefixEnd_1281361 := by exact prefixLift 1281361
  have htrace : WordTrace (prefixWord ++ tailWord_1281361) baseStart_1281361 baseEnd_1281361 := by
    simpa [prefixWord, tailWord_1281361, baseEnd_1281361] using wordTrace_append hprefix tailTrace_1281361
  have hstable : (prefixWord ++ tailWord_1281361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281361).length < 2 ^ (prefixWord ++ tailWord_1281361).sum := by decide
  have hdescent : baseEnd_1281361 < baseStart_1281361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281364 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1281364 : Nat := 118140960795 + 1281364 * 2 ^ 59
def prefixEnd_1281364 : Nat := 4983230072969 + 3 ^ 40 * 1281364 * 2
def baseEnd_1281364 : Nat := 292424722385702173847609

theorem tailTrace_1281364 : CollatzResearch.WordTrace tailWord_1281364 prefixEnd_1281364 292424722385702173847609 := by
  unfold tailWord_1281364
  simp only [CollatzResearch.WordTrace]
  refine ⟨23367592264922271196801573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31156789686563028262402097 23367592264922271196801573)
  ·
    refine ⟨4381423549672925849400295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23367592264922271196801573 4381423549672925849400295)
    ·
      refine ⟨6572135324509388774100443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381423549672925849400295 6572135324509388774100443)
      ·
        refine ⟨9858202986764083161150665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6572135324509388774100443 9858202986764083161150665)
        ·
          refine ⟨7393652240073062370862999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9858202986764083161150665 7393652240073062370862999)
          ·
            refine ⟨11090478360109593556294499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393652240073062370862999 11090478360109593556294499)
            ·
              refine ⟨16635717540164390334441749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11090478360109593556294499 16635717540164390334441749)
              ·
                refine ⟨779799259695205796926957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16635717540164390334441749 779799259695205796926957)
                ·
                  refine ⟨292424722385702173847609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779799259695205796926957 292424722385702173847609)
                  ·
                    rfl

theorem cell21_1281364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1281364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281364 prefixEnd_1281364 := by exact prefixLift 1281364
  have htrace : WordTrace (prefixWord ++ tailWord_1281364) baseStart_1281364 baseEnd_1281364 := by
    simpa [prefixWord, tailWord_1281364, baseEnd_1281364] using wordTrace_append hprefix tailTrace_1281364
  have hstable : (prefixWord ++ tailWord_1281364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281364).length < 2 ^ (prefixWord ++ tailWord_1281364).sum := by decide
  have hdescent : baseEnd_1281364 < baseStart_1281364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281375 : List Nat := [1, 1, 2, 3, 1, 2, 1, 10]
def baseStart_1281375 : Nat := 118140960795 + 1281375 * 2 ^ 59
def prefixEnd_1281375 : Nat := 4983230072969 + 3 ^ 40 * 1281375 * 2
def baseEnd_1281375 : Nat := 97475744245189533054751

theorem tailTrace_1281375 : CollatzResearch.WordTrace tailWord_1281375 prefixEnd_1281375 97475744245189533054751 := by
  unfold tailWord_1281375
  simp only [CollatzResearch.WordTrace]
  refine ⟨46735585732804691272253579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31157057155203127514835719 46735585732804691272253579)
  ·
    refine ⟨70103378599207036908380369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46735585732804691272253579 70103378599207036908380369)
    ·
      refine ⟨52577533949405277681285277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70103378599207036908380369 52577533949405277681285277)
      ·
        refine ⟨19716575231026979130481979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52577533949405277681285277 19716575231026979130481979)
        ·
          refine ⟨29574862846540468695722969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19716575231026979130481979 29574862846540468695722969)
          ·
            refine ⟨22181147134905351521792227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29574862846540468695722969 22181147134905351521792227)
            ·
              refine ⟨33271720702358027282688341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22181147134905351521792227 33271720702358027282688341)
              ·
                refine ⟨97475744245189533054751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33271720702358027282688341 97475744245189533054751)
                ·
                  rfl

theorem cell21_1281375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_1281375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281375 prefixEnd_1281375 := by exact prefixLift 1281375
  have htrace : WordTrace (prefixWord ++ tailWord_1281375) baseStart_1281375 baseEnd_1281375 := by
    simpa [prefixWord, tailWord_1281375, baseEnd_1281375] using wordTrace_append hprefix tailTrace_1281375
  have hstable : (prefixWord ++ tailWord_1281375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281375).length < 2 ^ (prefixWord ++ tailWord_1281375).sum := by decide
  have hdescent : baseEnd_1281375 < baseStart_1281375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281409 : List Nat := [1, 2, 4, 3, 2, 2, 7]
def baseStart_1281409 : Nat := 118140960795 + 1281409 * 2 ^ 59
def prefixEnd_1281409 : Nat := 4983230072969 + 3 ^ 40 * 1281409 * 2
def baseEnd_1281409 : Nat := 32492776888754677288613

theorem tailTrace_1281409 : CollatzResearch.WordTrace tailWord_1281409 prefixEnd_1281409 32492776888754677288613 := by
  unfold tailWord_1281409
  simp only [CollatzResearch.WordTrace]
  refine ⟨46736825814681515078991281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31157883876454343385994187 46736825814681515078991281)
  ·
    refine ⟨35052619361011136309243461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46736825814681515078991281 35052619361011136309243461)
    ·
      refine ⟨6572366130189588057983149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35052619361011136309243461 6572366130189588057983149)
      ·
        refine ⟨2464637298821095521743681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6572366130189588057983149 2464637298821095521743681)
        ·
          refine ⟨1848477974115821641307761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464637298821095521743681 1848477974115821641307761)
          ·
            refine ⟨1386358480586866230980821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848477974115821641307761 1386358480586866230980821)
            ·
              refine ⟨32492776888754677288613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1386358480586866230980821 32492776888754677288613)
              ·
                rfl

theorem cell21_1281409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 7].length) (baseStart_1281409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281409 prefixEnd_1281409 := by exact prefixLift 1281409
  have htrace : WordTrace (prefixWord ++ tailWord_1281409) baseStart_1281409 baseEnd_1281409 := by
    simpa [prefixWord, tailWord_1281409, baseEnd_1281409] using wordTrace_append hprefix tailTrace_1281409
  have hstable : (prefixWord ++ tailWord_1281409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281409).length < 2 ^ (prefixWord ++ tailWord_1281409).sum := by decide
  have hdescent : baseEnd_1281409 < baseStart_1281409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281426 : List Nat := [3, 2, 3, 3, 1, 1, 2, 6]
def baseStart_1281426 : Nat := 118140960795 + 1281426 * 2 ^ 59
def prefixEnd_1281426 : Nat := 4983230072969 + 3 ^ 40 * 1281426 * 2
def baseEnd_1281426 : Nat := 97479623876801281271383

theorem tailTrace_1281426 : CollatzResearch.WordTrace tailWord_1281426 prefixEnd_1281426 97479623876801281271383 := by
  unfold tailWord_1281426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11684361463904981745590033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31158297237079951321573421 11684361463904981745590033)
  ·
    refine ⟨8763271097928736309192525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11684361463904981745590033 8763271097928736309192525)
    ·
      refine ⟨3286226661723276115947197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8763271097928736309192525 3286226661723276115947197)
      ·
        refine ⟨1232334998146228543480199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3286226661723276115947197 1232334998146228543480199)
        ·
          refine ⟨1848502497219342815220299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232334998146228543480199 1848502497219342815220299)
          ·
            refine ⟨2772753745829014222830449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848502497219342815220299 2772753745829014222830449)
            ·
              refine ⟨2079565309371760667122837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772753745829014222830449 2079565309371760667122837)
              ·
                refine ⟨97479623876801281271383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2079565309371760667122837 97479623876801281271383)
                ·
                  rfl

theorem cell21_1281426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_1281426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281426 prefixEnd_1281426 := by exact prefixLift 1281426
  have htrace : WordTrace (prefixWord ++ tailWord_1281426) baseStart_1281426 baseEnd_1281426 := by
    simpa [prefixWord, tailWord_1281426, baseEnd_1281426] using wordTrace_append hprefix tailTrace_1281426
  have hstable : (prefixWord ++ tailWord_1281426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281426).length < 2 ^ (prefixWord ++ tailWord_1281426).sum := by decide
  have hdescent : baseEnd_1281426 < baseStart_1281426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281468 : List Nat := [2, 2, 2, 4, 2, 9]
def baseStart_1281468 : Nat := 118140960795 + 1281468 * 2 ^ 59
def prefixEnd_1281468 : Nat := 4983230072969 + 3 ^ 40 * 1281468 * 2
def baseEnd_1281468 : Nat := 10831424318615596448669

theorem tailTrace_1281468 : CollatzResearch.WordTrace tailWord_1281468 prefixEnd_1281468 10831424318615596448669 := by
  unfold tailWord_1281468
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369488860733884077694529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31159318480978512103592705 23369488860733884077694529)
  ·
    refine ⟨17527116645550413058270897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23369488860733884077694529 17527116645550413058270897)
    ·
      refine ⟨13145337484162809793703173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17527116645550413058270897 13145337484162809793703173)
      ·
        refine ⟨2464750778280526836319345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13145337484162809793703173 2464750778280526836319345)
        ·
          refine ⟨1848563083710395127239509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464750778280526836319345 1848563083710395127239509)
          ·
            refine ⟨10831424318615596448669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1848563083710395127239509 10831424318615596448669)
            ·
              rfl

theorem cell21_1281468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 9].length) (baseStart_1281468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281468 prefixEnd_1281468 := by exact prefixLift 1281468
  have htrace : WordTrace (prefixWord ++ tailWord_1281468) baseStart_1281468 baseEnd_1281468 := by
    simpa [prefixWord, tailWord_1281468, baseEnd_1281468] using wordTrace_append hprefix tailTrace_1281468
  have hstable : (prefixWord ++ tailWord_1281468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281468).length < 2 ^ (prefixWord ++ tailWord_1281468).sum := by decide
  have hdescent : baseEnd_1281468 < baseStart_1281468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281547 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 4]
def baseStart_1281547 : Nat := 118140960795 + 1281547 * 2 ^ 59
def prefixEnd_1281547 : Nat := 4983230072969 + 3 ^ 40 * 1281547 * 2
def baseEnd_1281547 : Nat := 292466485478934522297235

theorem tailTrace_1281547 : CollatzResearch.WordTrace tailWord_1281547 prefixEnd_1281547 292466485478934522297235 := by
  unfold tailWord_1281547
  simp only [CollatzResearch.WordTrace]
  refine ⟨46741859088181564647514895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31161239392121043098343263 46741859088181564647514895)
  ·
    refine ⟨70112788632272346971272343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46741859088181564647514895 70112788632272346971272343)
    ·
      refine ⟨105169182948408520456908515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70112788632272346971272343 105169182948408520456908515)
      ·
        refine ⟨157753774422612780685362773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105169182948408520456908515 157753774422612780685362773)
        ·
          refine ⟨1848677044014993523656595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 157753774422612780685362773 1848677044014993523656595)
          ·
            refine ⟨2773015566022490285484893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848677044014993523656595 2773015566022490285484893)
            ·
              refine ⟨1039880837258433857056835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2773015566022490285484893 1039880837258433857056835)
              ·
                refine ⟨1559821255887650785585253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039880837258433857056835 1559821255887650785585253)
                ·
                  refine ⟨292466485478934522297235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559821255887650785585253 292466485478934522297235)
                  ·
                    rfl

theorem cell21_1281547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4].length) (baseStart_1281547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281547 prefixEnd_1281547 := by exact prefixLift 1281547
  have htrace : WordTrace (prefixWord ++ tailWord_1281547) baseStart_1281547 baseEnd_1281547 := by
    simpa [prefixWord, tailWord_1281547, baseEnd_1281547] using wordTrace_append hprefix tailTrace_1281547
  have hstable : (prefixWord ++ tailWord_1281547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281547).length < 2 ^ (prefixWord ++ tailWord_1281547).sum := by decide
  have hdescent : baseEnd_1281547 < baseStart_1281547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281589 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_1281589 : Nat := 118140960795 + 1281589 * 2 ^ 59
def prefixEnd_1281589 : Nat := 4983230072969 + 3 ^ 40 * 1281589 * 2
def baseEnd_1281589 : Nat := 292476070451151782597149

theorem tailTrace_1281589 : CollatzResearch.WordTrace tailWord_1281589 prefixEnd_1281589 292476070451151782597149 := by
  unfold tailWord_1281589
  simp only [CollatzResearch.WordTrace]
  refine ⟨46743390954029405820543821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31162260636019603880362547 46743390954029405820543821)
  ·
    refine ⟨17528771607761027182703933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46743390954029405820543821 17528771607761027182703933)
    ·
      refine ⟨6573289352910385193513975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17528771607761027182703933 6573289352910385193513975)
      ·
        refine ⟨9859934029365577790270963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6573289352910385193513975 9859934029365577790270963)
        ·
          refine ⟨14789901044048366685406445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9859934029365577790270963 14789901044048366685406445)
          ·
            refine ⟨5546212891518137507027417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14789901044048366685406445 5546212891518137507027417)
            ·
              refine ⟨4159659668638603130270563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546212891518137507027417 4159659668638603130270563)
              ·
                refine ⟨6239489502957904695405845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159659668638603130270563 6239489502957904695405845)
                ·
                  refine ⟨292476070451151782597149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6239489502957904695405845 292476070451151782597149)
                  ·
                    rfl

theorem cell21_1281589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_1281589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281589 prefixEnd_1281589 := by exact prefixLift 1281589
  have htrace : WordTrace (prefixWord ++ tailWord_1281589) baseStart_1281589 baseEnd_1281589 := by
    simpa [prefixWord, tailWord_1281589, baseEnd_1281589] using wordTrace_append hprefix tailTrace_1281589
  have hstable : (prefixWord ++ tailWord_1281589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281589).length < 2 ^ (prefixWord ++ tailWord_1281589).sum := by decide
  have hdescent : baseEnd_1281589 < baseStart_1281589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281761 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 3]
def baseStart_1281761 : Nat := 118140960795 + 1281761 * 2 ^ 59
def prefixEnd_1281761 : Nat := 4983230072969 + 3 ^ 40 * 1281761 * 2
def baseEnd_1281761 : Nat := 292515323194517705730131

theorem tailTrace_1281761 : CollatzResearch.WordTrace tailWord_1281761 prefixEnd_1281761 292515323194517705730131 := by
  unfold tailWord_1281761
  simp only [CollatzResearch.WordTrace]
  refine ⟨46749664309406279195805137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31166442872937519463870091 46749664309406279195805137)
  ·
    refine ⟨35062248232054709396853853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46749664309406279195805137 35062248232054709396853853)
    ·
      refine ⟨13148343087020516023820195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35062248232054709396853853 13148343087020516023820195)
      ·
        refine ⟨19722514630530774035730293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13148343087020516023820195 19722514630530774035730293)
        ·
          refine ⟨1848985746612260065849715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19722514630530774035730293 1848985746612260065849715)
          ·
            refine ⟨2773478619918390098774573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848985746612260065849715 2773478619918390098774573)
            ·
              refine ⟨1040054482469396287040465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2773478619918390098774573 1040054482469396287040465)
              ·
                refine ⟨780040861852047215280349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040054482469396287040465 780040861852047215280349)
                ·
                  refine ⟨292515323194517705730131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780040861852047215280349 292515323194517705730131)
                  ·
                    rfl

theorem cell21_1281761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_1281761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281761 prefixEnd_1281761 := by exact prefixLift 1281761
  have htrace : WordTrace (prefixWord ++ tailWord_1281761) baseStart_1281761 baseEnd_1281761 := by
    simpa [prefixWord, tailWord_1281761, baseEnd_1281761] using wordTrace_append hprefix tailTrace_1281761
  have hstable : (prefixWord ++ tailWord_1281761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281761).length < 2 ^ (prefixWord ++ tailWord_1281761).sum := by decide
  have hdescent : baseEnd_1281761 < baseStart_1281761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281812 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1281812 : Nat := 118140960795 + 1281812 * 2 ^ 59
def prefixEnd_1281812 : Nat := 4983230072969 + 3 ^ 40 * 1281812 * 2
def baseEnd_1281812 : Nat := 292526962089352950380027

theorem tailTrace_1281812 : CollatzResearch.WordTrace tailWord_1281812 prefixEnd_1281812 292526962089352950380027 := by
  unfold tailWord_1281812
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375762216110757452955845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31167682954814343270607793 23375762216110757452955845)
  ·
    refine ⟨4382955415520767022429221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23375762216110757452955845 4382955415520767022429221)
    ·
      refine ⟨821804140410143816705479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4382955415520767022429221 821804140410143816705479)
      ·
        refine ⟨1232706210615215725058219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821804140410143816705479 1232706210615215725058219)
        ·
          refine ⟨1849059315922823587587329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232706210615215725058219 1849059315922823587587329)
          ·
            refine ⟨1386794486942117690690497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849059315922823587587329 1386794486942117690690497)
            ·
              refine ⟨1040095865206588268017873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386794486942117690690497 1040095865206588268017873)
              ·
                refine ⟨780071898904941201013405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040095865206588268017873 780071898904941201013405)
                ·
                  refine ⟨292526962089352950380027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780071898904941201013405 292526962089352950380027)
                  ·
                    rfl

theorem cell21_1281812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1281812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281812 prefixEnd_1281812 := by exact prefixLift 1281812
  have htrace : WordTrace (prefixWord ++ tailWord_1281812) baseStart_1281812 baseEnd_1281812 := by
    simpa [prefixWord, tailWord_1281812, baseEnd_1281812] using wordTrace_append hprefix tailTrace_1281812
  have hstable : (prefixWord ++ tailWord_1281812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281812).length < 2 ^ (prefixWord ++ tailWord_1281812).sum := by decide
  have hdescent : baseEnd_1281812 < baseStart_1281812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281848 : List Nat := [2, 1, 2, 1, 3, 4, 3, 5]
def baseStart_1281848 : Nat := 118140960795 + 1281848 * 2 ^ 59
def prefixEnd_1281848 : Nat := 4983230072969 + 3 ^ 40 * 1281848 * 2
def baseEnd_1281848 : Nat := 97511725926608295926651

theorem tailTrace_1281848 : CollatzResearch.WordTrace tailWord_1281848 prefixEnd_1281848 97511725926608295926651 := by
  unfold tailWord_1281848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376418730045546527111099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31168558306727395369481465 23376418730045546527111099)
  ·
    refine ⟨35064628095068319790666649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23376418730045546527111099 35064628095068319790666649)
    ·
      refine ⟨26298471071301239842999987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35064628095068319790666649 26298471071301239842999987)
      ·
        refine ⟨39447706606951859764499981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26298471071301239842999987 39447706606951859764499981)
        ·
          refine ⟨14792889977606947411687493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39447706606951859764499981 14792889977606947411687493)
          ·
            refine ⟨2773666870801302639691405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14792889977606947411687493 2773666870801302639691405)
            ·
              refine ⟨1040125076550488489884277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2773666870801302639691405 1040125076550488489884277)
              ·
                refine ⟨97511725926608295926651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1040125076550488489884277 97511725926608295926651)
                ·
                  rfl

theorem cell21_1281848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_1281848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281848 prefixEnd_1281848 := by exact prefixLift 1281848
  have htrace : WordTrace (prefixWord ++ tailWord_1281848) baseStart_1281848 baseEnd_1281848 := by
    simpa [prefixWord, tailWord_1281848, baseEnd_1281848] using wordTrace_append hprefix tailTrace_1281848
  have hstable : (prefixWord ++ tailWord_1281848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281848).length < 2 ^ (prefixWord ++ tailWord_1281848).sum := by decide
  have hdescent : baseEnd_1281848 < baseStart_1281848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281879 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_1281879 : Nat := 118140960795 + 1281879 * 2 ^ 59
def prefixEnd_1281879 : Nat := 4983230072969 + 3 ^ 40 * 1281879 * 2
def baseEnd_1281879 : Nat := 292542252402175722763223

theorem tailTrace_1281879 : CollatzResearch.WordTrace tailWord_1281879 prefixEnd_1281879 292542252402175722763223 := by
  unfold tailWord_1281879
  simp only [CollatzResearch.WordTrace]
  refine ⟨46753968122978785348600691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31169312081985856899067127 46753968122978785348600691)
  ·
    refine ⟨70130952184468178022901037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46753968122978785348600691 70130952184468178022901037)
    ·
      refine ⟨26299107069175566758587889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70130952184468178022901037 26299107069175566758587889)
      ·
        refine ⟨19724330301881675068940917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26299107069175566758587889 19724330301881675068940917)
        ·
          refine ⟨1849155965801407037713211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19724330301881675068940917 1849155965801407037713211)
          ·
            refine ⟨2773733948702110556569817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849155965801407037713211 2773733948702110556569817)
            ·
              refine ⟨2080300461526582917427363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773733948702110556569817 2080300461526582917427363)
              ·
                refine ⟨3120450692289874376141045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080300461526582917427363 3120450692289874376141045)
                ·
                  refine ⟨292542252402175722763223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3120450692289874376141045 292542252402175722763223)
                  ·
                    rfl

theorem cell21_1281879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_1281879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281879 prefixEnd_1281879 := by exact prefixLift 1281879
  have htrace : WordTrace (prefixWord ++ tailWord_1281879) baseStart_1281879 baseEnd_1281879 := by
    simpa [prefixWord, tailWord_1281879, baseEnd_1281879] using wordTrace_append hprefix tailTrace_1281879
  have hstable : (prefixWord ++ tailWord_1281879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281879).length < 2 ^ (prefixWord ++ tailWord_1281879).sum := by decide
  have hdescent : baseEnd_1281879 < baseStart_1281879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281944 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_1281944 : Nat := 118140960795 + 1281944 * 2 ^ 59
def prefixEnd_1281944 : Nat := 4983230072969 + 3 ^ 40 * 1281944 * 2
def baseEnd_1281944 : Nat := 292557086287750054179757

theorem tailTrace_1281944 : CollatzResearch.WordTrace tailWord_1281944 prefixEnd_1281944 292557086287750054179757 := by
  unfold tailWord_1281944
  simp only [CollatzResearch.WordTrace]
  refine ⟨23378169433871650724858443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31170892578495534299811257 23378169433871650724858443)
  ·
    refine ⟨35067254150807476087287665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23378169433871650724858443 35067254150807476087287665)
    ·
      refine ⟨26300440613105607065465749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35067254150807476087287665 26300440613105607065465749)
      ·
        refine ⟨1232833153739325331193707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26300440613105607065465749 1232833153739325331193707)
        ·
          refine ⟨1849249730608987996790561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232833153739325331193707 1849249730608987996790561)
          ·
            refine ⟨1386937297956740997592921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849249730608987996790561 1386937297956740997592921)
            ·
              refine ⟨1040202973467555748194691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386937297956740997592921 1040202973467555748194691)
              ·
                refine ⟨1560304460201333622292037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040202973467555748194691 1560304460201333622292037)
                ·
                  refine ⟨292557086287750054179757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560304460201333622292037 292557086287750054179757)
                  ·
                    rfl

theorem cell21_1281944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_1281944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1281944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1281944 prefixEnd_1281944 := by exact prefixLift 1281944
  have htrace : WordTrace (prefixWord ++ tailWord_1281944) baseStart_1281944 baseEnd_1281944 := by
    simpa [prefixWord, tailWord_1281944, baseEnd_1281944] using wordTrace_append hprefix tailTrace_1281944
  have hstable : (prefixWord ++ tailWord_1281944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281944).length < 2 ^ (prefixWord ++ tailWord_1281944).sum := by decide
  have hdescent : baseEnd_1281944 < baseStart_1281944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282031 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 3]
def baseStart_1282031 : Nat := 118140960795 + 1282031 * 2 ^ 59
def prefixEnd_1282031 : Nat := 4983230072969 + 3 ^ 40 * 1282031 * 2
def baseEnd_1282031 : Nat := 292576940873057236229579

theorem tailTrace_1282031 : CollatzResearch.WordTrace tailWord_1282031 prefixEnd_1282031 292576940873057236229579 := by
  unfold tailWord_1282031
  simp only [CollatzResearch.WordTrace]
  refine ⟨46759512018428115308133947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31173008012285410205422631 46759512018428115308133947)
  ·
    refine ⟨70139268027642172962200921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46759512018428115308133947 70139268027642172962200921)
    ·
      refine ⟨52604451020731629721650691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70139268027642172962200921 52604451020731629721650691)
      ·
        refine ⟨78906676531097444582476037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52604451020731629721650691 78906676531097444582476037)
        ·
          refine ⟨14795001849580770859214257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78906676531097444582476037 14795001849580770859214257)
          ·
            refine ⟨11096251387185578144410693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14795001849580770859214257 11096251387185578144410693)
            ·
              refine ⟨2080547135097295902077005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11096251387185578144410693 2080547135097295902077005)
              ·
                refine ⟨780205175661485963278877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2080547135097295902077005 780205175661485963278877)
                ·
                  refine ⟨292576940873057236229579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780205175661485963278877 292576940873057236229579)
                  ·
                    rfl

theorem cell21_1282031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3].length) (baseStart_1282031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282031 prefixEnd_1282031 := by exact prefixLift 1282031
  have htrace : WordTrace (prefixWord ++ tailWord_1282031) baseStart_1282031 baseEnd_1282031 := by
    simpa [prefixWord, tailWord_1282031, baseEnd_1282031] using wordTrace_append hprefix tailTrace_1282031
  have hstable : (prefixWord ++ tailWord_1282031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282031).length < 2 ^ (prefixWord ++ tailWord_1282031).sum := by decide
  have hdescent : baseEnd_1282031 < baseStart_1282031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282045 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1282045 : Nat := 118140960795 + 1282045 * 2 ^ 59
def prefixEnd_1282045 : Nat := 4983230072969 + 3 ^ 40 * 1282045 * 2
def baseEnd_1282045 : Nat := 292580135863796322996217

theorem tailTrace_1282045 : CollatzResearch.WordTrace tailWord_1282045 prefixEnd_1282045 292580135863796322996217 := by
  unfold tailWord_1282045
  simp only [CollatzResearch.WordTrace]
  refine ⟨46760022640377395699143589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31173348426918263799429059 46760022640377395699143589)
  ·
    refine ⟨8767504245070761693589423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46760022640377395699143589 8767504245070761693589423)
    ·
      refine ⟨13151256367606142540384135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8767504245070761693589423 13151256367606142540384135)
      ·
        refine ⟨19726884551409213810576203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13151256367606142540384135 19726884551409213810576203)
        ·
          refine ⟨29590326827113820715864305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19726884551409213810576203 29590326827113820715864305)
          ·
            refine ⟨22192745120335365536898229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29590326827113820715864305 22192745120335365536898229)
            ·
              refine ⟨2080569855031440519084209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22192745120335365536898229 2080569855031440519084209)
              ·
                refine ⟨1560427391273580389313157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080569855031440519084209 1560427391273580389313157)
                ·
                  refine ⟨292580135863796322996217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560427391273580389313157 292580135863796322996217)
                  ·
                    rfl

theorem cell21_1282045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1282045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282045 prefixEnd_1282045 := by exact prefixLift 1282045
  have htrace : WordTrace (prefixWord ++ tailWord_1282045) baseStart_1282045 baseEnd_1282045 := by
    simpa [prefixWord, tailWord_1282045, baseEnd_1282045] using wordTrace_append hprefix tailTrace_1282045
  have hstable : (prefixWord ++ tailWord_1282045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282045).length < 2 ^ (prefixWord ++ tailWord_1282045).sum := by decide
  have hdescent : baseEnd_1282045 < baseStart_1282045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282054 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1282054 : Nat := 118140960795 + 1282054 * 2 ^ 59
def prefixEnd_1282054 : Nat := 4983230072969 + 3 ^ 40 * 1282054 * 2
def baseEnd_1282054 : Nat := 292582189786414307346199

theorem tailTrace_1282054 : CollatzResearch.WordTrace tailWord_1282054 prefixEnd_1282054 292582189786414307346199 := by
  unfold tailWord_1282054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461260965542024694881913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31173567264896526824147477 1461260965542024694881913)
  ·
    refine ⟨1095945724156518521161435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1461260965542024694881913 1095945724156518521161435)
    ·
      refine ⟨1643918586234777781742153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095945724156518521161435 1643918586234777781742153)
      ·
        refine ⟨1232938939676083336306615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1643918586234777781742153 1232938939676083336306615)
        ·
          refine ⟨1849408409514125004459923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232938939676083336306615 1849408409514125004459923)
          ·
            refine ⟨2774112614271187506689885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849408409514125004459923 2774112614271187506689885)
            ·
              refine ⟨1040292230351695315008707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2774112614271187506689885 1040292230351695315008707)
              ·
                refine ⟨1560438345527542972513061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040292230351695315008707 1560438345527542972513061)
                ·
                  refine ⟨292582189786414307346199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560438345527542972513061 292582189786414307346199)
                  ·
                    rfl

theorem cell21_1282054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1282054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282054 prefixEnd_1282054 := by exact prefixLift 1282054
  have htrace : WordTrace (prefixWord ++ tailWord_1282054) baseStart_1282054 baseEnd_1282054 := by
    simpa [prefixWord, tailWord_1282054, baseEnd_1282054] using wordTrace_append hprefix tailTrace_1282054
  have hstable : (prefixWord ++ tailWord_1282054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282054).length < 2 ^ (prefixWord ++ tailWord_1282054).sum := by decide
  have hdescent : baseEnd_1282054 < baseStart_1282054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282062 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1282062 : Nat := 118140960795 + 1282062 * 2 ^ 59
def prefixEnd_1282062 : Nat := 4983230072969 + 3 ^ 40 * 1282062 * 2
def baseEnd_1282062 : Nat := 292584015495408071212849

theorem tailTrace_1282062 : CollatzResearch.WordTrace tailWord_1282062 prefixEnd_1282062 292584015495408071212849 := by
  unfold tailWord_1282062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845080335164475950314055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31173761787543871735008293 5845080335164475950314055)
  ·
    refine ⟨8767620502746713925471083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5845080335164475950314055 8767620502746713925471083)
    ·
      refine ⟨13151430754120070888206625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8767620502746713925471083 13151430754120070888206625)
      ·
        refine ⟨9863573065590053166154969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13151430754120070888206625 9863573065590053166154969)
        ·
          refine ⟨7397679799192539874616227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9863573065590053166154969 7397679799192539874616227)
          ·
            refine ⟨11096519698788809811924341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7397679799192539874616227 11096519698788809811924341)
            ·
              refine ⟨1040298721761450919867907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11096519698788809811924341 1040298721761450919867907)
              ·
                refine ⟨1560448082642176379801861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040298721761450919867907 1560448082642176379801861)
                ·
                  refine ⟨292584015495408071212849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560448082642176379801861 292584015495408071212849)
                  ·
                    rfl

theorem cell21_1282062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1282062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282062 prefixEnd_1282062 := by exact prefixLift 1282062
  have htrace : WordTrace (prefixWord ++ tailWord_1282062) baseStart_1282062 baseEnd_1282062 := by
    simpa [prefixWord, tailWord_1282062, baseEnd_1282062] using wordTrace_append hprefix tailTrace_1282062
  have hstable : (prefixWord ++ tailWord_1282062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282062).length < 2 ^ (prefixWord ++ tailWord_1282062).sum := by decide
  have hdescent : baseEnd_1282062 < baseStart_1282062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282076 : List Nat := [2, 2, 3, 1, 3, 1, 4, 5]
def baseStart_1282076 : Nat := 118140960795 + 1282076 * 2 ^ 59
def prefixEnd_1282076 : Nat := 4983230072969 + 3 ^ 40 * 1282076 * 2
def baseEnd_1282076 : Nat := 97529070162049052659829

theorem tailTrace_1282076 : CollatzResearch.WordTrace tailWord_1282076 prefixEnd_1282076 97529070162049052659829 := by
  unfold tailWord_1282076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23380576651632543996761041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31174102202176725329014721 23380576651632543996761041)
  ·
    refine ⟨17535432488724407997570781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23380576651632543996761041 17535432488724407997570781)
    ·
      refine ⟨6575787183271652999089043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17535432488724407997570781 6575787183271652999089043)
      ·
        refine ⟨9863680774907479498633565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575787183271652999089043 9863680774907479498633565)
        ·
          refine ⟨3698880290590304811987587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9863680774907479498633565 3698880290590304811987587)
          ·
            refine ⟨5548320435885457217981381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698880290590304811987587 5548320435885457217981381)
            ·
              refine ⟨1040310081728523228371509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5548320435885457217981381 1040310081728523228371509)
              ·
                refine ⟨97529070162049052659829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1040310081728523228371509 97529070162049052659829)
                ·
                  rfl

theorem cell21_1282076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_1282076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282076 prefixEnd_1282076 := by exact prefixLift 1282076
  have htrace : WordTrace (prefixWord ++ tailWord_1282076) baseStart_1282076 baseEnd_1282076 := by
    simpa [prefixWord, tailWord_1282076, baseEnd_1282076] using wordTrace_append hprefix tailTrace_1282076
  have hstable : (prefixWord ++ tailWord_1282076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282076).length < 2 ^ (prefixWord ++ tailWord_1282076).sum := by decide
  have hdescent : baseEnd_1282076 < baseStart_1282076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282200 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_1282200 : Nat := 118140960795 + 1282200 * 2 ^ 59
def prefixEnd_1282200 : Nat := 4983230072969 + 3 ^ 40 * 1282200 * 2
def baseEnd_1282200 : Nat := 292615508975550497912567

theorem tailTrace_1282200 : CollatzResearch.WordTrace tailWord_1282200 prefixEnd_1282200 292615508975550497912567 := by
  unfold tailWord_1282200
  simp only [CollatzResearch.WordTrace]
  refine ⟨23382837977407928585518027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31177117303210571447357369 23382837977407928585518027)
  ·
    refine ⟨35074256966111892878277041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23382837977407928585518027 35074256966111892878277041)
    ·
      refine ⟨26305692724583919658707781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35074256966111892878277041 26305692724583919658707781)
      ·
        refine ⟨4932317385859484936007709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26305692724583919658707781 4932317385859484936007709)
        ·
          refine ⟨1849619019697306851002891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4932317385859484936007709 1849619019697306851002891)
          ·
            refine ⟨2774428529545960276504337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849619019697306851002891 2774428529545960276504337)
            ·
              refine ⟨2080821397159470207378253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774428529545960276504337 2080821397159470207378253)
              ·
                refine ⟨780308023934801327766845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2080821397159470207378253 780308023934801327766845)
                ·
                  refine ⟨292615508975550497912567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780308023934801327766845 292615508975550497912567)
                  ·
                    rfl

theorem cell21_1282200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_1282200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282200 prefixEnd_1282200 := by exact prefixLift 1282200
  have htrace : WordTrace (prefixWord ++ tailWord_1282200) baseStart_1282200 baseEnd_1282200 := by
    simpa [prefixWord, tailWord_1282200, baseEnd_1282200] using wordTrace_append hprefix tailTrace_1282200
  have hstable : (prefixWord ++ tailWord_1282200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282200).length < 2 ^ (prefixWord ++ tailWord_1282200).sum := by decide
  have hdescent : baseEnd_1282200 < baseStart_1282200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282287 : List Nat := [1, 1, 2, 1, 6, 2, 2, 6]
def baseStart_1282287 : Nat := 118140960795 + 1282287 * 2 ^ 59
def prefixEnd_1282287 : Nat := 4983230072969 + 3 ^ 40 * 1282287 * 2
def baseEnd_1282287 : Nat := 97545121186952559987463

theorem tailTrace_1282287 : CollatzResearch.WordTrace tailWord_1282287 prefixEnd_1282287 97545121186952559987463 := by
  unfold tailWord_1282287
  simp only [CollatzResearch.WordTrace]
  refine ⟨46768849105500671029453115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31179232737000447352968743 46768849105500671029453115)
  ·
    refine ⟨70153273658251006544179673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46768849105500671029453115 70153273658251006544179673)
    ·
      refine ⟨52614955243688254908134755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70153273658251006544179673 52614955243688254908134755)
      ·
        refine ⟨78922432865532382362202133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52614955243688254908134755 78922432865532382362202133)
        ·
          refine ⟨3699489040571830423228225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78922432865532382362202133 3699489040571830423228225)
          ·
            refine ⟨2774616780428872817421169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699489040571830423228225 2774616780428872817421169)
            ·
              refine ⟨2080962585321654613065877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774616780428872817421169 2080962585321654613065877)
              ·
                refine ⟨97545121186952559987463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2080962585321654613065877 97545121186952559987463)
                ·
                  rfl

theorem cell21_1282287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_1282287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282287 prefixEnd_1282287 := by exact prefixLift 1282287
  have htrace : WordTrace (prefixWord ++ tailWord_1282287) baseStart_1282287 baseEnd_1282287 := by
    simpa [prefixWord, tailWord_1282287, baseEnd_1282287] using wordTrace_append hprefix tailTrace_1282287
  have hstable : (prefixWord ++ tailWord_1282287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282287).length < 2 ^ (prefixWord ++ tailWord_1282287).sum := by decide
  have hdescent : baseEnd_1282287 < baseStart_1282287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282290 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1282290 : Nat := 118140960795 + 1282290 * 2 ^ 59
def prefixEnd_1282290 : Nat := 4983230072969 + 3 ^ 40 * 1282290 * 2
def baseEnd_1282290 : Nat := 292636048201730341412383

theorem tailTrace_1282290 : CollatzResearch.WordTrace tailWord_1282290 prefixEnd_1282290 292636048201730341412383 := by
  unfold tailWord_1282290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11692239631122450635453081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31179305682993201694541549 11692239631122450635453081)
  ·
    refine ⟨8769179723341837976589811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11692239631122450635453081 8769179723341837976589811)
    ·
      refine ⟨13153769585012756964884717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8769179723341837976589811 13153769585012756964884717)
      ·
        refine ⟨4932663594379783861831769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13153769585012756964884717 4932663594379783861831769)
        ·
          refine ⟨3699497695784837896373827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4932663594379783861831769 3699497695784837896373827)
          ·
            refine ⟨5549246543677256844560741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699497695784837896373827 5549246543677256844560741)
            ·
              refine ⟨1040483726939485658355139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5549246543677256844560741 1040483726939485658355139)
              ·
                refine ⟨1560725590409228487532709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040483726939485658355139 1560725590409228487532709)
                ·
                  refine ⟨292636048201730341412383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560725590409228487532709 292636048201730341412383)
                  ·
                    rfl

theorem cell21_1282290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1282290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282290 prefixEnd_1282290 := by exact prefixLift 1282290
  have htrace : WordTrace (prefixWord ++ tailWord_1282290) baseStart_1282290 baseEnd_1282290 := by
    simpa [prefixWord, tailWord_1282290, baseEnd_1282290] using wordTrace_append hprefix tailTrace_1282290
  have hstable : (prefixWord ++ tailWord_1282290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282290).length < 2 ^ (prefixWord ++ tailWord_1282290).sum := by decide
  have hdescent : baseEnd_1282290 < baseStart_1282290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282301 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1282301 : Nat := 118140960795 + 1282301 * 2 ^ 59
def prefixEnd_1282301 : Nat := 4983230072969 + 3 ^ 40 * 1282301 * 2
def baseEnd_1282301 : Nat := 292638558551596766729027

theorem tailTrace_1282301 : CollatzResearch.WordTrace tailWord_1282301 prefixEnd_1282301 292638558551596766729027 := by
  unfold tailWord_1282301
  simp only [CollatzResearch.WordTrace]
  refine ⟨46769359727449951420462757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31179573151633300946975171 46769359727449951420462757)
  ·
    refine ⟨8769254948896865891336767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46769359727449951420462757 8769254948896865891336767)
    ·
      refine ⟨13153882423345298837005151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8769254948896865891336767 13153882423345298837005151)
      ·
        refine ⟨19730823635017948255507727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13153882423345298837005151 19730823635017948255507727)
        ·
          refine ⟨29596235452526922383261591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19730823635017948255507727 29596235452526922383261591)
          ·
            refine ⟨44394353178790383574892387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29596235452526922383261591 44394353178790383574892387)
            ·
              refine ⟨66591529768185575362338581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44394353178790383574892387 66591529768185575362338581)
              ·
                refine ⟨3121477957883698845109621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66591529768185575362338581 3121477957883698845109621)
                ·
                  refine ⟨292638558551596766729027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3121477957883698845109621 292638558551596766729027)
                  ·
                    rfl

theorem cell21_1282301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1282301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282301 prefixEnd_1282301 := by exact prefixLift 1282301
  have htrace : WordTrace (prefixWord ++ tailWord_1282301) baseStart_1282301 baseEnd_1282301 := by
    simpa [prefixWord, tailWord_1282301, baseEnd_1282301] using wordTrace_append hprefix tailTrace_1282301
  have hstable : (prefixWord ++ tailWord_1282301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282301).length < 2 ^ (prefixWord ++ tailWord_1282301).sum := by decide
  have hdescent : baseEnd_1282301 < baseStart_1282301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282335 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 3]
def baseStart_1282335 : Nat := 118140960795 + 1282335 * 2 ^ 59
def prefixEnd_1282335 : Nat := 4983230072969 + 3 ^ 40 * 1282335 * 2
def baseEnd_1282335 : Nat := 292646317814820263162291

theorem tailTrace_1282335 : CollatzResearch.WordTrace tailWord_1282335 prefixEnd_1282335 292646317814820263162291 := by
  unfold tailWord_1282335
  simp only [CollatzResearch.WordTrace]
  refine ⟨46770599809326775227200459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31180399872884516818133639 46770599809326775227200459)
  ·
    refine ⟨70155899713990162840800689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46770599809326775227200459 70155899713990162840800689)
    ·
      refine ⟨52616924785492622130600517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70155899713990162840800689 52616924785492622130600517)
      ·
        refine ⟨9865673397279866649487597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52616924785492622130600517 9865673397279866649487597)
        ·
          refine ⟨3699627523979949993557849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9865673397279866649487597 3699627523979949993557849)
          ·
            refine ⟨2774720642984962495168387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699627523979949993557849 2774720642984962495168387)
            ·
              refine ⟨4162080964477443742752581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774720642984962495168387 4162080964477443742752581)
              ·
                refine ⟨780390180839520701766109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4162080964477443742752581 780390180839520701766109)
                ·
                  refine ⟨292646317814820263162291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780390180839520701766109 292646317814820263162291)
                  ·
                    rfl

theorem cell21_1282335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3].length) (baseStart_1282335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282335 prefixEnd_1282335 := by exact prefixLift 1282335
  have htrace : WordTrace (prefixWord ++ tailWord_1282335) baseStart_1282335 baseEnd_1282335 := by
    simpa [prefixWord, tailWord_1282335, baseEnd_1282335] using wordTrace_append hprefix tailTrace_1282335
  have hstable : (prefixWord ++ tailWord_1282335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282335).length < 2 ^ (prefixWord ++ tailWord_1282335).sum := by decide
  have hdescent : baseEnd_1282335 < baseStart_1282335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282504 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_1282504 : Nat := 118140960795 + 1282504 * 2 ^ 59
def prefixEnd_1282504 : Nat := 4983230072969 + 3 ^ 40 * 1282504 * 2
def baseEnd_1282504 : Nat := 292684885917313524845279

theorem tailTrace_1282504 : CollatzResearch.WordTrace tailWord_1282504 prefixEnd_1282504 292684885917313524845279 := by
  unfold tailWord_1282504
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388381872857258545051283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31184509163809678060068377 23388381872857258545051283)
  ·
    refine ⟨35082572809285887817576925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23388381872857258545051283 35082572809285887817576925)
    ·
      refine ⟨13155964803482207931591347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35082572809285887817576925 13155964803482207931591347)
      ·
        refine ⟨19733947205223311897387021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13155964803482207931591347 19733947205223311897387021)
        ·
          refine ⟨7400230201958741961520133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19733947205223311897387021 7400230201958741961520133)
          ·
            refine ⟨1387543162867264117785025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7400230201958741961520133 1387543162867264117785025)
            ·
              refine ⟨1040657372150448088338769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387543162867264117785025 1040657372150448088338769)
              ·
                refine ⟨780493029112836066254077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040657372150448088338769 780493029112836066254077)
                ·
                  refine ⟨292684885917313524845279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780493029112836066254077 292684885917313524845279)
                  ·
                    rfl

theorem cell21_1282504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_1282504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282504 prefixEnd_1282504 := by exact prefixLift 1282504
  have htrace : WordTrace (prefixWord ++ tailWord_1282504) baseStart_1282504 baseEnd_1282504 := by
    simpa [prefixWord, tailWord_1282504, baseEnd_1282504] using wordTrace_append hprefix tailTrace_1282504
  have hstable : (prefixWord ++ tailWord_1282504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282504).length < 2 ^ (prefixWord ++ tailWord_1282504).sum := by decide
  have hdescent : baseEnd_1282504 < baseStart_1282504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282529 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_1282529 : Nat := 118140960795 + 1282529 * 2 ^ 59
def prefixEnd_1282529 : Nat := 4983230072969 + 3 ^ 40 * 1282529 * 2
def baseEnd_1282529 : Nat := 292690591257919036928561

theorem tailTrace_1282529 : CollatzResearch.WordTrace tailWord_1282529 prefixEnd_1282529 292690591257919036928561 := by
  unfold tailWord_1282529
  simp only [CollatzResearch.WordTrace]
  refine ⟨46777675570623946359762641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31185117047082630906508427 46777675570623946359762641)
  ·
    refine ⟨35083256677967959769821981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46777675570623946359762641 35083256677967959769821981)
    ·
      refine ⟨13156221254237984913683243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35083256677967959769821981 13156221254237984913683243)
      ·
        refine ⟨19734331881356977370524865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13156221254237984913683243 19734331881356977370524865)
        ·
          refine ⟨14800748911017733027893649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19734331881356977370524865 14800748911017733027893649)
          ·
            refine ⟨11100561683263299770920237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14800748911017733027893649 11100561683263299770920237)
            ·
              refine ⟨4162710631223737414095089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11100561683263299770920237 4162710631223737414095089)
              ·
                refine ⟨3122032973417803060571317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162710631223737414095089 3122032973417803060571317)
                ·
                  refine ⟨292690591257919036928561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122032973417803060571317 292690591257919036928561)
                  ·
                    rfl

theorem cell21_1282529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_1282529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282529 prefixEnd_1282529 := by exact prefixLift 1282529
  have htrace : WordTrace (prefixWord ++ tailWord_1282529) baseStart_1282529 baseEnd_1282529 := by
    simpa [prefixWord, tailWord_1282529, baseEnd_1282529] using wordTrace_append hprefix tailTrace_1282529
  have hstable : (prefixWord ++ tailWord_1282529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282529).length < 2 ^ (prefixWord ++ tailWord_1282529).sum := by decide
  have hdescent : baseEnd_1282529 < baseStart_1282529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282543 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_1282543 : Nat := 118140960795 + 1282543 * 2 ^ 59
def prefixEnd_1282543 : Nat := 4983230072969 + 3 ^ 40 * 1282543 * 2
def baseEnd_1282543 : Nat := 292693786248658123695199

theorem tailTrace_1282543 : CollatzResearch.WordTrace tailWord_1282543 prefixEnd_1282543 292693786248658123695199 := by
  unfold tailWord_1282543
  simp only [CollatzResearch.WordTrace]
  refine ⟨46778186192573226750772283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31185457461715484500514855 46778186192573226750772283)
  ·
    refine ⟨70167279288859840126158425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46778186192573226750772283 70167279288859840126158425)
    ·
      refine ⟨52625459466644880094618819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70167279288859840126158425 52625459466644880094618819)
      ·
        refine ⟨78938189199967320141928229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52625459466644880094618819 78938189199967320141928229)
        ·
          refine ⟨14800910474993872526611543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78938189199967320141928229 14800910474993872526611543)
          ·
            refine ⟨22201365712490808789917315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14800910474993872526611543 22201365712490808789917315)
            ·
              refine ⟨33302048568736213184875973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22201365712490808789917315 33302048568736213184875973)
              ·
                refine ⟨6244134106638039972164245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33302048568736213184875973 6244134106638039972164245)
                ·
                  refine ⟨292693786248658123695199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6244134106638039972164245 292693786248658123695199)
                  ·
                    rfl

theorem cell21_1282543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_1282543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282543 prefixEnd_1282543 := by exact prefixLift 1282543
  have htrace : WordTrace (prefixWord ++ tailWord_1282543) baseStart_1282543 baseEnd_1282543 := by
    simpa [prefixWord, tailWord_1282543, baseEnd_1282543] using wordTrace_append hprefix tailTrace_1282543
  have hstable : (prefixWord ++ tailWord_1282543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282543).length < 2 ^ (prefixWord ++ tailWord_1282543).sum := by decide
  have hdescent : baseEnd_1282543 < baseStart_1282543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282636 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1282636 : Nat := 118140960795 + 1282636 * 2 ^ 59
def prefixEnd_1282636 : Nat := 4983230072969 + 3 ^ 40 * 1282636 * 2
def baseEnd_1282636 : Nat := 292715010115710628645009

theorem tailTrace_1282636 : CollatzResearch.WordTrace tailWord_1282636 prefixEnd_1282636 292715010115710628645009 := by
  unfold tailWord_1282636
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390789090618151816953881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31187718787490869089271841 23390789090618151816953881)
  ·
    refine ⟨17543091817963613862715411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23390789090618151816953881 17543091817963613862715411)
    ·
      refine ⟨26314637726945420794073117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17543091817963613862715411 26314637726945420794073117)
      ·
        refine ⟨9867989147604532797777419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26314637726945420794073117 9867989147604532797777419)
        ·
          refine ⟨14801983721406799196666129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9867989147604532797777419 14801983721406799196666129)
          ·
            refine ⟨11101487791055099397499597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14801983721406799196666129 11101487791055099397499597)
            ·
              refine ⟨4163057921645662274062349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11101487791055099397499597 4163057921645662274062349)
              ·
                refine ⟨1561146720617123352773381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163057921645662274062349 1561146720617123352773381)
                ·
                  refine ⟨292715010115710628645009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561146720617123352773381 292715010115710628645009)
                  ·
                    rfl

theorem cell21_1282636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1282636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282636 prefixEnd_1282636 := by exact prefixLift 1282636
  have htrace : WordTrace (prefixWord ++ tailWord_1282636) baseStart_1282636 baseEnd_1282636 := by
    simpa [prefixWord, tailWord_1282636, baseEnd_1282636] using wordTrace_append hprefix tailTrace_1282636
  have hstable : (prefixWord ++ tailWord_1282636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282636).length < 2 ^ (prefixWord ++ tailWord_1282636).sum := by decide
  have hdescent : baseEnd_1282636 < baseStart_1282636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282698 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1282698 : Nat := 118140960795 + 1282698 * 2 ^ 59
def prefixEnd_1282698 : Nat := 4983230072969 + 3 ^ 40 * 1282698 * 2
def baseEnd_1282698 : Nat := 292729159360412298611549

theorem tailTrace_1282698 : CollatzResearch.WordTrace tailWord_1282698 prefixEnd_1282698 292729159360412298611549 := by
  unfold tailWord_1282698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11695959876752922055666187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31189226338007792148443165 11695959876752922055666187)
  ·
    refine ⟨17543939815129383083499281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11695959876752922055666187 17543939815129383083499281)
    ·
      refine ⟨13157954861347037312624461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17543939815129383083499281 13157954861347037312624461)
      ·
        refine ⟨4934233073005138992234173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13157954861347037312624461 4934233073005138992234173)
        ·
          refine ⟨1850337402376927122087815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4934233073005138992234173 1850337402376927122087815)
          ·
            refine ⟨2775506103565390683131723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850337402376927122087815 2775506103565390683131723)
            ·
              refine ⟨4163259155348086024697585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775506103565390683131723 4163259155348086024697585)
              ·
                refine ⟨3122444366511064518523189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163259155348086024697585 3122444366511064518523189)
                ·
                  refine ⟨292729159360412298611549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122444366511064518523189 292729159360412298611549)
                  ·
                    rfl

theorem cell21_1282698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1282698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282698 prefixEnd_1282698 := by exact prefixLift 1282698
  have htrace : WordTrace (prefixWord ++ tailWord_1282698) baseStart_1282698 baseEnd_1282698 := by
    simpa [prefixWord, tailWord_1282698, baseEnd_1282698] using wordTrace_append hprefix tailTrace_1282698
  have hstable : (prefixWord ++ tailWord_1282698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282698).length < 2 ^ (prefixWord ++ tailWord_1282698).sum := by decide
  have hdescent : baseEnd_1282698 < baseStart_1282698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282802 : List Nat := [3, 2, 1, 3, 1, 2, 1, 8]
def baseStart_1282802 : Nat := 118140960795 + 1282802 * 2 ^ 59
def prefixEnd_1282802 : Nat := 4983230072969 + 3 ^ 40 * 1282802 * 2
def baseEnd_1282802 : Nat := 97584297859110409626001

theorem tailTrace_1282802 : CollatzResearch.WordTrace tailWord_1282802 prefixEnd_1282802 97584297859110409626001 := by
  unfold tailWord_1282802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696908174658728496112665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31191755132423275989633773 11696908174658728496112665)
  ·
    refine ⟨8772681130994046372084499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11696908174658728496112665 8772681130994046372084499)
    ·
      refine ⟨13159021696491069558126749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8772681130994046372084499 13159021696491069558126749)
      ·
        refine ⟨4934633136184151084297531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13159021696491069558126749 4934633136184151084297531)
        ·
          refine ⟨7401949704276226626446297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934633136184151084297531 7401949704276226626446297)
          ·
            refine ⟨5551462278207169969834723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401949704276226626446297 5551462278207169969834723)
            ·
              refine ⟨8327193417310754954752085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551462278207169969834723 8327193417310754954752085)
              ·
                refine ⟨97584297859110409626001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8327193417310754954752085 97584297859110409626001)
                ·
                  rfl

theorem cell21_1282802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_1282802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282802 prefixEnd_1282802 := by exact prefixLift 1282802
  have htrace : WordTrace (prefixWord ++ tailWord_1282802) baseStart_1282802 baseEnd_1282802 := by
    simpa [prefixWord, tailWord_1282802, baseEnd_1282802] using wordTrace_append hprefix tailTrace_1282802
  have hstable : (prefixWord ++ tailWord_1282802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282802).length < 2 ^ (prefixWord ++ tailWord_1282802).sum := by decide
  have hdescent : baseEnd_1282802 < baseStart_1282802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282923 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_1282923 : Nat := 118140960795 + 1282923 * 2 ^ 59
def prefixEnd_1282923 : Nat := 4983230072969 + 3 ^ 40 * 1282923 * 2
def baseEnd_1282923 : Nat := 292780507425861907361089

theorem tailTrace_1282923 : CollatzResearch.WordTrace tailWord_1282923 prefixEnd_1282923 292780507425861907361089 := by
  unfold tailWord_1282923
  simp only [CollatzResearch.WordTrace]
  refine ⟨46792045931196551649605423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194697287464367766403615 46792045931196551649605423)
  ·
    refine ⟨70188068896794827474408135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46792045931196551649605423 70188068896794827474408135)
    ·
      refine ⟨105282103345192241211612203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70188068896794827474408135 105282103345192241211612203)
      ·
        refine ⟨157923155017788361817418305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105282103345192241211612203 157923155017788361817418305)
        ·
          refine ⟨118442366263341271363063729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157923155017788361817418305 118442366263341271363063729)
          ·
            refine ⟨88831774697505953522297797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118442366263341271363063729 88831774697505953522297797)
            ·
              refine ⟨16655957755782366285430837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88831774697505953522297797 16655957755782366285430837)
              ·
                refine ⟨1561496039604596839259141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16655957755782366285430837 1561496039604596839259141)
                ·
                  refine ⟨292780507425861907361089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561496039604596839259141 292780507425861907361089)
                  ·
                    rfl

theorem cell21_1282923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_1282923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282923 prefixEnd_1282923 := by exact prefixLift 1282923
  have htrace : WordTrace (prefixWord ++ tailWord_1282923) baseStart_1282923 baseEnd_1282923 := by
    simpa [prefixWord, tailWord_1282923, baseEnd_1282923] using wordTrace_append hprefix tailTrace_1282923
  have hstable : (prefixWord ++ tailWord_1282923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282923).length < 2 ^ (prefixWord ++ tailWord_1282923).sum := by decide
  have hdescent : baseEnd_1282923 < baseStart_1282923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282954 : List Nat := [3, 1, 2, 4, 1, 1, 9]
def baseStart_1282954 : Nat := 118140960795 + 1282954 * 2 ^ 59
def prefixEnd_1282954 : Nat := 4983230072969 + 3 ^ 40 * 1282954 * 2
def baseEnd_1282954 : Nat := 32531953560912526927151

theorem tailTrace_1282954 : CollatzResearch.WordTrace tailWord_1282954 prefixEnd_1282954 32531953560912526927151 := by
  unfold tailWord_1282954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11698294148521060985995979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31195451062722829295989277 11698294148521060985995979)
  ·
    refine ⟨17547441222781591478993969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11698294148521060985995979 17547441222781591478993969)
    ·
      refine ⟨13160580917086193609245477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17547441222781591478993969 13160580917086193609245477)
      ·
        refine ⟨2467608921953661301733527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13160580917086193609245477 2467608921953661301733527)
        ·
          refine ⟨3701413382930491952600291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467608921953661301733527 3701413382930491952600291)
          ·
            refine ⟨5552120074395737928900437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701413382930491952600291 5552120074395737928900437)
            ·
              refine ⟨32531953560912526927151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5552120074395737928900437 32531953560912526927151)
              ·
                rfl

theorem cell21_1282954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 9].length) (baseStart_1282954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1282954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1282954 prefixEnd_1282954 := by exact prefixLift 1282954
  have htrace : WordTrace (prefixWord ++ tailWord_1282954) baseStart_1282954 baseEnd_1282954 := by
    simpa [prefixWord, tailWord_1282954, baseEnd_1282954] using wordTrace_append hprefix tailTrace_1282954
  have hstable : (prefixWord ++ tailWord_1282954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282954).length < 2 ^ (prefixWord ++ tailWord_1282954).sum := by decide
  have hdescent : baseEnd_1282954 < baseStart_1282954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283019 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 3]
def baseStart_1283019 : Nat := 118140960795 + 1283019 * 2 ^ 59
def prefixEnd_1283019 : Nat := 4983230072969 + 3 ^ 40 * 1283019 * 2
def baseEnd_1283019 : Nat := 292802415933787073760893

theorem tailTrace_1283019 : CollatzResearch.WordTrace tailWord_1283019 prefixEnd_1283019 292802415933787073760893 := by
  unfold tailWord_1283019
  simp only [CollatzResearch.WordTrace]
  refine ⟨46795547338848760045100111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31197031559232506696733407 46795547338848760045100111)
  ·
    refine ⟨70193321008273140067650167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46795547338848760045100111 70193321008273140067650167)
    ·
      refine ⟨105289981512409710101475251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70193321008273140067650167 105289981512409710101475251)
      ·
        refine ⟨157934972268614565152212877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105289981512409710101475251 157934972268614565152212877)
        ·
          refine ⟨59225614600730461932079829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157934972268614565152212877 59225614600730461932079829)
          ·
            refine ⟨1388100342204620201533121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59225614600730461932079829 1388100342204620201533121)
            ·
              refine ⟨1041075256653465151149841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388100342204620201533121 1041075256653465151149841)
              ·
                refine ⟨780806442490098863362381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041075256653465151149841 780806442490098863362381)
                ·
                  refine ⟨292802415933787073760893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780806442490098863362381 292802415933787073760893)
                  ·
                    rfl

theorem cell21_1283019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3].length) (baseStart_1283019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283019 prefixEnd_1283019 := by exact prefixLift 1283019
  have htrace : WordTrace (prefixWord ++ tailWord_1283019) baseStart_1283019 baseEnd_1283019 := by
    simpa [prefixWord, tailWord_1283019, baseEnd_1283019] using wordTrace_append hprefix tailTrace_1283019
  have hstable : (prefixWord ++ tailWord_1283019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283019).length < 2 ^ (prefixWord ++ tailWord_1283019).sum := by decide
  have hdescent : baseEnd_1283019 < baseStart_1283019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283047 : List Nat := [1, 1, 5, 2, 2, 2, 3, 5]
def baseStart_1283047 : Nat := 118140960795 + 1283047 * 2 ^ 59
def prefixEnd_1283047 : Nat := 4983230072969 + 3 ^ 40 * 1283047 * 2
def baseEnd_1283047 : Nat := 97602935305088415764723

theorem tailTrace_1283047 : CollatzResearch.WordTrace tailWord_1283047 prefixEnd_1283047 97602935305088415764723 := by
  unfold tailWord_1283047
  simp only [CollatzResearch.WordTrace]
  refine ⟨46796568582747320827119395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31197712388498213884746263 46796568582747320827119395)
  ·
    refine ⟨70194852874120981240679093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46796568582747320827119395 70194852874120981240679093)
    ·
      refine ⟨6580767456948841991313665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70194852874120981240679093 6580767456948841991313665)
      ·
        refine ⟨4935575592711631493485249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6580767456948841991313665 4935575592711631493485249)
        ·
          refine ⟨3701681694533723620113937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4935575592711631493485249 3701681694533723620113937)
          ·
            refine ⟨2776261270900292715085453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701681694533723620113937 2776261270900292715085453)
            ·
              refine ⟨1041097976587609768157045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776261270900292715085453 1041097976587609768157045)
              ·
                refine ⟨97602935305088415764723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1041097976587609768157045 97602935305088415764723)
                ·
                  rfl

theorem cell21_1283047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 5].length) (baseStart_1283047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283047 prefixEnd_1283047 := by exact prefixLift 1283047
  have htrace : WordTrace (prefixWord ++ tailWord_1283047) baseStart_1283047 baseEnd_1283047 := by
    simpa [prefixWord, tailWord_1283047, baseEnd_1283047] using wordTrace_append hprefix tailTrace_1283047
  have hstable : (prefixWord ++ tailWord_1283047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283047).length < 2 ^ (prefixWord ++ tailWord_1283047).sum := by decide
  have hdescent : baseEnd_1283047 < baseStart_1283047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283106 : List Nat := [3, 3, 1, 1, 1, 4, 1, 7]
def baseStart_1283106 : Nat := 118140960795 + 1283106 * 2 ^ 59
def prefixEnd_1283106 : Nat := 4983230072969 + 3 ^ 40 * 1283106 * 2
def baseEnd_1283106 : Nat := 97607423506364751936905

theorem tailTrace_1283106 : CollatzResearch.WordTrace tailWord_1283106 prefixEnd_1283106 97607423506364751936905 := by
  unfold tailWord_1283106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11699680122383393475879293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31199146993022382602344781 11699680122383393475879293)
  ·
    refine ⟨4387380045893772553454735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11699680122383393475879293 4387380045893772553454735)
    ·
      refine ⟨6581070068840658830182103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387380045893772553454735 6581070068840658830182103)
      ·
        refine ⟨9871605103260988245273155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6581070068840658830182103 9871605103260988245273155)
        ·
          refine ⟨14807407654891482367909733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9871605103260988245273155 14807407654891482367909733)
          ·
            refine ⟨2776388935292152943983075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14807407654891482367909733 2776388935292152943983075)
            ·
              refine ⟨4164583402938229415974613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776388935292152943983075 4164583402938229415974613)
              ·
                refine ⟨97607423506364751936905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4164583402938229415974613 97607423506364751936905)
                ·
                  rfl

theorem cell21_1283106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_1283106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283106 prefixEnd_1283106 := by exact prefixLift 1283106
  have htrace : WordTrace (prefixWord ++ tailWord_1283106) baseStart_1283106 baseEnd_1283106 := by
    simpa [prefixWord, tailWord_1283106, baseEnd_1283106] using wordTrace_append hprefix tailTrace_1283106
  have hstable : (prefixWord ++ tailWord_1283106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283106).length < 2 ^ (prefixWord ++ tailWord_1283106).sum := by decide
  have hdescent : baseEnd_1283106 < baseStart_1283106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283196 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1283196 : Nat := 118140960795 + 1283196 * 2 ^ 59
def prefixEnd_1283196 : Nat := 4983230072969 + 3 ^ 40 * 1283196 * 2
def baseEnd_1283196 : Nat := 292842809745274099310531

theorem tailTrace_1283196 : CollatzResearch.WordTrace tailWord_1283196 prefixEnd_1283196 292842809745274099310531 := by
  unfold tailWord_1283196
  simp only [CollatzResearch.WordTrace]
  refine ⟨23401001529603759637146721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31201335372805012849528961 23401001529603759637146721)
  ·
    refine ⟨17550751147202819727860041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23401001529603759637146721 17550751147202819727860041)
    ·
      refine ⟨13163063360402114795895031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17550751147202819727860041 13163063360402114795895031)
      ·
        refine ⟨19744595040603172193842547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13163063360402114795895031 19744595040603172193842547)
        ·
          refine ⟨29616892560904758290763821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19744595040603172193842547 29616892560904758290763821)
          ·
            refine ⟨11106334710339284359036433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29616892560904758290763821 11106334710339284359036433)
            ·
              refine ⟨8329751032754463269277325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11106334710339284359036433 8329751032754463269277325)
              ·
                refine ⟨3123656637282923725978997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8329751032754463269277325 3123656637282923725978997)
                ·
                  refine ⟨292842809745274099310531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3123656637282923725978997 292842809745274099310531)
                  ·
                    rfl

theorem cell21_1283196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1283196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283196 prefixEnd_1283196 := by exact prefixLift 1283196
  have htrace : WordTrace (prefixWord ++ tailWord_1283196) baseStart_1283196 baseEnd_1283196 := by
    simpa [prefixWord, tailWord_1283196, baseEnd_1283196] using wordTrace_append hprefix tailTrace_1283196
  have hstable : (prefixWord ++ tailWord_1283196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283196).length < 2 ^ (prefixWord ++ tailWord_1283196).sum := by decide
  have hdescent : baseEnd_1283196 < baseStart_1283196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283272 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_1283272 : Nat := 118140960795 + 1283272 * 2 ^ 59
def prefixEnd_1283272 : Nat := 4983230072969 + 3 ^ 40 * 1283272 * 2
def baseEnd_1283272 : Nat := 292860153980714856043709

theorem tailTrace_1283272 : CollatzResearch.WordTrace tailWord_1283272 prefixEnd_1283272 292860153980714856043709 := by
  unfold tailWord_1283272
  simp only [CollatzResearch.WordTrace]
  refine ⟨23402387503466092127030035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31203183337954789502706713 23402387503466092127030035)
  ·
    refine ⟨35103581255199138190545053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23402387503466092127030035 35103581255199138190545053)
    ·
      refine ⟨13163842970699676821454395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35103581255199138190545053 13163842970699676821454395)
      ·
        refine ⟨19745764456049515232181593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13163842970699676821454395 19745764456049515232181593)
        ·
          refine ⟨14809323342037136424136195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19745764456049515232181593 14809323342037136424136195)
          ·
            refine ⟨22213985013055704636204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14809323342037136424136195 22213985013055704636204293)
            ·
              refine ⟨4165122189947944619288305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22213985013055704636204293 4165122189947944619288305)
              ·
                refine ⟨3123841642460958464466229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165122189947944619288305 3123841642460958464466229)
                ·
                  refine ⟨292860153980714856043709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3123841642460958464466229 292860153980714856043709)
                  ·
                    rfl

theorem cell21_1283272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_1283272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283272 prefixEnd_1283272 := by exact prefixLift 1283272
  have htrace : WordTrace (prefixWord ++ tailWord_1283272) baseStart_1283272 baseEnd_1283272 := by
    simpa [prefixWord, tailWord_1283272, baseEnd_1283272] using wordTrace_append hprefix tailTrace_1283272
  have hstable : (prefixWord ++ tailWord_1283272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283272).length < 2 ^ (prefixWord ++ tailWord_1283272).sum := by decide
  have hdescent : baseEnd_1283272 < baseStart_1283272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283379 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_1283379 : Nat := 118140960795 + 1283379 * 2 ^ 59
def prefixEnd_1283379 : Nat := 4983230072969 + 3 ^ 40 * 1283379 * 2
def baseEnd_1283379 : Nat := 292884572838506447760157

theorem tailTrace_1283379 : CollatzResearch.WordTrace tailWord_1283379 prefixEnd_1283379 292884572838506447760157 := by
  unfold tailWord_1283379
  simp only [CollatzResearch.WordTrace]
  refine ⟨46808677617544541528205191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31205785078363027685470127 46808677617544541528205191)
  ·
    refine ⟨70213016426316812292307787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46808677617544541528205191 70213016426316812292307787)
    ·
      refine ⟨105319524639475218438461681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70213016426316812292307787 105319524639475218438461681)
      ·
        refine ⟨78989643479606413828846261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105319524639475218438461681 78989643479606413828846261)
        ·
          refine ⟨7405279076213101296454337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78989643479606413828846261 7405279076213101296454337)
          ·
            refine ⟨5553959307159825972340753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7405279076213101296454337 5553959307159825972340753)
            ·
              refine ⟨4165469480369869479255565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5553959307159825972340753 4165469480369869479255565)
              ·
                refine ⟨1562051055138701054720837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4165469480369869479255565 1562051055138701054720837)
                ·
                  refine ⟨292884572838506447760157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562051055138701054720837 292884572838506447760157)
                  ·
                    rfl

theorem cell21_1283379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_1283379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283379 prefixEnd_1283379 := by exact prefixLift 1283379
  have htrace : WordTrace (prefixWord ++ tailWord_1283379) baseStart_1283379 baseEnd_1283379 := by
    simpa [prefixWord, tailWord_1283379, baseEnd_1283379] using wordTrace_append hprefix tailTrace_1283379
  have hstable : (prefixWord ++ tailWord_1283379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283379).length < 2 ^ (prefixWord ++ tailWord_1283379).sum := by decide
  have hdescent : baseEnd_1283379 < baseStart_1283379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283424 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1283424 : Nat := 118140960795 + 1283424 * 2 ^ 59
def prefixEnd_1283424 : Nat := 4983230072969 + 3 ^ 40 * 1283424 * 2
def baseEnd_1283424 : Nat := 292894842451596369510065

theorem tailTrace_1283424 : CollatzResearch.WordTrace tailWord_1283424 prefixEnd_1283424 292894842451596369510065 := by
  unfold tailWord_1283424
  simp only [CollatzResearch.WordTrace]
  refine ⟨23405159451190757106796663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31206879268254342809062217 23405159451190757106796663)
  ·
    refine ⟨35107739176786135660194995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23405159451190757106796663 35107739176786135660194995)
    ·
      refine ⟨52661608765179203490292493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35107739176786135660194995 52661608765179203490292493)
      ·
        refine ⟨19748103286942201308859685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52661608765179203490292493 19748103286942201308859685)
        ·
          refine ⟨3702769366301662745411191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19748103286942201308859685 3702769366301662745411191)
          ·
            refine ⟨5554154049452494118116787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702769366301662745411191 5554154049452494118116787)
            ·
              refine ⟨8331231074178741177175181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554154049452494118116787 8331231074178741177175181)
              ·
                refine ⟨3124211652817027941440693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331231074178741177175181 3124211652817027941440693)
                ·
                  refine ⟨292894842451596369510065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124211652817027941440693 292894842451596369510065)
                  ·
                    rfl

theorem cell21_1283424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1283424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283424 prefixEnd_1283424 := by exact prefixLift 1283424
  have htrace : WordTrace (prefixWord ++ tailWord_1283424) baseStart_1283424 baseEnd_1283424 := by
    simpa [prefixWord, tailWord_1283424, baseEnd_1283424] using wordTrace_append hprefix tailTrace_1283424
  have hstable : (prefixWord ++ tailWord_1283424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283424).length < 2 ^ (prefixWord ++ tailWord_1283424).sum := by decide
  have hdescent : baseEnd_1283424 < baseStart_1283424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283517 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1283517 : Nat := 118140960795 + 1283517 * 2 ^ 59
def prefixEnd_1283517 : Nat := 4983230072969 + 3 ^ 40 * 1283517 * 2
def baseEnd_1283517 : Nat := 292916066318648874459875

theorem tailTrace_1283517 : CollatzResearch.WordTrace tailWord_1283517 prefixEnd_1283517 292916066318648874459875 := by
  unfold tailWord_1283517
  simp only [CollatzResearch.WordTrace]
  refine ⟨46813710891044591096728805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31209140594029727397819203 46813710891044591096728805)
  ·
    refine ⟨8777570792070860830636651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46813710891044591096728805 8777570792070860830636651)
    ·
      refine ⟨13166356188106291245954977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777570792070860830636651 13166356188106291245954977)
      ·
        refine ⟨9874767141079718434466233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13166356188106291245954977 9874767141079718434466233)
        ·
          refine ⟨7406075355809788825849675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9874767141079718434466233 7406075355809788825849675)
          ·
            refine ⟨11109113033714683238774513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7406075355809788825849675 11109113033714683238774513)
            ·
              refine ⟨8331834775286012429080885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11109113033714683238774513 8331834775286012429080885)
              ·
                refine ⟨781109510183063665226333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8331834775286012429080885 781109510183063665226333)
                ·
                  refine ⟨292916066318648874459875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781109510183063665226333 292916066318648874459875)
                  ·
                    rfl

theorem cell21_1283517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1283517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283517 prefixEnd_1283517 := by exact prefixLift 1283517
  have htrace : WordTrace (prefixWord ++ tailWord_1283517) baseStart_1283517 baseEnd_1283517 := by
    simpa [prefixWord, tailWord_1283517, baseEnd_1283517] using wordTrace_append hprefix tailTrace_1283517
  have hstable : (prefixWord ++ tailWord_1283517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283517).length < 2 ^ (prefixWord ++ tailWord_1283517).sum := by decide
  have hdescent : baseEnd_1283517 < baseStart_1283517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283534 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_1283534 : Nat := 118140960795 + 1283534 * 2 ^ 59
def prefixEnd_1283534 : Nat := 4983230072969 + 3 ^ 40 * 1283534 * 2
def baseEnd_1283534 : Nat := 292919945950260622676507

theorem tailTrace_1283534 : CollatzResearch.WordTrace tailWord_1283534 prefixEnd_1283534 292919945950260622676507 := by
  unfold tailWord_1283534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851791366497875375012207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31209553954655335333398437 5851791366497875375012207)
  ·
    refine ⟨8777687049746813062518311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5851791366497875375012207 8777687049746813062518311)
    ·
      refine ⟨13166530574620219593777467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777687049746813062518311 13166530574620219593777467)
      ·
        refine ⟨19749795861930329390666201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13166530574620219593777467 19749795861930329390666201)
        ·
          refine ⟨14812346896447747042999651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19749795861930329390666201 14812346896447747042999651)
          ·
            refine ⟨22218520344671620564499477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14812346896447747042999651 22218520344671620564499477)
            ·
              refine ⟨1041493141156482213960913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22218520344671620564499477 1041493141156482213960913)
              ·
                refine ⟨781119855867361660470685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041493141156482213960913 781119855867361660470685)
                ·
                  refine ⟨292919945950260622676507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781119855867361660470685 292919945950260622676507)
                  ·
                    rfl

theorem cell21_1283534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_1283534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283534 prefixEnd_1283534 := by exact prefixLift 1283534
  have htrace : WordTrace (prefixWord ++ tailWord_1283534) baseStart_1283534 baseEnd_1283534 := by
    simpa [prefixWord, tailWord_1283534, baseEnd_1283534] using wordTrace_append hprefix tailTrace_1283534
  have hstable : (prefixWord ++ tailWord_1283534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283534).length < 2 ^ (prefixWord ++ tailWord_1283534).sum := by decide
  have hdescent : baseEnd_1283534 < baseStart_1283534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283545 : List Nat := [1, 2, 1, 2, 4, 2, 3, 6]
def baseStart_1283545 : Nat := 118140960795 + 1283545 * 2 ^ 59
def prefixEnd_1283545 : Nat := 4983230072969 + 3 ^ 40 * 1283545 * 2
def baseEnd_1283545 : Nat := 97640818766709015997717

theorem tailTrace_1283545 : CollatzResearch.WordTrace tailWord_1283545 prefixEnd_1283545 97640818766709015997717 := by
  unfold tailWord_1283545
  simp only [CollatzResearch.WordTrace]
  refine ⟨46814732134943151878748089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31209821423295434585832059 46814732134943151878748089)
  ·
    refine ⟨35111049101207363909061067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46814732134943151878748089 35111049101207363909061067)
    ·
      refine ⟨52666573651811045863591601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35111049101207363909061067 52666573651811045863591601)
      ·
        refine ⟨39499930238858284397693701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52666573651811045863591601 39499930238858284397693701)
        ·
          refine ⟨7406236919785928324567569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39499930238858284397693701 7406236919785928324567569)
          ·
            refine ⟨5554677689839446243425677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406236919785928324567569 5554677689839446243425677)
            ·
              refine ⟨2083004133689792341284629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5554677689839446243425677 2083004133689792341284629)
              ·
                refine ⟨97640818766709015997717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2083004133689792341284629 97640818766709015997717)
                ·
                  rfl

theorem cell21_1283545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_1283545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283545 prefixEnd_1283545 := by exact prefixLift 1283545
  have htrace : WordTrace (prefixWord ++ tailWord_1283545) baseStart_1283545 baseEnd_1283545 := by
    simpa [prefixWord, tailWord_1283545, baseEnd_1283545] using wordTrace_append hprefix tailTrace_1283545
  have hstable : (prefixWord ++ tailWord_1283545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283545).length < 2 ^ (prefixWord ++ tailWord_1283545).sum := by decide
  have hdescent : baseEnd_1283545 < baseStart_1283545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283582 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1283582 : Nat := 118140960795 + 1283582 * 2 ^ 59
def prefixEnd_1283582 : Nat := 4983230072969 + 3 ^ 40 * 1283582 * 2
def baseEnd_1283582 : Nat := 292930900204223205876409

theorem tailTrace_1283582 : CollatzResearch.WordTrace tailWord_1283582 prefixEnd_1283582 292930900204223205876409 := by
  unfold tailWord_1283582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852010204476138399730625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31210721090539404798563333 5852010204476138399730625)
  ·
    refine ⟨4389007653357103799797969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852010204476138399730625 4389007653357103799797969)
    ·
      refine ⟨3291755740017827849848477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4389007653357103799797969 3291755740017827849848477)
      ·
        refine ⟨1234408402506685443693179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3291755740017827849848477 1234408402506685443693179)
        ·
          refine ⟨1851612603760028165539769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234408402506685443693179 1851612603760028165539769)
          ·
            refine ⟨1388709452820021124154827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851612603760028165539769 1388709452820021124154827)
            ·
              refine ⟨2083064179230031686232241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388709452820021124154827 2083064179230031686232241)
              ·
                refine ⟨1562298134422523764674181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083064179230031686232241 1562298134422523764674181)
                ·
                  refine ⟨292930900204223205876409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562298134422523764674181 292930900204223205876409)
                  ·
                    rfl

theorem cell21_1283582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1283582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283582 prefixEnd_1283582 := by exact prefixLift 1283582
  have htrace : WordTrace (prefixWord ++ tailWord_1283582) baseStart_1283582 baseEnd_1283582 := by
    simpa [prefixWord, tailWord_1283582, baseEnd_1283582] using wordTrace_append hprefix tailTrace_1283582
  have hstable : (prefixWord ++ tailWord_1283582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283582).length < 2 ^ (prefixWord ++ tailWord_1283582).sum := by decide
  have hdescent : baseEnd_1283582 < baseStart_1283582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283745 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 3]
def baseStart_1283745 : Nat := 118140960795 + 1283745 * 2 ^ 59
def prefixEnd_1283745 : Nat := 4983230072969 + 3 ^ 40 * 1283745 * 2
def baseEnd_1283745 : Nat := 292968099024971144659409

theorem tailTrace_1283745 : CollatzResearch.WordTrace tailWord_1283745 prefixEnd_1283745 292968099024971144659409 := by
  unfold tailWord_1283745
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822026734218586036028689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31214684489479057357352459 46822026734218586036028689)
  ·
    refine ⟨35116520050663939527021517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46822026734218586036028689 35116520050663939527021517)
    ·
      refine ⟨13168695018998977322633069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35116520050663939527021517 13168695018998977322633069)
      ·
        refine ⟨4938260632124616495987401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13168695018998977322633069 4938260632124616495987401)
        ·
          refine ⟨3703695474093462371990551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4938260632124616495987401 3703695474093462371990551)
          ·
            refine ⟨5555543211140193557985827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703695474093462371990551 5555543211140193557985827)
            ·
              refine ⟨8333314816710290336978741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555543211140193557985827 8333314816710290336978741)
              ·
                refine ⟨781248264066589719091757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8333314816710290336978741 781248264066589719091757)
                ·
                  refine ⟨292968099024971144659409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781248264066589719091757 292968099024971144659409)
                  ·
                    rfl

theorem cell21_1283745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_1283745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283745 prefixEnd_1283745 := by exact prefixLift 1283745
  have htrace : WordTrace (prefixWord ++ tailWord_1283745) baseStart_1283745 baseEnd_1283745 := by
    simpa [prefixWord, tailWord_1283745, baseEnd_1283745] using wordTrace_append hprefix tailTrace_1283745
  have hstable : (prefixWord ++ tailWord_1283745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283745).length < 2 ^ (prefixWord ++ tailWord_1283745).sum := by decide
  have hdescent : baseEnd_1283745 < baseStart_1283745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283818 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1283818 : Nat := 118140960795 + 1283818 * 2 ^ 59
def prefixEnd_1283818 : Nat := 4983230072969 + 3 ^ 40 * 1283818 * 2
def baseEnd_1283818 : Nat := 292984758619539239942593

theorem tailTrace_1283818 : CollatzResearch.WordTrace tailWord_1283818 prefixEnd_1283818 292984758619539239942593 := by
  unfold tailWord_1283818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11706172315738529875859027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31216459508636079668957405 11706172315738529875859027)
  ·
    refine ⟨17559258473607794813788541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11706172315738529875859027 17559258473607794813788541)
    ·
      refine ⟨6584721927602923055170703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17559258473607794813788541 6584721927602923055170703)
      ·
        refine ⟨9877082891404384582756055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6584721927602923055170703 9877082891404384582756055)
        ·
          refine ⟨14815624337106576874134083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9877082891404384582756055 14815624337106576874134083)
          ·
            refine ⟨22223436505659865311201125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14815624337106576874134083 22223436505659865311201125)
            ·
              refine ⟨4166894344811224745850211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22223436505659865311201125 4166894344811224745850211)
              ·
                refine ⟨6250341517216837118775317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166894344811224745850211 6250341517216837118775317)
                ·
                  refine ⟨292984758619539239942593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6250341517216837118775317 292984758619539239942593)
                  ·
                    rfl

theorem cell21_1283818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1283818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283818 prefixEnd_1283818 := by exact prefixLift 1283818
  have htrace : WordTrace (prefixWord ++ tailWord_1283818) baseStart_1283818 baseEnd_1283818 := by
    simpa [prefixWord, tailWord_1283818, baseEnd_1283818] using wordTrace_append hprefix tailTrace_1283818
  have hstable : (prefixWord ++ tailWord_1283818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283818).length < 2 ^ (prefixWord ++ tailWord_1283818).sum := by decide
  have hdescent : baseEnd_1283818 < baseStart_1283818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283821 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1283821 : Nat := 118140960795 + 1283821 * 2 ^ 59
def prefixEnd_1283821 : Nat := 4983230072969 + 3 ^ 40 * 1283821 * 2
def baseEnd_1283821 : Nat := 292985443260411901392587

theorem tailTrace_1283821 : CollatzResearch.WordTrace tailWord_1283821 prefixEnd_1283821 292985443260411901392587 := by
  unfold tailWord_1283821
  simp only [CollatzResearch.WordTrace]
  refine ⟨46824798681943251015795317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31216532454628834010530211 46824798681943251015795317)
  ·
    refine ⟨4389824876432179782730811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46824798681943251015795317 4389824876432179782730811)
    ·
      refine ⟨6584737314648269674096217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389824876432179782730811 6584737314648269674096217)
      ·
        refine ⟨4938552985986202255572163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6584737314648269674096217 4938552985986202255572163)
        ·
          refine ⟨7407829478979303383358245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938552985986202255572163 7407829478979303383358245)
          ·
            refine ⟨1388968027308619384379671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7407829478979303383358245 1388968027308619384379671)
            ·
              refine ⟨2083452040962929076569507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388968027308619384379671 2083452040962929076569507)
              ·
                refine ⟨3125178061444393614854261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083452040962929076569507 3125178061444393614854261)
                ·
                  refine ⟨292985443260411901392587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3125178061444393614854261 292985443260411901392587)
                  ·
                    rfl

theorem cell21_1283821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1283821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283821 prefixEnd_1283821 := by exact prefixLift 1283821
  have htrace : WordTrace (prefixWord ++ tailWord_1283821) baseStart_1283821 baseEnd_1283821 := by
    simpa [prefixWord, tailWord_1283821, baseEnd_1283821] using wordTrace_append hprefix tailTrace_1283821
  have hstable : (prefixWord ++ tailWord_1283821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283821).length < 2 ^ (prefixWord ++ tailWord_1283821).sum := by decide
  have hdescent : baseEnd_1283821 < baseStart_1283821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283897 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 5]
def baseStart_1283897 : Nat := 118140960795 + 1283897 * 2 ^ 59
def prefixEnd_1283897 : Nat := 4983230072969 + 3 ^ 40 * 1283897 * 2
def baseEnd_1283897 : Nat := 293002787495852658125765

theorem tailTrace_1283897 : CollatzResearch.WordTrace tailWord_1283897 prefixEnd_1283897 293002787495852658125765 := by
  unfold tailWord_1283897
  simp only [CollatzResearch.WordTrace]
  refine ⟨46827570629667915995561945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31218380419778610663707963 46827570629667915995561945)
  ·
    refine ⟨35120677972250936996671459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46827570629667915995561945 35120677972250936996671459)
    ·
      refine ⟨52681016958376405495007189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35120677972250936996671459 52681016958376405495007189)
      ·
        refine ⟨1234711334961947003789231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52681016958376405495007189 1234711334961947003789231)
        ·
          refine ⟨1852067002442920505683847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234711334961947003789231 1852067002442920505683847)
          ·
            refine ⟨2778100503664380758525771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852067002442920505683847 2778100503664380758525771)
            ·
              refine ⟨4167150755496571137788657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778100503664380758525771 4167150755496571137788657)
              ·
                refine ⟨3125363066622428353341493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4167150755496571137788657 3125363066622428353341493)
                ·
                  refine ⟨293002787495852658125765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3125363066622428353341493 293002787495852658125765)
                  ·
                    rfl

theorem cell21_1283897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_1283897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1283897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1283897 prefixEnd_1283897 := by exact prefixLift 1283897
  have htrace : WordTrace (prefixWord ++ tailWord_1283897) baseStart_1283897 baseEnd_1283897 := by
    simpa [prefixWord, tailWord_1283897, baseEnd_1283897] using wordTrace_append hprefix tailTrace_1283897
  have hstable : (prefixWord ++ tailWord_1283897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283897).length < 2 ^ (prefixWord ++ tailWord_1283897).sum := by decide
  have hdescent : baseEnd_1283897 < baseStart_1283897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284004 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1284004 : Nat := 118140960795 + 1284004 * 2 ^ 59
def prefixEnd_1284004 : Nat := 4983230072969 + 3 ^ 40 * 1284004 * 2
def baseEnd_1284004 : Nat := 293027206353644249842213

theorem tailTrace_1284004 : CollatzResearch.WordTrace tailWord_1284004 prefixEnd_1284004 293027206353644249842213 := by
  unfold tailWord_1284004
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415736620140136634853533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31220982160186848846471377 23415736620140136634853533)
  ·
    refine ⟨8780901232552551238070075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23415736620140136634853533 8780901232552551238070075)
    ·
      refine ⟨13171351848828826857105113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8780901232552551238070075 13171351848828826857105113)
      ·
        refine ⟨9878513886621620142828835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13171351848828826857105113 9878513886621620142828835)
        ·
          refine ⟨14817770829932430214243253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9878513886621620142828835 14817770829932430214243253)
          ·
            refine ⟨1389166015306165332585305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14817770829932430214243253 1389166015306165332585305)
            ·
              refine ⟨1041874511479623999438979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389166015306165332585305 1041874511479623999438979)
              ·
                refine ⟨1562811767219435999158469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041874511479623999438979 1562811767219435999158469)
                ·
                  refine ⟨293027206353644249842213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562811767219435999158469 293027206353644249842213)
                  ·
                    rfl

theorem cell21_1284004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1284004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284004 prefixEnd_1284004 := by exact prefixLift 1284004
  have htrace : WordTrace (prefixWord ++ tailWord_1284004) baseStart_1284004 baseEnd_1284004 := by
    simpa [prefixWord, tailWord_1284004, baseEnd_1284004] using wordTrace_append hprefix tailTrace_1284004
  have hstable : (prefixWord ++ tailWord_1284004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284004).length < 2 ^ (prefixWord ++ tailWord_1284004).sum := by decide
  have hdescent : baseEnd_1284004 < baseStart_1284004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284032 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_1284032 : Nat := 118140960795 + 1284032 * 2 ^ 59
def prefixEnd_1284032 : Nat := 4983230072969 + 3 ^ 40 * 1284032 * 2
def baseEnd_1284032 : Nat := 293033596335122423375489

theorem tailTrace_1284032 : CollatzResearch.WordTrace tailWord_1284032 prefixEnd_1284032 293033596335122423375489 := by
  unfold tailWord_1284032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23416247242089417025863175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31221662989452556034484233 23416247242089417025863175)
  ·
    refine ⟨35124370863134125538794763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23416247242089417025863175 35124370863134125538794763)
    ·
      refine ⟨52686556294701188308192145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35124370863134125538794763 52686556294701188308192145)
      ·
        refine ⟨39514917221025891231144109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52686556294701188308192145 39514917221025891231144109)
        ·
          refine ⟨14818093957884709211679041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39514917221025891231144109 14818093957884709211679041)
          ·
            refine ⟨11113570468413531908759281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14818093957884709211679041 11113570468413531908759281)
            ·
              refine ⟨8335177851310148931569461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11113570468413531908759281 8335177851310148931569461)
              ·
                refine ⟨781422923560326462334637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8335177851310148931569461 781422923560326462334637)
                ·
                  refine ⟨293033596335122423375489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781422923560326462334637 293033596335122423375489)
                  ·
                    rfl

theorem cell21_1284032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_1284032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284032 prefixEnd_1284032 := by exact prefixLift 1284032
  have htrace : WordTrace (prefixWord ++ tailWord_1284032) baseStart_1284032 baseEnd_1284032 := by
    simpa [prefixWord, tailWord_1284032, baseEnd_1284032] using wordTrace_append hprefix tailTrace_1284032
  have hstable : (prefixWord ++ tailWord_1284032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284032).length < 2 ^ (prefixWord ++ tailWord_1284032).sum := by decide
  have hdescent : baseEnd_1284032 < baseStart_1284032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284108 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_1284108 : Nat := 118140960795 + 1284108 * 2 ^ 59
def prefixEnd_1284108 : Nat := 4983230072969 + 3 ^ 40 * 1284108 * 2
def baseEnd_1284108 : Nat := 293050940570563180108667

theorem tailTrace_1284108 : CollatzResearch.WordTrace tailWord_1284108 prefixEnd_1284108 293050940570563180108667 := by
  unfold tailWord_1284108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23417633215951749515746489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31223510954602332687661985 23417633215951749515746489)
  ·
    refine ⟨17563224911963812136809867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23417633215951749515746489 17563224911963812136809867)
    ·
      refine ⟨26344837367945718205214801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17563224911963812136809867 26344837367945718205214801)
      ·
        refine ⟨19758628025959288653911101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26344837367945718205214801 19758628025959288653911101)
        ·
          refine ⟨7409485509734733245216663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19758628025959288653911101 7409485509734733245216663)
          ·
            refine ⟨11114228264602099867824995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7409485509734733245216663 11114228264602099867824995)
            ·
              refine ⟨16671342396903149801737493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11114228264602099867824995 16671342396903149801737493)
              ·
                refine ⟨781469174854835146956445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16671342396903149801737493 781469174854835146956445)
                ·
                  refine ⟨293050940570563180108667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781469174854835146956445 293050940570563180108667)
                  ·
                    rfl

theorem cell21_1284108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_1284108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284108 prefixEnd_1284108 := by exact prefixLift 1284108
  have htrace : WordTrace (prefixWord ++ tailWord_1284108) baseStart_1284108 baseEnd_1284108 := by
    simpa [prefixWord, tailWord_1284108, baseEnd_1284108] using wordTrace_append hprefix tailTrace_1284108
  have hstable : (prefixWord ++ tailWord_1284108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284108).length < 2 ^ (prefixWord ++ tailWord_1284108).sum := by decide
  have hdescent : baseEnd_1284108 < baseStart_1284108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284142 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1284142 : Nat := 118140960795 + 1284142 * 2 ^ 59
def prefixEnd_1284142 : Nat := 4983230072969 + 3 ^ 40 * 1284142 * 2
def baseEnd_1284142 : Nat := 293058699833786676541931

theorem tailTrace_1284142 : CollatzResearch.WordTrace tailWord_1284142 prefixEnd_1284142 293058699833786676541931 := by
  unfold tailWord_1284142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854563314222540354778835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31224337675853548558820453 5854563314222540354778835)
  ·
    refine ⟨8781844971333810532168253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5854563314222540354778835 8781844971333810532168253)
    ·
      refine ⟨3293191864250178949563095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8781844971333810532168253 3293191864250178949563095)
      ·
        refine ⟨4939787796375268424344643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293191864250178949563095 4939787796375268424344643)
        ·
          refine ⟨7409681694562902636516965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939787796375268424344643 7409681694562902636516965)
          ·
            refine ⟨1389315317730544244346931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7409681694562902636516965 1389315317730544244346931)
            ·
              refine ⟨2083972976595816366520397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389315317730544244346931 2083972976595816366520397)
              ·
                refine ⟨781489866223431137445149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2083972976595816366520397 781489866223431137445149)
                ·
                  refine ⟨293058699833786676541931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781489866223431137445149 293058699833786676541931)
                  ·
                    rfl

theorem cell21_1284142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1284142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284142 prefixEnd_1284142 := by exact prefixLift 1284142
  have htrace : WordTrace (prefixWord ++ tailWord_1284142) baseStart_1284142 baseEnd_1284142 := by
    simpa [prefixWord, tailWord_1284142, baseEnd_1284142] using wordTrace_append hprefix tailTrace_1284142
  have hstable : (prefixWord ++ tailWord_1284142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284142).length < 2 ^ (prefixWord ++ tailWord_1284142).sum := by decide
  have hdescent : baseEnd_1284142 < baseStart_1284142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284153 : List Nat := [1, 2, 1, 5, 3, 2, 7]
def baseStart_1284153 : Nat := 118140960795 + 1284153 * 2 ^ 59
def prefixEnd_1284153 : Nat := 4983230072969 + 3 ^ 40 * 1284153 * 2
def baseEnd_1284153 : Nat := 32562356687072566873175

theorem tailTrace_1284153 : CollatzResearch.WordTrace tailWord_1284153 prefixEnd_1284153 32562356687072566873175 := by
  unfold tailWord_1284153
  simp only [CollatzResearch.WordTrace]
  refine ⟨46836907716740471716881113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31224605144493647811254075 46836907716740471716881113)
  ·
    refine ⟨35127680787555353787660835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46836907716740471716881113 35127680787555353787660835)
    ·
      refine ⟨52691521181333030681491253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35127680787555353787660835 52691521181333030681491253)
      ·
        refine ⟨4939830110749971626389805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52691521181333030681491253 4939830110749971626389805)
        ·
          refine ⟨1852436291531239359896177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4939830110749971626389805 1852436291531239359896177)
          ·
            refine ⟨1389327218648429519922133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852436291531239359896177 1389327218648429519922133)
            ·
              refine ⟨32562356687072566873175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1389327218648429519922133 32562356687072566873175)
              ·
                rfl

theorem cell21_1284153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 7].length) (baseStart_1284153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284153 prefixEnd_1284153 := by exact prefixLift 1284153
  have htrace : WordTrace (prefixWord ++ tailWord_1284153) baseStart_1284153 baseEnd_1284153 := by
    simpa [prefixWord, tailWord_1284153, baseEnd_1284153] using wordTrace_append hprefix tailTrace_1284153
  have hstable : (prefixWord ++ tailWord_1284153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284153).length < 2 ^ (prefixWord ++ tailWord_1284153).sum := by decide
  have hdescent : baseEnd_1284153 < baseStart_1284153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284229 : List Nat := [1, 3, 1, 1, 5, 3, 1, 6]
def baseStart_1284229 : Nat := 118140960795 + 1284229 * 2 ^ 59
def prefixEnd_1284229 : Nat := 4983230072969 + 3 ^ 40 * 1284229 * 2
def baseEnd_1284229 : Nat := 97692851473031286197251

theorem tailTrace_1284229 : CollatzResearch.WordTrace tailWord_1284229 prefixEnd_1284229 97692851473031286197251 := by
  unfold tailWord_1284229
  simp only [CollatzResearch.WordTrace]
  refine ⟨46839679664465136696647741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31226453109643424464431827 46839679664465136696647741)
  ·
    refine ⟨17564879874174426261242903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46839679664465136696647741 17564879874174426261242903)
    ·
      refine ⟨26347319811261639391864355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17564879874174426261242903 26347319811261639391864355)
      ·
        refine ⟨39520979716892459087796533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26347319811261639391864355 39520979716892459087796533)
        ·
          refine ⟨3705091848458668039480925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39520979716892459087796533 3705091848458668039480925)
          ·
            refine ⟨1389409443172000514805347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3705091848458668039480925 1389409443172000514805347)
            ·
              refine ⟨2084114164758000772208021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389409443172000514805347 2084114164758000772208021)
              ·
                refine ⟨97692851473031286197251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2084114164758000772208021 97692851473031286197251)
                ·
                  rfl

theorem cell21_1284229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 6].length) (baseStart_1284229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284229 prefixEnd_1284229 := by exact prefixLift 1284229
  have htrace : WordTrace (prefixWord ++ tailWord_1284229) baseStart_1284229 baseEnd_1284229 := by
    simpa [prefixWord, tailWord_1284229, baseEnd_1284229] using wordTrace_append hprefix tailTrace_1284229
  have hstable : (prefixWord ++ tailWord_1284229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284229).length < 2 ^ (prefixWord ++ tailWord_1284229).sum := by decide
  have hdescent : baseEnd_1284229 < baseStart_1284229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284277 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1284277 : Nat := 118140960795 + 1284277 * 2 ^ 59
def prefixEnd_1284277 : Nat := 4983230072969 + 3 ^ 40 * 1284277 * 2
def baseEnd_1284277 : Nat := 293089508673056441791655

theorem tailTrace_1284277 : CollatzResearch.WordTrace tailWord_1284277 prefixEnd_1284277 293089508673056441791655 := by
  unfold tailWord_1284277
  simp only [CollatzResearch.WordTrace]
  refine ⟨46841430368291240894395085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31227620245527493929596723 46841430368291240894395085)
  ·
    refine ⟨17565536388109215335398157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46841430368291240894395085 17565536388109215335398157)
    ·
      refine ⟨6587076145540955750774309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17565536388109215335398157 6587076145540955750774309)
      ·
        refine ⟨1235076777288929203270183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6587076145540955750774309 1235076777288929203270183)
        ·
          refine ⟨1852615165933393804905275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235076777288929203270183 1852615165933393804905275)
          ·
            refine ⟨2778922748900090707357913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852615165933393804905275 2778922748900090707357913)
            ·
              refine ⟨2084192061675068030518435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2778922748900090707357913 2084192061675068030518435)
              ·
                refine ⟨3126288092512602045777653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084192061675068030518435 3126288092512602045777653)
                ·
                  refine ⟨293089508673056441791655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126288092512602045777653 293089508673056441791655)
                  ·
                    rfl

theorem cell21_1284277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1284277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284277 prefixEnd_1284277 := by exact prefixLift 1284277
  have htrace : WordTrace (prefixWord ++ tailWord_1284277) baseStart_1284277 baseEnd_1284277 := by
    simpa [prefixWord, tailWord_1284277, baseEnd_1284277] using wordTrace_append hprefix tailTrace_1284277
  have hstable : (prefixWord ++ tailWord_1284277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284277).length < 2 ^ (prefixWord ++ tailWord_1284277).sum := by decide
  have hdescent : baseEnd_1284277 < baseStart_1284277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284381 : List Nat := [1, 4, 2, 3, 3, 8]
def baseStart_1284381 : Nat := 118140960795 + 1284381 * 2 ^ 59
def prefixEnd_1284381 : Nat := 4983230072969 + 3 ^ 40 * 1284381 * 2
def baseEnd_1284381 : Nat := 10856046032962050816967

theorem tailTrace_1284381 : CollatzResearch.WordTrace tailWord_1284381 prefixEnd_1284381 10856046032962050816967 := by
  unfold tailWord_1284381
  simp only [CollatzResearch.WordTrace]
  refine ⟨46845223559914466656180997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31230149039942977770787331 46845223559914466656180997)
  ·
    refine ⟨8783479417483962498033937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46845223559914466656180997 8783479417483962498033937)
    ·
      refine ⟨6587609563112971873525453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8783479417483962498033937 6587609563112971873525453)
      ·
        refine ⟨2470353586167364452572045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6587609563112971873525453 2470353586167364452572045)
        ·
          refine ⟨926382594812761669714517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2470353586167364452572045 926382594812761669714517)
          ·
            refine ⟨10856046032962050816967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 926382594812761669714517 10856046032962050816967)
            ·
              rfl

theorem cell21_1284381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 8].length) (baseStart_1284381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284381 prefixEnd_1284381 := by exact prefixLift 1284381
  have htrace : WordTrace (prefixWord ++ tailWord_1284381) baseStart_1284381 baseEnd_1284381 := by
    simpa [prefixWord, tailWord_1284381, baseEnd_1284381] using wordTrace_append hprefix tailTrace_1284381
  have hstable : (prefixWord ++ tailWord_1284381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284381).length < 2 ^ (prefixWord ++ tailWord_1284381).sum := by decide
  have hdescent : baseEnd_1284381 < baseStart_1284381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284519 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 4]
def baseStart_1284519 : Nat := 118140960795 + 1284519 * 2 ^ 59
def prefixEnd_1284519 : Nat := 4983230072969 + 3 ^ 40 * 1284519 * 2
def baseEnd_1284519 : Nat := 293144736370117798757827

theorem tailTrace_1284519 : CollatzResearch.WordTrace tailWord_1284519 prefixEnd_1284519 293144736370117798757827 := by
  unfold tailWord_1284519
  simp only [CollatzResearch.WordTrace]
  refine ⟨46850256833414516224704611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31233504555609677483136407 46850256833414516224704611)
  ·
    refine ⟨70275385250121774337056917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46850256833414516224704611 70275385250121774337056917)
    ·
      refine ⟨3294158683599458172049543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70275385250121774337056917 3294158683599458172049543)
      ·
        refine ⟨4941238025399187258074315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294158683599458172049543 4941238025399187258074315)
        ·
          refine ⟨7411857038098780887111473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941238025399187258074315 7411857038098780887111473)
          ·
            refine ⟨5558892778574085665333605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7411857038098780887111473 5558892778574085665333605)
            ·
              refine ⟨1042292395982641062250051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5558892778574085665333605 1042292395982641062250051)
              ·
                refine ⟨1563438593973961593375077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042292395982641062250051 1563438593973961593375077)
                ·
                  refine ⟨293144736370117798757827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563438593973961593375077 293144736370117798757827)
                  ·
                    rfl

theorem cell21_1284519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4].length) (baseStart_1284519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284519 prefixEnd_1284519 := by exact prefixLift 1284519
  have htrace : WordTrace (prefixWord ++ tailWord_1284519) baseStart_1284519 baseEnd_1284519 := by
    simpa [prefixWord, tailWord_1284519, baseEnd_1284519] using wordTrace_append hprefix tailTrace_1284519
  have hstable : (prefixWord ++ tailWord_1284519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284519).length < 2 ^ (prefixWord ++ tailWord_1284519).sum := by decide
  have hdescent : baseEnd_1284519 < baseStart_1284519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284530 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1284530 : Nat := 118140960795 + 1284530 * 2 ^ 59
def prefixEnd_1284530 : Nat := 4983230072969 + 3 ^ 40 * 1284530 * 2
def baseEnd_1284530 : Nat := 293147246719984224074471

theorem tailTrace_1284530 : CollatzResearch.WordTrace tailWord_1284530 prefixEnd_1284530 293147246719984224074471 := by
  unfold tailWord_1284530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712664509093666275838761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31233772024249776735570029 11712664509093666275838761)
  ·
    refine ⟨8784498381820249706879071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11712664509093666275838761 8784498381820249706879071)
    ·
      refine ⟨13176747572730374560318607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784498381820249706879071 13176747572730374560318607)
      ·
        refine ⟨19765121359095561840477911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13176747572730374560318607 19765121359095561840477911)
        ·
          refine ⟨29647682038643342760716867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19765121359095561840477911 29647682038643342760716867)
          ·
            refine ⟨44471523057965014141075301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29647682038643342760716867 44471523057965014141075301)
            ·
              refine ⟨8338410573368440151451619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44471523057965014141075301 8338410573368440151451619)
              ·
                refine ⟨12507615860052660227177429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338410573368440151451619 12507615860052660227177429)
                ·
                  refine ⟨293147246719984224074471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12507615860052660227177429 293147246719984224074471)
                  ·
                    rfl

theorem cell21_1284530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1284530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284530 prefixEnd_1284530 := by exact prefixLift 1284530
  have htrace : WordTrace (prefixWord ++ tailWord_1284530) baseStart_1284530 baseEnd_1284530 := by
    simpa [prefixWord, tailWord_1284530, baseEnd_1284530] using wordTrace_append hprefix tailTrace_1284530
  have hstable : (prefixWord ++ tailWord_1284530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284530).length < 2 ^ (prefixWord ++ tailWord_1284530).sum := by decide
  have hdescent : baseEnd_1284530 < baseStart_1284530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284547 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 3]
def baseStart_1284547 : Nat := 118140960795 + 1284547 * 2 ^ 59
def prefixEnd_1284547 : Nat := 4983230072969 + 3 ^ 40 * 1284547 * 2
def baseEnd_1284547 : Nat := 293151126351595972291103

theorem tailTrace_1284547 : CollatzResearch.WordTrace tailWord_1284547 prefixEnd_1284547 293151126351595972291103 := by
  unfold tailWord_1284547
  simp only [CollatzResearch.WordTrace]
  refine ⟨46851278077313077006723895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31234185384875384671149263 46851278077313077006723895)
  ·
    refine ⟨70276917115969615510085843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46851278077313077006723895 70276917115969615510085843)
    ·
      refine ⟨105415375673954423265128765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70276917115969615510085843 105415375673954423265128765)
      ·
        refine ⟨39530765877732908724423287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105415375673954423265128765 39530765877732908724423287)
        ·
          refine ⟨59296148816599363086634931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39530765877732908724423287 59296148816599363086634931)
          ·
            refine ⟨88944223224899044629952397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59296148816599363086634931 88944223224899044629952397)
            ·
              refine ⟨33354083709337141736232149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88944223224899044629952397 33354083709337141736232149)
              ·
                refine ⟨781736336937589259442941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33354083709337141736232149 781736336937589259442941)
                ·
                  refine ⟨293151126351595972291103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781736336937589259442941 293151126351595972291103)
                  ·
                    rfl

theorem cell21_1284547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3].length) (baseStart_1284547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284547 prefixEnd_1284547 := by exact prefixLift 1284547
  have htrace : WordTrace (prefixWord ++ tailWord_1284547) baseStart_1284547 baseEnd_1284547 := by
    simpa [prefixWord, tailWord_1284547, baseEnd_1284547] using wordTrace_append hprefix tailTrace_1284547
  have hstable : (prefixWord ++ tailWord_1284547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284547).length < 2 ^ (prefixWord ++ tailWord_1284547).sum := by decide
  have hdescent : baseEnd_1284547 < baseStart_1284547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284592 : List Nat := [2, 1, 1, 1, 3, 3, 5, 5]
def baseStart_1284592 : Nat := 118140960795 + 1284592 * 2 ^ 59
def prefixEnd_1284592 : Nat := 4983230072969 + 3 ^ 40 * 1284592 * 2
def baseEnd_1284592 : Nat := 97720465321561964680337

theorem tailTrace_1284592 : CollatzResearch.WordTrace tailWord_1284592 prefixEnd_1284592 97720465321561964680337 := by
  unfold tailWord_1284592
  simp only [CollatzResearch.WordTrace]
  refine ⟨23426459681075024846056015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31235279574766699794741353 23426459681075024846056015)
  ·
    refine ⟨35139689521612537269084023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23426459681075024846056015 35139689521612537269084023)
    ·
      refine ⟨52709534282418805903626035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35139689521612537269084023 52709534282418805903626035)
      ·
        refine ⟨79064301423628208855439053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52709534282418805903626035 79064301423628208855439053)
        ·
          refine ⟨29649113033860578320789645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79064301423628208855439053 29649113033860578320789645)
          ·
            refine ⟨11118417387697716870296117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29649113033860578320789645 11118417387697716870296117)
            ·
              refine ⟨1042351630096660956590261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11118417387697716870296117 1042351630096660956590261)
              ·
                refine ⟨97720465321561964680337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1042351630096660956590261 97720465321561964680337)
                ·
                  rfl

theorem cell21_1284592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_1284592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284592 prefixEnd_1284592 := by exact prefixLift 1284592
  have htrace : WordTrace (prefixWord ++ tailWord_1284592) baseStart_1284592 baseEnd_1284592 := by
    simpa [prefixWord, tailWord_1284592, baseEnd_1284592] using wordTrace_append hprefix tailTrace_1284592
  have hstable : (prefixWord ++ tailWord_1284592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284592).length < 2 ^ (prefixWord ++ tailWord_1284592).sum := by decide
  have hdescent : baseEnd_1284592 < baseStart_1284592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284668 : List Nat := [2, 2, 2, 2, 3, 3, 7]
def baseStart_1284668 : Nat := 118140960795 + 1284668 * 2 ^ 59
def prefixEnd_1284668 : Nat := 4983230072969 + 3 ^ 40 * 1284668 * 2
def baseEnd_1284668 : Nat := 32575415577791850086021

theorem tailTrace_1284668 : CollatzResearch.WordTrace tailWord_1284668 prefixEnd_1284668 32575415577791850086021 := by
  unfold tailWord_1284668
  simp only [CollatzResearch.WordTrace]
  refine ⟨23427845654937357335939329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31237127539916476447919105 23427845654937357335939329)
  ·
    refine ⟨17570884241203018001954497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23427845654937357335939329 17570884241203018001954497)
    ·
      refine ⟨13178163180902263501465873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17570884241203018001954497 13178163180902263501465873)
      ·
        refine ⟨9883622385676697626099405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13178163180902263501465873 9883622385676697626099405)
        ·
          refine ⟨3706358394628761609787277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9883622385676697626099405 3706358394628761609787277)
          ·
            refine ⟨1389884397985785603670229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3706358394628761609787277 1389884397985785603670229)
            ·
              refine ⟨32575415577791850086021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1389884397985785603670229 32575415577791850086021)
              ·
                rfl

theorem cell21_1284668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 7].length) (baseStart_1284668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284668 prefixEnd_1284668 := by exact prefixLift 1284668
  have htrace : WordTrace (prefixWord ++ tailWord_1284668) baseStart_1284668 baseEnd_1284668 := by
    simpa [prefixWord, tailWord_1284668, baseEnd_1284668] using wordTrace_append hprefix tailTrace_1284668
  have hstable : (prefixWord ++ tailWord_1284668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284668).length < 2 ^ (prefixWord ++ tailWord_1284668).sum := by decide
  have hdescent : baseEnd_1284668 < baseStart_1284668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284685 : List Nat := [1, 6, 1, 1, 2, 2, 2, 6]
def baseStart_1284685 : Nat := 118140960795 + 1284685 * 2 ^ 59
def prefixEnd_1284685 : Nat := 4983230072969 + 3 ^ 40 * 1284685 * 2
def baseEnd_1284685 : Nat := 97727539943912799663607

theorem tailTrace_1284685 : CollatzResearch.WordTrace tailWord_1284685 prefixEnd_1284685 97727539943912799663607 := by
  unfold tailWord_1284685
  simp only [CollatzResearch.WordTrace]
  refine ⟨46856311350813126575247509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31237540900542084383498339 46856311350813126575247509)
  ·
    refine ⟨2196389594569365308214727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46856311350813126575247509 2196389594569365308214727)
    ·
      refine ⟨3294584391854047962322091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196389594569365308214727 3294584391854047962322091)
      ·
        refine ⟨4941876587781071943483137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294584391854047962322091 4941876587781071943483137)
        ·
          refine ⟨3706407440835803957612353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4941876587781071943483137 3706407440835803957612353)
          ·
            refine ⟨2779805580626852968209265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3706407440835803957612353 2779805580626852968209265)
            ·
              refine ⟨2084854185470139726156949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2779805580626852968209265 2084854185470139726156949)
              ·
                refine ⟨97727539943912799663607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2084854185470139726156949 97727539943912799663607)
                ·
                  rfl

theorem cell21_1284685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_1284685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284685 prefixEnd_1284685 := by exact prefixLift 1284685
  have htrace : WordTrace (prefixWord ++ tailWord_1284685) baseStart_1284685 baseEnd_1284685 := by
    simpa [prefixWord, tailWord_1284685, baseEnd_1284685] using wordTrace_append hprefix tailTrace_1284685
  have hstable : (prefixWord ++ tailWord_1284685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284685).length < 2 ^ (prefixWord ++ tailWord_1284685).sum := by decide
  have hdescent : baseEnd_1284685 < baseStart_1284685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284848 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_1284848 : Nat := 118140960795 + 1284848 * 2 ^ 59
def prefixEnd_1284848 : Nat := 4983230072969 + 3 ^ 40 * 1284848 * 2
def baseEnd_1284848 : Nat := 293219818652486337773821

theorem tailTrace_1284848 : CollatzResearch.WordTrace tailWord_1284848 prefixEnd_1284848 293219818652486337773821 := by
  unfold tailWord_1284848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23431128224611302706715599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31241504299481736942287465 23431128224611302706715599)
  ·
    refine ⟨35146692336916954060073399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23431128224611302706715599 35146692336916954060073399)
    ·
      refine ⟨52720038505375431090110099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35146692336916954060073399 52720038505375431090110099)
      ·
        refine ⟨79080057758063146635165149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52720038505375431090110099 79080057758063146635165149)
        ·
          refine ⟨29655021659273679988186931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79080057758063146635165149 29655021659273679988186931)
          ·
            refine ⟨44482532488910519982280397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29655021659273679988186931 44482532488910519982280397)
            ·
              refine ⟨16680949683341444993355149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44482532488910519982280397 16680949683341444993355149)
              ·
                refine ⟨6255356131253041872508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16680949683341444993355149 6255356131253041872508181)
                ·
                  refine ⟨293219818652486337773821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6255356131253041872508181 293219818652486337773821)
                  ·
                    rfl

theorem cell21_1284848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_1284848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284848 prefixEnd_1284848 := by exact prefixLift 1284848
  have htrace : WordTrace (prefixWord ++ tailWord_1284848) baseStart_1284848 baseEnd_1284848 := by
    simpa [prefixWord, tailWord_1284848, baseEnd_1284848] using wordTrace_append hprefix tailTrace_1284848
  have hstable : (prefixWord ++ tailWord_1284848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284848).length < 2 ^ (prefixWord ++ tailWord_1284848).sum := by decide
  have hdescent : baseEnd_1284848 < baseStart_1284848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284924 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1284924 : Nat := 118140960795 + 1284924 * 2 ^ 59
def prefixEnd_1284924 : Nat := 4983230072969 + 3 ^ 40 * 1284924 * 2
def baseEnd_1284924 : Nat := 293237162887927094506999

theorem tailTrace_1284924 : CollatzResearch.WordTrace tailWord_1284924 prefixEnd_1284924 293237162887927094506999 := by
  unfold tailWord_1284924
  simp only [CollatzResearch.WordTrace]
  refine ⟨23432514198473635196598913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31243352264631513595465217 23432514198473635196598913)
  ·
    refine ⟨17574385648855226397449185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23432514198473635196598913 17574385648855226397449185)
    ·
      refine ⟨13180789236641419798086889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17574385648855226397449185 13180789236641419798086889)
      ·
        refine ⟨9885591927481064848565167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13180789236641419798086889 9885591927481064848565167)
        ·
          refine ⟨14828387891221597272847751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9885591927481064848565167 14828387891221597272847751)
          ·
            refine ⟨22242581836832395909271627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14828387891221597272847751 22242581836832395909271627)
            ·
              refine ⟨33363872755248593863907441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22242581836832395909271627 33363872755248593863907441)
              ·
                refine ⟨25022904566436445397930581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33363872755248593863907441 25022904566436445397930581)
                ·
                  refine ⟨293237162887927094506999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25022904566436445397930581 293237162887927094506999)
                  ·
                    rfl

theorem cell21_1284924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1284924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1284924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1284924 prefixEnd_1284924 := by exact prefixLift 1284924
  have htrace : WordTrace (prefixWord ++ tailWord_1284924) baseStart_1284924 baseEnd_1284924 := by
    simpa [prefixWord, tailWord_1284924, baseEnd_1284924] using wordTrace_append hprefix tailTrace_1284924
  have hstable : (prefixWord ++ tailWord_1284924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284924).length < 2 ^ (prefixWord ++ tailWord_1284924).sum := by decide
  have hdescent : baseEnd_1284924 < baseStart_1284924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285003 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 3]
def baseStart_1285003 : Nat := 118140960795 + 1285003 * 2 ^ 59
def prefixEnd_1285003 : Nat := 4983230072969 + 3 ^ 40 * 1285003 * 2
def baseEnd_1285003 : Nat := 293255191764240512690171

theorem tailTrace_1285003 : CollatzResearch.WordTrace tailWord_1285003 prefixEnd_1285003 293255191764240512690171 := by
  unfold tailWord_1285003
  simp only [CollatzResearch.WordTrace]
  refine ⟨46867909763661066885323663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31245273175774044590215775 46867909763661066885323663)
  ·
    refine ⟨70301864645491600327985495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46867909763661066885323663 70301864645491600327985495)
    ·
      refine ⟨105452796968237400491978243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70301864645491600327985495 105452796968237400491978243)
      ·
        refine ⟨158179195452356100737967365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105452796968237400491978243 158179195452356100737967365)
        ·
          refine ⟨29658599147316768888368881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158179195452356100737967365 29658599147316768888368881)
          ·
            refine ⟨22243949360487576666276661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29658599147316768888368881 22243949360487576666276661)
            ·
              refine ⟨2085370252545710312463437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22243949360487576666276661 2085370252545710312463437)
              ·
                refine ⟨782013844704641367173789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085370252545710312463437 782013844704641367173789)
                ·
                  refine ⟨293255191764240512690171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782013844704641367173789 293255191764240512690171)
                  ·
                    rfl

theorem cell21_1285003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3].length) (baseStart_1285003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285003 prefixEnd_1285003 := by exact prefixLift 1285003
  have htrace : WordTrace (prefixWord ++ tailWord_1285003) baseStart_1285003 baseEnd_1285003 := by
    simpa [prefixWord, tailWord_1285003, baseEnd_1285003] using wordTrace_append hprefix tailTrace_1285003
  have hstable : (prefixWord ++ tailWord_1285003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285003).length < 2 ^ (prefixWord ++ tailWord_1285003).sum := by decide
  have hdescent : baseEnd_1285003 < baseStart_1285003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285020 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1285020 : Nat := 118140960795 + 1285020 * 2 ^ 59
def prefixEnd_1285020 : Nat := 4983230072969 + 3 ^ 40 * 1285020 * 2
def baseEnd_1285020 : Nat := 293259071395852260906803

theorem tailTrace_1285020 : CollatzResearch.WordTrace tailWord_1285020 prefixEnd_1285020 293259071395852260906803 := by
  unfold tailWord_1285020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23434264902299739394346257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31245686536399652525795009 23434264902299739394346257)
  ·
    refine ⟨17575698676724804545759693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23434264902299739394346257 17575698676724804545759693)
    ·
      refine ⟨6590887003771801704659885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17575698676724804545759693 6590887003771801704659885)
      ·
        refine ⟨2471582626414425639247457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6590887003771801704659885 2471582626414425639247457)
        ·
          refine ⟨1853686969810819229435593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2471582626414425639247457 1853686969810819229435593)
          ·
            refine ⟨1390265227358114422076695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853686969810819229435593 1390265227358114422076695)
            ·
              refine ⟨2085397841037171633115043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390265227358114422076695 2085397841037171633115043)
              ·
                refine ⟨3128096761555757449672565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085397841037171633115043 3128096761555757449672565)
                ·
                  refine ⟨293259071395852260906803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128096761555757449672565 293259071395852260906803)
                  ·
                    rfl

theorem cell21_1285020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1285020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285020 prefixEnd_1285020 := by exact prefixLift 1285020
  have htrace : WordTrace (prefixWord ++ tailWord_1285020) baseStart_1285020 baseEnd_1285020 := by
    simpa [prefixWord, tailWord_1285020, baseEnd_1285020] using wordTrace_append hprefix tailTrace_1285020
  have hstable : (prefixWord ++ tailWord_1285020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285020).length < 2 ^ (prefixWord ++ tailWord_1285020).sum := by decide
  have hdescent : baseEnd_1285020 < baseStart_1285020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285245 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1285245 : Nat := 118140960795 + 1285245 * 2 ^ 59
def prefixEnd_1285245 : Nat := 4983230072969 + 3 ^ 40 * 1285245 * 2
def baseEnd_1285245 : Nat := 293310419461301869656343

theorem tailTrace_1285245 : CollatzResearch.WordTrace tailWord_1285245 prefixEnd_1285245 293310419461301869656343 := by
  unfold tailWord_1285245
  simp only [CollatzResearch.WordTrace]
  refine ⟨46876736228784342215633189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31251157485856228143755459 46876736228784342215633189)
  ·
    refine ⟨8789388042897064165431223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46876736228784342215633189 8789388042897064165431223)
    ·
      refine ⟨13184082064345596248146835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8789388042897064165431223 13184082064345596248146835)
      ·
        refine ⟨19776123096518394372220253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13184082064345596248146835 19776123096518394372220253)
        ·
          refine ⟨7416046161194397889582595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19776123096518394372220253 7416046161194397889582595)
          ·
            refine ⟨11124069241791596834373893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416046161194397889582595 11124069241791596834373893)
            ·
              refine ⟨2085762982835924406445105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11124069241791596834373893 2085762982835924406445105)
              ·
                refine ⟨1564322237126943304833829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085762982835924406445105 1564322237126943304833829)
                ·
                  refine ⟨293310419461301869656343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564322237126943304833829 293310419461301869656343)
                  ·
                    rfl

theorem cell21_1285245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1285245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285245 prefixEnd_1285245 := by exact prefixLift 1285245
  have htrace : WordTrace (prefixWord ++ tailWord_1285245) baseStart_1285245 baseEnd_1285245 := by
    simpa [prefixWord, tailWord_1285245, baseEnd_1285245] using wordTrace_append hprefix tailTrace_1285245
  have hstable : (prefixWord ++ tailWord_1285245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285245).length < 2 ^ (prefixWord ++ tailWord_1285245).sum := by decide
  have hdescent : baseEnd_1285245 < baseStart_1285245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285276 : List Nat := [2, 2, 3, 2, 1, 3, 3, 5]
def baseStart_1285276 : Nat := 118140960795 + 1285276 * 2 ^ 59
def prefixEnd_1285276 : Nat := 4983230072969 + 3 ^ 40 * 1285276 * 2
def baseEnd_1285276 : Nat := 97772498027884234879871

theorem tailTrace_1285276 : CollatzResearch.WordTrace tailWord_1285276 prefixEnd_1285276 97772498027884234879871 := by
  unfold tailWord_1285276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23438933445836017255005841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31251911261114689673341121 23438933445836017255005841)
  ·
    refine ⟨17579200084377012941254381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23438933445836017255005841 17579200084377012941254381)
    ·
      refine ⟨6592200031641379852970393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17579200084377012941254381 6592200031641379852970393)
      ·
        refine ⟨4944150023731034889727795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6592200031641379852970393 4944150023731034889727795)
        ·
          refine ⟨7416225035596552334591693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944150023731034889727795 7416225035596552334591693)
          ·
            refine ⟨2781084388348707125471885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7416225035596552334591693 2781084388348707125471885)
            ·
              refine ⟨1042906645630765172051957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2781084388348707125471885 1042906645630765172051957)
              ·
                refine ⟨97772498027884234879871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1042906645630765172051957 97772498027884234879871)
                ·
                  rfl

theorem cell21_1285276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_1285276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285276 prefixEnd_1285276 := by exact prefixLift 1285276
  have htrace : WordTrace (prefixWord ++ tailWord_1285276) baseStart_1285276 baseEnd_1285276 := by
    simpa [prefixWord, tailWord_1285276, baseEnd_1285276] using wordTrace_append hprefix tailTrace_1285276
  have hstable : (prefixWord ++ tailWord_1285276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285276).length < 2 ^ (prefixWord ++ tailWord_1285276).sum := by decide
  have hdescent : baseEnd_1285276 < baseStart_1285276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285304 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_1285304 : Nat := 118140960795 + 1285304 * 2 ^ 59
def prefixEnd_1285304 : Nat := 4983230072969 + 3 ^ 40 * 1285304 * 2
def baseEnd_1285304 : Nat := 293323884065130878172889

theorem tailTrace_1285304 : CollatzResearch.WordTrace tailWord_1285304 prefixEnd_1285304 293323884065130878172889 := by
  unfold tailWord_1285304
  simp only [CollatzResearch.WordTrace]
  refine ⟨23439444067785297646015483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31252592090380396861353977 23439444067785297646015483)
  ·
    refine ⟨35159166101677946469023225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23439444067785297646015483 35159166101677946469023225)
    ·
      refine ⟨26369374576258459851767419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35159166101677946469023225 26369374576258459851767419)
      ·
        refine ⟨39554061864387689777651129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26369374576258459851767419 39554061864387689777651129)
        ·
          refine ⟨29665546398290767333238347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39554061864387689777651129 29665546398290767333238347)
          ·
            refine ⟨44498319597436150999857521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29665546398290767333238347 44498319597436150999857521)
            ·
              refine ⟨33373739698077113249893141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44498319597436150999857521 33373739698077113249893141)
              ·
                refine ⟨1564394048347364683588741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33373739698077113249893141 1564394048347364683588741)
                ·
                  refine ⟨293323884065130878172889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564394048347364683588741 293323884065130878172889)
                  ·
                    rfl

theorem cell21_1285304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_1285304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285304 prefixEnd_1285304 := by exact prefixLift 1285304
  have htrace : WordTrace (prefixWord ++ tailWord_1285304) baseStart_1285304 baseEnd_1285304 := by
    simpa [prefixWord, tailWord_1285304, baseEnd_1285304] using wordTrace_append hprefix tailTrace_1285304
  have hstable : (prefixWord ++ tailWord_1285304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285304).length < 2 ^ (prefixWord ++ tailWord_1285304).sum := by decide
  have hdescent : baseEnd_1285304 < baseStart_1285304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285335 : List Nat := [1, 1, 3, 2, 1, 2, 6, 5]
def baseStart_1285335 : Nat := 118140960795 + 1285335 * 2 ^ 59
def prefixEnd_1285335 : Nat := 4983230072969 + 3 ^ 40 * 1285335 * 2
def baseEnd_1285335 : Nat := 97776986229160571052053

theorem tailTrace_1285335 : CollatzResearch.WordTrace tailWord_1285335 prefixEnd_1285335 97776986229160571052053 := by
  unfold tailWord_1285335
  simp only [CollatzResearch.WordTrace]
  refine ⟨46880018798458287586409459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31253345865638858390939639 46880018798458287586409459)
  ·
    refine ⟨70320028197687431379614189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46880018798458287586409459 70320028197687431379614189)
    ·
      refine ⟨26370010574132786767355321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70320028197687431379614189 26370010574132786767355321)
      ·
        refine ⟨19777507930599590075516491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26370010574132786767355321 19777507930599590075516491)
        ·
          refine ⟨29666261895899385113274737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19777507930599590075516491 29666261895899385113274737)
          ·
            refine ⟨22249696421924538834956053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29666261895899385113274737 22249696421924538834956053)
            ·
              refine ⟨1042954519777712757888565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22249696421924538834956053 1042954519777712757888565)
              ·
                refine ⟨97776986229160571052053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1042954519777712757888565 97776986229160571052053)
                ·
                  rfl

theorem cell21_1285335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 5].length) (baseStart_1285335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285335 prefixEnd_1285335 := by exact prefixLift 1285335
  have htrace : WordTrace (prefixWord ++ tailWord_1285335) baseStart_1285335 baseEnd_1285335 := by
    simpa [prefixWord, tailWord_1285335, baseEnd_1285335] using wordTrace_append hprefix tailTrace_1285335
  have hstable : (prefixWord ++ tailWord_1285335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285335).length < 2 ^ (prefixWord ++ tailWord_1285335).sum := by decide
  have hdescent : baseEnd_1285335 < baseStart_1285335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285341 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1285341 : Nat := 118140960795 + 1285341 * 2 ^ 59
def prefixEnd_1285341 : Nat := 4983230072969 + 3 ^ 40 * 1285341 * 2
def baseEnd_1285341 : Nat := 293332327969227036056147

theorem tailTrace_1285341 : CollatzResearch.WordTrace tailWord_1285341 prefixEnd_1285341 293332327969227036056147 := by
  unfold tailWord_1285341
  simp only [CollatzResearch.WordTrace]
  refine ⟨46880237636436550611127877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31253491757624367074085251 46880237636436550611127877)
  ·
    refine ⟨8790044556831853239586477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46880237636436550611127877 8790044556831853239586477)
    ·
      refine ⟨3296266708811944964844929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8790044556831853239586477 3296266708811944964844929)
      ·
        refine ⟨2472200031608958723633697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296266708811944964844929 2472200031608958723633697)
        ·
          refine ⟨1854150023706719042725273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472200031608958723633697 1854150023706719042725273)
          ·
            refine ⟨1390612517780039282043955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1854150023706719042725273 1390612517780039282043955)
            ·
              refine ⟨2085918776670058923065933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390612517780039282043955 2085918776670058923065933)
              ·
                refine ⟨782219541251272096149725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085918776670058923065933 782219541251272096149725)
                ·
                  refine ⟨293332327969227036056147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782219541251272096149725 293332327969227036056147)
                  ·
                    rfl

theorem cell21_1285341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1285341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285341 prefixEnd_1285341 := by exact prefixLift 1285341
  have htrace : WordTrace (prefixWord ++ tailWord_1285341) baseStart_1285341 baseEnd_1285341 := by
    simpa [prefixWord, tailWord_1285341, baseEnd_1285341] using wordTrace_append hprefix tailTrace_1285341
  have hstable : (prefixWord ++ tailWord_1285341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285341).length < 2 ^ (prefixWord ++ tailWord_1285341).sum := by decide
  have hdescent : baseEnd_1285341 < baseStart_1285341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285462 : List Nat := [5, 2, 3, 1, 1, 1, 8]
def baseStart_1285462 : Nat := 118140960795 + 1285462 * 2 ^ 59
def prefixEnd_1285462 : Nat := 4983230072969 + 3 ^ 40 * 1285462 * 2
def baseEnd_1285462 : Nat := 32595549090861968282137

theorem tailTrace_1285462 : CollatzResearch.WordTrace tailWord_1285462 prefixEnd_1285462 32595549090861968282137 := by
  unfold tailWord_1285462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930290679312386767267665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31256433912665458850855093 2930290679312386767267665)
  ·
    refine ⟨2197718009484290075450749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2930290679312386767267665 2197718009484290075450749)
    ·
      refine ⟨824144253556608778294031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2197718009484290075450749 824144253556608778294031)
      ·
        refine ⟨1236216380334913167441047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824144253556608778294031 1236216380334913167441047)
        ·
          refine ⟨1854324570502369751161571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236216380334913167441047 1854324570502369751161571)
          ·
            refine ⟨2781486855753554626742357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854324570502369751161571 2781486855753554626742357)
            ·
              refine ⟨32595549090861968282137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2781486855753554626742357 32595549090861968282137)
              ·
                rfl

theorem cell21_1285462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 8].length) (baseStart_1285462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285462 prefixEnd_1285462 := by exact prefixLift 1285462
  have htrace : WordTrace (prefixWord ++ tailWord_1285462) baseStart_1285462 baseEnd_1285462 := by
    simpa [prefixWord, tailWord_1285462, baseEnd_1285462] using wordTrace_append hprefix tailTrace_1285462
  have hstable : (prefixWord ++ tailWord_1285462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285462).length < 2 ^ (prefixWord ++ tailWord_1285462).sum := by decide
  have hdescent : baseEnd_1285462 < baseStart_1285462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285501 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1285501 : Nat := 118140960795 + 1285501 * 2 ^ 59
def prefixEnd_1285501 : Nat := 4983230072969 + 3 ^ 40 * 1285501 * 2
def baseEnd_1285501 : Nat := 293368842149102313389153

theorem tailTrace_1285501 : CollatzResearch.WordTrace tailWord_1285501 prefixEnd_1285501 293368842149102313389153 := by
  unfold tailWord_1285501
  simp only [CollatzResearch.WordTrace]
  refine ⟨46886073315856897936952357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31257382210571265291301571 46886073315856897936952357)
  ·
    refine ⟨8791138746723168363178567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46886073315856897936952357 8791138746723168363178567)
    ·
      refine ⟨13186708120084752544767851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791138746723168363178567 13186708120084752544767851)
      ·
        refine ⟨19780062180127128817151777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13186708120084752544767851 19780062180127128817151777)
        ·
          refine ⟨14835046635095346612863833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19780062180127128817151777 14835046635095346612863833)
          ·
            refine ⟨11126284976321509959647875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14835046635095346612863833 11126284976321509959647875)
            ·
              refine ⟨16689427464482264939471813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126284976321509959647875 16689427464482264939471813)
              ·
                refine ⟨3129267649590424676150965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16689427464482264939471813 3129267649590424676150965)
                ·
                  refine ⟨293368842149102313389153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129267649590424676150965 293368842149102313389153)
                  ·
                    rfl

theorem cell21_1285501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1285501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285501 prefixEnd_1285501 := by exact prefixLift 1285501
  have htrace : WordTrace (prefixWord ++ tailWord_1285501) baseStart_1285501 baseEnd_1285501 := by
    simpa [prefixWord, tailWord_1285501, baseEnd_1285501] using wordTrace_append hprefix tailTrace_1285501
  have hstable : (prefixWord ++ tailWord_1285501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285501).length < 2 ^ (prefixWord ++ tailWord_1285501).sum := by decide
  have hdescent : baseEnd_1285501 < baseStart_1285501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285515 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_1285515 : Nat := 118140960795 + 1285515 * 2 ^ 59
def prefixEnd_1285515 : Nat := 4983230072969 + 3 ^ 40 * 1285515 * 2
def baseEnd_1285515 : Nat := 293372037139841400155791

theorem tailTrace_1285515 : CollatzResearch.WordTrace tailWord_1285515 prefixEnd_1285515 293372037139841400155791 := by
  unfold tailWord_1285515
  simp only [CollatzResearch.WordTrace]
  refine ⟨46886583937806178327961999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31257722625204118885307999 46886583937806178327961999)
  ·
    refine ⟨70329875906709267491942999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46886583937806178327961999 70329875906709267491942999)
    ·
      refine ⟨105494813860063901237914499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70329875906709267491942999 105494813860063901237914499)
      ·
        refine ⟨158242220790095851856871749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105494813860063901237914499 158242220790095851856871749)
        ·
          refine ⟨29670416398142972223163453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158242220790095851856871749 29670416398142972223163453)
          ·
            refine ⟨11126406149303614583686295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29670416398142972223163453 11126406149303614583686295)
            ·
              refine ⟨16689609223955421875529443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126406149303614583686295 16689609223955421875529443)
              ·
                refine ⟨25034413835933132813294165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16689609223955421875529443 25034413835933132813294165)
                ·
                  refine ⟨293372037139841400155791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25034413835933132813294165 293372037139841400155791)
                  ·
                    rfl

theorem cell21_1285515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_1285515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285515 prefixEnd_1285515 := by exact prefixLift 1285515
  have htrace : WordTrace (prefixWord ++ tailWord_1285515) baseStart_1285515 baseEnd_1285515 := by
    simpa [prefixWord, tailWord_1285515, baseEnd_1285515] using wordTrace_append hprefix tailTrace_1285515
  have hstable : (prefixWord ++ tailWord_1285515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285515).length < 2 ^ (prefixWord ++ tailWord_1285515).sum := by decide
  have hdescent : baseEnd_1285515 < baseStart_1285515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285591 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_1285591 : Nat := 118140960795 + 1285591 * 2 ^ 59
def prefixEnd_1285591 : Nat := 4983230072969 + 3 ^ 40 * 1285591 * 2
def baseEnd_1285591 : Nat := 293389381375282156888969

theorem tailTrace_1285591 : CollatzResearch.WordTrace tailWord_1285591 prefixEnd_1285591 293389381375282156888969 := by
  unfold tailWord_1285591
  simp only [CollatzResearch.WordTrace]
  refine ⟨46889355885530843307728627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31259570590353895538485751 46889355885530843307728627)
  ·
    refine ⟨70334033828296264961592941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46889355885530843307728627 70334033828296264961592941)
    ·
      refine ⟨26375262685611099360597353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70334033828296264961592941 26375262685611099360597353)
      ·
        refine ⟨19781447014208324520448015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26375262685611099360597353 19781447014208324520448015)
        ·
          refine ⟨29672170521312486780672023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19781447014208324520448015 29672170521312486780672023)
          ·
            refine ⟨44508255781968730171008035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29672170521312486780672023 44508255781968730171008035)
            ·
              refine ⟨66762383672953095256512053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44508255781968730171008035 66762383672953095256512053)
              ·
                refine ⟨6258973469339352680298005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66762383672953095256512053 6258973469339352680298005)
                ·
                  refine ⟨293389381375282156888969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6258973469339352680298005 293389381375282156888969)
                  ·
                    rfl

theorem cell21_1285591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_1285591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285591 prefixEnd_1285591 := by exact prefixLift 1285591
  have htrace : WordTrace (prefixWord ++ tailWord_1285591) baseStart_1285591 baseEnd_1285591 := by
    simpa [prefixWord, tailWord_1285591, baseEnd_1285591] using wordTrace_append hprefix tailTrace_1285591
  have hstable : (prefixWord ++ tailWord_1285591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285591).length < 2 ^ (prefixWord ++ tailWord_1285591).sum := by decide
  have hdescent : baseEnd_1285591 < baseStart_1285591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285608 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_1285608 : Nat := 118140960795 + 1285608 * 2 ^ 59
def prefixEnd_1285608 : Nat := 4983230072969 + 3 ^ 40 * 1285608 * 2
def baseEnd_1285608 : Nat := 293393261006893905105601

theorem tailTrace_1285608 : CollatzResearch.WordTrace tailWord_1285608 prefixEnd_1285608 293393261006893905105601 := by
  unfold tailWord_1285608
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444987963234627605548739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31259983950979503474064985 23444987963234627605548739)
  ·
    refine ⟨35167481944851941408323109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23444987963234627605548739 35167481944851941408323109)
    ·
      refine ⟨6593902864659739014060583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35167481944851941408323109 6593902864659739014060583)
      ·
        refine ⟨9890854296989608521090875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593902864659739014060583 9890854296989608521090875)
        ·
          refine ⟨14836281445484412781636313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890854296989608521090875 14836281445484412781636313)
          ·
            refine ⟨11127211084113309586227235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14836281445484412781636313 11127211084113309586227235)
            ·
              refine ⟨16690816626169964379340853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11127211084113309586227235 16690816626169964379340853)
              ·
                refine ⟨1564764058703434160563205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16690816626169964379340853 1564764058703434160563205)
                ·
                  refine ⟨293393261006893905105601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564764058703434160563205 293393261006893905105601)
                  ·
                    rfl

theorem cell21_1285608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_1285608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285608 prefixEnd_1285608 := by exact prefixLift 1285608
  have htrace : WordTrace (prefixWord ++ tailWord_1285608) baseStart_1285608 baseEnd_1285608 := by
    simpa [prefixWord, tailWord_1285608, baseEnd_1285608] using wordTrace_append hprefix tailTrace_1285608
  have hstable : (prefixWord ++ tailWord_1285608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285608).length < 2 ^ (prefixWord ++ tailWord_1285608).sum := by decide
  have hdescent : baseEnd_1285608 < baseStart_1285608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285653 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1285653 : Nat := 118140960795 + 1285653 * 2 ^ 59
def prefixEnd_1285653 : Nat := 4983230072969 + 3 ^ 40 * 1285653 * 2
def baseEnd_1285653 : Nat := 293403530619983826855509

theorem tailTrace_1285653 : CollatzResearch.WordTrace tailWord_1285653 prefixEnd_1285653 293403530619983826855509 := by
  unfold tailWord_1285653
  simp only [CollatzResearch.WordTrace]
  refine ⟨46891617211306227896485613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31261078140870818597657075 46891617211306227896485613)
  ·
    refine ⟨17584356454239835461182105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46891617211306227896485613 17584356454239835461182105)
    ·
      refine ⟨13188267340679876595886579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17584356454239835461182105 13188267340679876595886579)
      ·
        refine ⟨19782401011019814893829869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13188267340679876595886579 19782401011019814893829869)
        ·
          refine ⟨7418400379132430585186201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19782401011019814893829869 7418400379132430585186201)
          ·
            refine ⟨5563800284349322938889651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418400379132430585186201 5563800284349322938889651)
            ·
              refine ⟨8345700426523984408334477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563800284349322938889651 8345700426523984408334477)
              ·
                refine ⟨3129637659946494153125429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8345700426523984408334477 3129637659946494153125429)
                ·
                  refine ⟨293403530619983826855509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129637659946494153125429 293403530619983826855509)
                  ·
                    rfl

theorem cell21_1285653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1285653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285653 prefixEnd_1285653 := by exact prefixLift 1285653
  have htrace : WordTrace (prefixWord ++ tailWord_1285653) baseStart_1285653 baseEnd_1285653 := by
    simpa [prefixWord, tailWord_1285653, baseEnd_1285653] using wordTrace_append hprefix tailTrace_1285653
  have hstable : (prefixWord ++ tailWord_1285653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285653).length < 2 ^ (prefixWord ++ tailWord_1285653).sum := by decide
  have hdescent : baseEnd_1285653 < baseStart_1285653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285687 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 3]
def baseStart_1285687 : Nat := 118140960795 + 1285687 * 2 ^ 59
def prefixEnd_1285687 : Nat := 4983230072969 + 3 ^ 40 * 1285687 * 2
def baseEnd_1285687 : Nat := 293411289883207323288773

theorem tailTrace_1285687 : CollatzResearch.WordTrace tailWord_1285687 prefixEnd_1285687 293411289883207323288773 := by
  unfold tailWord_1285687
  simp only [CollatzResearch.WordTrace]
  refine ⟨46892857293183051703223315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31261904862122034468815543 46892857293183051703223315)
  ·
    refine ⟨70339285939774577554834973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46892857293183051703223315 70339285939774577554834973)
    ·
      refine ⟨26377232227415466583063115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70339285939774577554834973 26377232227415466583063115)
      ·
        refine ⟨39565848341123199874594673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26377232227415466583063115 39565848341123199874594673)
        ·
          refine ⟨29674386255842399905946005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39565848341123199874594673 29674386255842399905946005)
          ·
            refine ⟨1390986855742612495591219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29674386255842399905946005 1390986855742612495591219)
            ·
              refine ⟨2086480283613918743386829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390986855742612495591219 2086480283613918743386829)
              ·
                refine ⟨782430106355219528770061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2086480283613918743386829 782430106355219528770061)
                ·
                  refine ⟨293411289883207323288773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782430106355219528770061 293411289883207323288773)
                  ·
                    rfl

theorem cell21_1285687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3].length) (baseStart_1285687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285687 prefixEnd_1285687 := by exact prefixLift 1285687
  have htrace : WordTrace (prefixWord ++ tailWord_1285687) baseStart_1285687 baseEnd_1285687 := by
    simpa [prefixWord, tailWord_1285687, baseEnd_1285687] using wordTrace_append hprefix tailTrace_1285687
  have hstable : (prefixWord ++ tailWord_1285687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285687).length < 2 ^ (prefixWord ++ tailWord_1285687).sum := by decide
  have hdescent : baseEnd_1285687 < baseStart_1285687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285760 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_1285760 : Nat := 118140960795 + 1285760 * 2 ^ 59
def prefixEnd_1285760 : Nat := 4983230072969 + 3 ^ 40 * 1285760 * 2
def baseEnd_1285760 : Nat := 293427949477775418571957

theorem tailTrace_1285760 : CollatzResearch.WordTrace tailWord_1285760 prefixEnd_1285760 293427949477775418571957 := by
  unfold tailWord_1285760
  simp only [CollatzResearch.WordTrace]
  refine ⟨23447759910959292585315367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31263679881279056780420489 23447759910959292585315367)
  ·
    refine ⟨35171639866438938877973051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23447759910959292585315367 35171639866438938877973051)
    ·
      refine ⟨52757459799658408316959577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35171639866438938877973051 52757459799658408316959577)
      ·
        refine ⟨39568094849743806237719683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52757459799658408316959577 39568094849743806237719683)
        ·
          refine ⟨59352142274615709356579525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39568094849743806237719683 59352142274615709356579525)
          ·
            refine ⟨11128526676490445504358661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59352142274615709356579525 11128526676490445504358661)
            ·
              refine ⟨2086598751841958532067249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11128526676490445504358661 2086598751841958532067249)
              ·
                refine ⟨1564949063881468899050437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086598751841958532067249 1564949063881468899050437)
                ·
                  refine ⟨293427949477775418571957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564949063881468899050437 293427949477775418571957)
                  ·
                    rfl

theorem cell21_1285760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_1285760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285760 prefixEnd_1285760 := by exact prefixLift 1285760
  have htrace : WordTrace (prefixWord ++ tailWord_1285760) baseStart_1285760 baseEnd_1285760 := by
    simpa [prefixWord, tailWord_1285760, baseEnd_1285760] using wordTrace_append hprefix tailTrace_1285760
  have hstable : (prefixWord ++ tailWord_1285760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285760).length < 2 ^ (prefixWord ++ tailWord_1285760).sum := by decide
  have hdescent : baseEnd_1285760 < baseStart_1285760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285805 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1285805 : Nat := 118140960795 + 1285805 * 2 ^ 59
def prefixEnd_1285805 : Nat := 4983230072969 + 3 ^ 40 * 1285805 * 2
def baseEnd_1285805 : Nat := 293438219090865340321865

theorem tailTrace_1285805 : CollatzResearch.WordTrace tailWord_1285805 prefixEnd_1285805 293438219090865340321865 := by
  unfold tailWord_1285805
  simp only [CollatzResearch.WordTrace]
  refine ⟨46897161106755557856018869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31264774071170371904012579 46897161106755557856018869)
  ·
    refine ⟨4396608853758333549001769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46897161106755557856018869 4396608853758333549001769)
    ·
      refine ⟨3297456640318750161751327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4396608853758333549001769 3297456640318750161751327)
      ·
        refine ⟨4946184960478125242626991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297456640318750161751327 4946184960478125242626991)
        ·
          refine ⟨7419277440717187863940487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946184960478125242626991 7419277440717187863940487)
          ·
            refine ⟨11128916161075781795910731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419277440717187863940487 11128916161075781795910731)
            ·
              refine ⟨16693374241613672693866097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11128916161075781795910731 16693374241613672693866097)
              ·
                refine ⟨12520030681210254520399573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16693374241613672693866097 12520030681210254520399573)
                ·
                  refine ⟨293438219090865340321865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12520030681210254520399573 293438219090865340321865)
                  ·
                    rfl

theorem cell21_1285805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1285805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285805 prefixEnd_1285805 := by exact prefixLift 1285805
  have htrace : WordTrace (prefixWord ++ tailWord_1285805) baseStart_1285805 baseEnd_1285805 := by
    simpa [prefixWord, tailWord_1285805, baseEnd_1285805] using wordTrace_append hprefix tailTrace_1285805
  have hstable : (prefixWord ++ tailWord_1285805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285805).length < 2 ^ (prefixWord ++ tailWord_1285805).sum := by decide
  have hdescent : baseEnd_1285805 < baseStart_1285805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285822 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1285822 : Nat := 118140960795 + 1285822 * 2 ^ 59
def prefixEnd_1285822 : Nat := 4983230072969 + 3 ^ 40 * 1285822 * 2
def baseEnd_1285822 : Nat := 293442098722477088538497

theorem tailTrace_1285822 : CollatzResearch.WordTrace tailWord_1285822 prefixEnd_1285822 293442098722477088538497 := by
  unfold tailWord_1285822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862222643461746219923465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31265187431795979839591813 5862222643461746219923465)
  ·
    refine ⟨4396666982596309664942599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5862222643461746219923465 4396666982596309664942599)
    ·
      refine ⟨6595000473894464497413899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396666982596309664942599 6595000473894464497413899)
      ·
        refine ⟨9892500710841696746120849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6595000473894464497413899 9892500710841696746120849)
        ·
          refine ⟨7419375533131272559590637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9892500710841696746120849 7419375533131272559590637)
          ·
            refine ⟨2782265824924227209846489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7419375533131272559590637 2782265824924227209846489)
            ·
              refine ⟨2086699368693170407384867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782265824924227209846489 2086699368693170407384867)
              ·
                refine ⟨3130049053039755611077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086699368693170407384867 3130049053039755611077301)
                ·
                  refine ⟨293442098722477088538497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130049053039755611077301 293442098722477088538497)
                  ·
                    rfl

theorem cell21_1285822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1285822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285822 prefixEnd_1285822 := by exact prefixLift 1285822
  have htrace : WordTrace (prefixWord ++ tailWord_1285822) baseStart_1285822 baseEnd_1285822 := by
    simpa [prefixWord, tailWord_1285822, baseEnd_1285822] using wordTrace_append hprefix tailTrace_1285822
  have hstable : (prefixWord ++ tailWord_1285822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285822).length < 2 ^ (prefixWord ++ tailWord_1285822).sum := by decide
  have hdescent : baseEnd_1285822 < baseStart_1285822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285850 : List Nat := [3, 1, 1, 2, 2, 4, 1, 7]
def baseStart_1285850 : Nat := 118140960795 + 1285850 * 2 ^ 59
def prefixEnd_1285850 : Nat := 4983230072969 + 3 ^ 40 * 1285850 * 2
def baseEnd_1285850 : Nat := 97816162901318420690591

theorem tailTrace_1285850 : CollatzResearch.WordTrace tailWord_1285850 prefixEnd_1285850 97816162901318420690591 := by
  unfold tailWord_1285850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724700597898132635351751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31265868261061687027604669 11724700597898132635351751)
  ·
    refine ⟨17587050896847198953027627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11724700597898132635351751 17587050896847198953027627)
    ·
      refine ⟨26380576345270798429541441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17587050896847198953027627 26380576345270798429541441)
      ·
        refine ⟨19785432258953098822156081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26380576345270798429541441 19785432258953098822156081)
        ·
          refine ⟨14839074194214824116617061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19785432258953098822156081 14839074194214824116617061)
          ·
            refine ⟨2782326411415279521865699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14839074194214824116617061 2782326411415279521865699)
            ·
              refine ⟨4173489617122919282798549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782326411415279521865699 4173489617122919282798549)
              ·
                refine ⟨97816162901318420690591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4173489617122919282798549 97816162901318420690591)
                ·
                  rfl

theorem cell21_1285850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_1285850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285850 prefixEnd_1285850 := by exact prefixLift 1285850
  have htrace : WordTrace (prefixWord ++ tailWord_1285850) baseStart_1285850 baseEnd_1285850 := by
    simpa [prefixWord, tailWord_1285850, baseEnd_1285850] using wordTrace_append hprefix tailTrace_1285850
  have hstable : (prefixWord ++ tailWord_1285850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285850).length < 2 ^ (prefixWord ++ tailWord_1285850).sum := by decide
  have hdescent : baseEnd_1285850 < baseStart_1285850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285985 : List Nat := [1, 2, 3, 1, 1, 1, 12]
def baseStart_1285985 : Nat := 118140960795 + 1285985 * 2 ^ 59
def prefixEnd_1285985 : Nat := 4983230072969 + 3 ^ 40 * 1285985 * 2
def baseEnd_1285985 : Nat := 32608810838136114146833

theorem tailTrace_1285985 : CollatzResearch.WordTrace tailWord_1285985 prefixEnd_1285985 32608810838136114146833 := by
  unfold tailWord_1285985
  simp only [CollatzResearch.WordTrace]
  refine ⟨46903726246103448597571409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31269150830735632398380939 46903726246103448597571409)
  ·
    refine ⟨35177794684577586448178557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46903726246103448597571409 35177794684577586448178557)
    ·
      refine ⟨13191673006716594918066959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35177794684577586448178557 13191673006716594918066959)
      ·
        refine ⟨19787509510074892377100439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13191673006716594918066959 19787509510074892377100439)
        ·
          refine ⟨29681264265112338565650659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19787509510074892377100439 29681264265112338565650659)
          ·
            refine ⟨44521896397668507848475989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29681264265112338565650659 44521896397668507848475989)
            ·
              refine ⟨32608810838136114146833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44521896397668507848475989 32608810838136114146833)
              ·
                rfl

theorem cell21_1285985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 12].length) (baseStart_1285985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285985 prefixEnd_1285985 := by exact prefixLift 1285985
  have htrace : WordTrace (prefixWord ++ tailWord_1285985) baseStart_1285985 baseEnd_1285985 := by
    simpa [prefixWord, tailWord_1285985, baseEnd_1285985] using wordTrace_append hprefix tailTrace_1285985
  have hstable : (prefixWord ++ tailWord_1285985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285985).length < 2 ^ (prefixWord ++ tailWord_1285985).sum := by decide
  have hdescent : baseEnd_1285985 < baseStart_1285985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285988 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1285988 : Nat := 118140960795 + 1285988 * 2 ^ 59
def prefixEnd_1285988 : Nat := 4983230072969 + 3 ^ 40 * 1285988 * 2
def baseEnd_1285988 : Nat := 293479982184097688771491

theorem tailTrace_1285988 : CollatzResearch.WordTrace tailWord_1285988 prefixEnd_1285988 293479982184097688771491 := by
  unfold tailWord_1285988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451917832546290054965309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31269223776728386739953745 23451917832546290054965309)
  ·
    refine ⟨8794469187204858770611991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23451917832546290054965309 8794469187204858770611991)
    ·
      refine ⟨13191703780807288155917987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8794469187204858770611991 13191703780807288155917987)
      ·
        refine ⟨19787555671210932233876981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13191703780807288155917987 19787555671210932233876981)
        ·
          refine ⟨1855083344176024896925967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19787555671210932233876981 1855083344176024896925967)
          ·
            refine ⟨2782625016264037345388951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855083344176024896925967 2782625016264037345388951)
            ·
              refine ⟨4173937524396056018083427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782625016264037345388951 4173937524396056018083427)
              ·
                refine ⟨6260906286594084027125141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173937524396056018083427 6260906286594084027125141)
                ·
                  refine ⟨293479982184097688771491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6260906286594084027125141 293479982184097688771491)
                  ·
                    rfl

theorem cell21_1285988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1285988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1285988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1285988 prefixEnd_1285988 := by exact prefixLift 1285988
  have htrace : WordTrace (prefixWord ++ tailWord_1285988) baseStart_1285988 baseEnd_1285988 := by
    simpa [prefixWord, tailWord_1285988, baseEnd_1285988] using wordTrace_append hprefix tailTrace_1285988
  have hstable : (prefixWord ++ tailWord_1285988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285988).length < 2 ^ (prefixWord ++ tailWord_1285988).sum := by decide
  have hdescent : baseEnd_1285988 < baseStart_1285988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286005 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1286005 : Nat := 118140960795 + 1286005 * 2 ^ 59
def prefixEnd_1286005 : Nat := 4983230072969 + 3 ^ 40 * 1286005 * 2
def baseEnd_1286005 : Nat := 293483861815709436988123

theorem tailTrace_1286005 : CollatzResearch.WordTrace tailWord_1286005 prefixEnd_1286005 293483861815709436988123 := by
  unfold tailWord_1286005
  simp only [CollatzResearch.WordTrace]
  refine ⟨46904455706030992013299469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31269637137353994675532979 46904455706030992013299469)
  ·
    refine ⟨17589170889761622004987301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46904455706030992013299469 17589170889761622004987301)
    ·
      refine ⟨3297969541830304125935119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17589170889761622004987301 3297969541830304125935119)
      ·
        refine ⟨4946954312745456188902679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297969541830304125935119 4946954312745456188902679)
        ·
          refine ⟨7420431469118184283354019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946954312745456188902679 7420431469118184283354019)
          ·
            refine ⟨11130647203677276425031029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420431469118184283354019 11130647203677276425031029)
            ·
              refine ⟨1043498175344744664846659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11130647203677276425031029 1043498175344744664846659)
              ·
                refine ⟨1565247263017116997269989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043498175344744664846659 1565247263017116997269989)
                ·
                  refine ⟨293483861815709436988123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565247263017116997269989 293483861815709436988123)
                  ·
                    rfl

theorem cell21_1286005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1286005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286005 prefixEnd_1286005 := by exact prefixLift 1286005
  have htrace : WordTrace (prefixWord ++ tailWord_1286005) baseStart_1286005 baseEnd_1286005 := by
    simpa [prefixWord, tailWord_1286005, baseEnd_1286005] using wordTrace_append hprefix tailTrace_1286005
  have hstable : (prefixWord ++ tailWord_1286005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286005).length < 2 ^ (prefixWord ++ tailWord_1286005).sum := by decide
  have hdescent : baseEnd_1286005 < baseStart_1286005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286016 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1286016 : Nat := 118140960795 + 1286016 * 2 ^ 59
def prefixEnd_1286016 : Nat := 4983230072969 + 3 ^ 40 * 1286016 * 2
def baseEnd_1286016 : Nat := 293486372165575862304767

theorem tailTrace_1286016 : CollatzResearch.WordTrace tailWord_1286016 prefixEnd_1286016 293486372165575862304767 := by
  unfold tailWord_1286016
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452428454495570445974951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31269904605994093927966601 23452428454495570445974951)
  ·
    refine ⟨35178642681743355668962427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23452428454495570445974951 35178642681743355668962427)
    ·
      refine ⟨52767964022615033503443641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35178642681743355668962427 52767964022615033503443641)
      ·
        refine ⟨39575973016961275127582731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52767964022615033503443641 39575973016961275127582731)
        ·
          refine ⟨59363959525441912691374097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39575973016961275127582731 59363959525441912691374097)
          ·
            refine ⟨44522969644081434518530573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59363959525441912691374097 44522969644081434518530573)
            ·
              refine ⟨16696113616530537944448965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44522969644081434518530573 16696113616530537944448965)
              ·
                refine ⟨3130521303099475864584181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16696113616530537944448965 3130521303099475864584181)
                ·
                  refine ⟨293486372165575862304767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130521303099475864584181 293486372165575862304767)
                  ·
                    rfl

theorem cell21_1286016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1286016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286016 prefixEnd_1286016 := by exact prefixLift 1286016
  have htrace : WordTrace (prefixWord ++ tailWord_1286016) baseStart_1286016 baseEnd_1286016 := by
    simpa [prefixWord, tailWord_1286016, baseEnd_1286016] using wordTrace_append hprefix tailTrace_1286016
  have hstable : (prefixWord ++ tailWord_1286016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286016).length < 2 ^ (prefixWord ++ tailWord_1286016).sum := by decide
  have hdescent : baseEnd_1286016 < baseStart_1286016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286019 : List Nat := [1, 1, 1, 3, 4, 4, 2, 5]
def baseStart_1286019 : Nat := 118140960795 + 1286019 * 2 ^ 59
def prefixEnd_1286019 : Nat := 4983230072969 + 3 ^ 40 * 1286019 * 2
def baseEnd_1286019 : Nat := 97829018935482841251587

theorem tailTrace_1286019 : CollatzResearch.WordTrace tailWord_1286019 prefixEnd_1286019 97829018935482841251587 := by
  unfold tailWord_1286019
  simp only [CollatzResearch.WordTrace]
  refine ⟨46904966327980272404309111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31269977551986848269539407 46904966327980272404309111)
  ·
    refine ⟨70357449491970408606463667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46904966327980272404309111 70357449491970408606463667)
    ·
      refine ⟨105536174237955612909695501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70357449491970408606463667 105536174237955612909695501)
      ·
        refine ⟨39576065339233354841135813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105536174237955612909695501 39576065339233354841135813)
        ·
          refine ⟨7420512251106254032712965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39576065339233354841135813 7420512251106254032712965)
          ·
            refine ⟨1391346047082422631133681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7420512251106254032712965 1391346047082422631133681)
            ·
              refine ⟨1043509535311816973350261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391346047082422631133681 1043509535311816973350261)
              ·
                refine ⟨97829018935482841251587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1043509535311816973350261 97829018935482841251587)
                ·
                  rfl

theorem cell21_1286019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 5].length) (baseStart_1286019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286019 prefixEnd_1286019 := by exact prefixLift 1286019
  have htrace : WordTrace (prefixWord ++ tailWord_1286019) baseStart_1286019 baseEnd_1286019 := by
    simpa [prefixWord, tailWord_1286019, baseEnd_1286019] using wordTrace_append hprefix tailTrace_1286019
  have hstable : (prefixWord ++ tailWord_1286019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286019).length < 2 ^ (prefixWord ++ tailWord_1286019).sum := by decide
  have hdescent : baseEnd_1286019 < baseStart_1286019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286056 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_1286056 : Nat := 118140960795 + 1286056 * 2 ^ 59
def prefixEnd_1286056 : Nat := 4983230072969 + 3 ^ 40 * 1286056 * 2
def baseEnd_1286056 : Nat := 293495500710544681638019

theorem tailTrace_1286056 : CollatzResearch.WordTrace tailWord_1286056 prefixEnd_1286056 293495500710544681638019 := by
  unfold tailWord_1286056
  simp only [CollatzResearch.WordTrace]
  refine ⟨23453157914423113861703011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31270877219230818482270681 23453157914423113861703011)
  ·
    refine ⟨35179736871634670792554517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23453157914423113861703011 35179736871634670792554517)
    ·
      refine ⟨1649050165857875193400993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35179736871634670792554517 1649050165857875193400993)
      ·
        refine ⟨1236787624393406395050745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649050165857875193400993 1236787624393406395050745)
        ·
          refine ⟨927590718295054796288059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236787624393406395050745 927590718295054796288059)
          ·
            refine ⟨1391386077442582194432089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927590718295054796288059 1391386077442582194432089)
            ·
              refine ⟨1043539558081936645824067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391386077442582194432089 1043539558081936645824067)
              ·
                refine ⟨1565309337122904968736101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043539558081936645824067 1565309337122904968736101)
                ·
                  refine ⟨293495500710544681638019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565309337122904968736101 293495500710544681638019)
                  ·
                    rfl

theorem cell21_1286056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_1286056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286056 prefixEnd_1286056 := by exact prefixLift 1286056
  have htrace : WordTrace (prefixWord ++ tailWord_1286056) baseStart_1286056 baseEnd_1286056 := by
    simpa [prefixWord, tailWord_1286056, baseEnd_1286056] using wordTrace_append hprefix tailTrace_1286056
  have hstable : (prefixWord ++ tailWord_1286056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286056).length < 2 ^ (prefixWord ++ tailWord_1286056).sum := by decide
  have hdescent : baseEnd_1286056 < baseStart_1286056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286078 : List Nat := [4, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1286078 : Nat := 118140960795 + 1286078 * 2 ^ 59
def prefixEnd_1286078 : Nat := 4983230072969 + 3 ^ 40 * 1286078 * 2
def baseEnd_1286078 : Nat := 97833507136759177423769

theorem tailTrace_1286078 : CollatzResearch.WordTrace tailWord_1286078 prefixEnd_1286078 97833507136759177423769 := by
  unfold tailWord_1286078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863389779345815685088361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31271412156511016987137925 5863389779345815685088361)
  ·
    refine ⟨4397542334509361763816271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5863389779345815685088361 4397542334509361763816271)
    ·
      refine ⟨6596313501764042645724407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397542334509361763816271 6596313501764042645724407)
      ·
        refine ⟨9894470252646063968586611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596313501764042645724407 9894470252646063968586611)
        ·
          refine ⟨14841705378969095952879917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894470252646063968586611 14841705378969095952879917)
          ·
            refine ⟨5565639517113410982329969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14841705378969095952879917 5565639517113410982329969)
            ·
              refine ⟨4174229637835058236747477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5565639517113410982329969 4174229637835058236747477)
              ·
                refine ⟨97833507136759177423769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4174229637835058236747477 97833507136759177423769)
                ·
                  rfl

theorem cell21_1286078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1286078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286078 prefixEnd_1286078 := by exact prefixLift 1286078
  have htrace : WordTrace (prefixWord ++ tailWord_1286078) baseStart_1286078 baseEnd_1286078 := by
    simpa [prefixWord, tailWord_1286078, baseEnd_1286078] using wordTrace_append hprefix tailTrace_1286078
  have hstable : (prefixWord ++ tailWord_1286078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286078).length < 2 ^ (prefixWord ++ tailWord_1286078).sum := by decide
  have hdescent : baseEnd_1286078 < baseStart_1286078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286154 : List Nat := [3, 1, 2, 2, 4, 1, 8]
def baseStart_1286154 : Nat := 118140960795 + 1286154 * 2 ^ 59
def prefixEnd_1286154 : Nat := 4983230072969 + 3 ^ 40 * 1286154 * 2
def baseEnd_1286154 : Nat := 32613096182857587667165

theorem tailTrace_1286154 : CollatzResearch.WordTrace tailWord_1286154 prefixEnd_1286154 32613096182857587667165 := by
  unfold tailWord_1286154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727472545622797615118379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31273260121660793640315677 11727472545622797615118379)
  ·
    refine ⟨17591208818434196422677569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11727472545622797615118379 17591208818434196422677569)
    ·
      refine ⟨13193406613825647317008177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17591208818434196422677569 13193406613825647317008177)
      ·
        refine ⟨9895054960369235487756133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13193406613825647317008177 9895054960369235487756133)
        ·
          refine ⟨1855322805069231653954275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9895054960369235487756133 1855322805069231653954275)
          ·
            refine ⟨2782984207603847480931413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855322805069231653954275 2782984207603847480931413)
            ·
              refine ⟨32613096182857587667165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2782984207603847480931413 32613096182857587667165)
              ·
                rfl

theorem cell21_1286154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 8].length) (baseStart_1286154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286154 prefixEnd_1286154 := by exact prefixLift 1286154
  have htrace : WordTrace (prefixWord ++ tailWord_1286154) baseStart_1286154 baseEnd_1286154 := by
    simpa [prefixWord, tailWord_1286154, baseEnd_1286154] using wordTrace_append hprefix tailTrace_1286154
  have hstable : (prefixWord ++ tailWord_1286154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286154).length < 2 ^ (prefixWord ++ tailWord_1286154).sum := by decide
  have hdescent : baseEnd_1286154 < baseStart_1286154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286244 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1286244 : Nat := 118140960795 + 1286244 * 2 ^ 59
def prefixEnd_1286244 : Nat := 4983230072969 + 3 ^ 40 * 1286244 * 2
def baseEnd_1286244 : Nat := 293538404871898132504301

theorem tailTrace_1286244 : CollatzResearch.WordTrace tailWord_1286244 prefixEnd_1286244 293538404871898132504301 := by
  unfold tailWord_1286244
  simp only [CollatzResearch.WordTrace]
  refine ⟨23456586376082567915624893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31275448501443423887499857 23456586376082567915624893)
  ·
    refine ⟨8796219891030962968359335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23456586376082567915624893 8796219891030962968359335)
    ·
      refine ⟨13194329836546444452539003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796219891030962968359335 13194329836546444452539003)
      ·
        refine ⟨19791494754819666678808505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194329836546444452539003 19791494754819666678808505)
        ·
          refine ⟨14843621066114750009106379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19791494754819666678808505 14843621066114750009106379)
          ·
            refine ⟨22265431599172125013659569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14843621066114750009106379 22265431599172125013659569)
            ·
              refine ⟨16699073699379093760244677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22265431599172125013659569 16699073699379093760244677)
              ·
                refine ⟨3131076318633580080045877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16699073699379093760244677 3131076318633580080045877)
                ·
                  refine ⟨293538404871898132504301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3131076318633580080045877 293538404871898132504301)
                  ·
                    rfl

theorem cell21_1286244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1286244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286244 prefixEnd_1286244 := by exact prefixLift 1286244
  have htrace : WordTrace (prefixWord ++ tailWord_1286244) baseStart_1286244 baseEnd_1286244 := by
    simpa [prefixWord, tailWord_1286244, baseEnd_1286244] using wordTrace_append hprefix tailTrace_1286244
  have hstable : (prefixWord ++ tailWord_1286244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286244).length < 2 ^ (prefixWord ++ tailWord_1286244).sum := by decide
  have hdescent : baseEnd_1286244 < baseStart_1286244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286275 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_1286275 : Nat := 118140960795 + 1286275 * 2 ^ 59
def prefixEnd_1286275 : Nat := 4983230072969 + 3 ^ 40 * 1286275 * 2
def baseEnd_1286275 : Nat := 293545479494248967487571

theorem tailTrace_1286275 : CollatzResearch.WordTrace tailWord_1286275 prefixEnd_1286275 293545479494248967487571 := by
  unfold tailWord_1286275
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914303415052828125628279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31276202276701885417085519 46914303415052828125628279)
  ·
    refine ⟨70371455122579242188442419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46914303415052828125628279 70371455122579242188442419)
    ·
      refine ⟨105557182683868863282663629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70371455122579242188442419 105557182683868863282663629)
      ·
        refine ⟨39583943506450823730998861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105557182683868863282663629 39583943506450823730998861)
        ·
          refine ⟨14843978814919058899124573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39583943506450823730998861 14843978814919058899124573)
          ·
            refine ⟨5566492055594647087171715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14843978814919058899124573 5566492055594647087171715)
            ·
              refine ⟨8349738083391970630757573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566492055594647087171715 8349738083391970630757573)
              ·
                refine ⟨1565575890635994493267045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8349738083391970630757573 1565575890635994493267045)
                ·
                  refine ⟨293545479494248967487571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565575890635994493267045 293545479494248967487571)
                  ·
                    rfl

theorem cell21_1286275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_1286275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286275 prefixEnd_1286275 := by exact prefixLift 1286275
  have htrace : WordTrace (prefixWord ++ tailWord_1286275) baseStart_1286275 baseEnd_1286275 := by
    simpa [prefixWord, tailWord_1286275, baseEnd_1286275] using wordTrace_append hprefix tailTrace_1286275
  have hstable : (prefixWord ++ tailWord_1286275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286275).length < 2 ^ (prefixWord ++ tailWord_1286275).sum := by decide
  have hdescent : baseEnd_1286275 < baseStart_1286275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286402 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1286402 : Nat := 118140960795 + 1286402 * 2 ^ 59
def prefixEnd_1286402 : Nat := 4983230072969 + 3 ^ 40 * 1286402 * 2
def baseEnd_1286402 : Nat := 293574462624524968870645

theorem tailTrace_1286402 : CollatzResearch.WordTrace tailWord_1286402 prefixEnd_1286402 293574462624524968870645 := by
  unfold tailWord_1286402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11729733871398182203875365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31279290323728485877000973 11729733871398182203875365)
  ·
    refine ⟨2199325100887159163226631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11729733871398182203875365 2199325100887159163226631)
    ·
      refine ⟨3298987651330738744839947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199325100887159163226631 3298987651330738744839947)
      ·
        refine ⟨4948481476996108117259921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298987651330738744839947 4948481476996108117259921)
        ·
          refine ⟨3711361107747081087944941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948481476996108117259921 3711361107747081087944941)
          ·
            refine ⟨1391760415405155407979353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3711361107747081087944941 1391760415405155407979353)
            ·
              refine ⟨1043820311553866555984515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391760415405155407979353 1043820311553866555984515)
              ·
                refine ⟨1565730467330799833976773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043820311553866555984515 1565730467330799833976773)
                ·
                  refine ⟨293574462624524968870645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565730467330799833976773 293574462624524968870645)
                  ·
                    rfl

theorem cell21_1286402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1286402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286402 prefixEnd_1286402 := by exact prefixLift 1286402
  have htrace : WordTrace (prefixWord ++ tailWord_1286402) baseStart_1286402 baseEnd_1286402 := by
    simpa [prefixWord, tailWord_1286402, baseEnd_1286402] using wordTrace_append hprefix tailTrace_1286402
  have hstable : (prefixWord ++ tailWord_1286402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286402).length < 2 ^ (prefixWord ++ tailWord_1286402).sum := by decide
  have hdescent : baseEnd_1286402 < baseStart_1286402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286455 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_1286455 : Nat := 118140960795 + 1286455 * 2 ^ 59
def prefixEnd_1286455 : Nat := 4983230072969 + 3 ^ 40 * 1286455 * 2
def baseEnd_1286455 : Nat := 293586557946608654487203

theorem tailTrace_1286455 : CollatzResearch.WordTrace tailWord_1286455 prefixEnd_1286455 293586557946608654487203 := by
  unfold tailWord_1286455
  simp only [CollatzResearch.WordTrace]
  refine ⟨46920868554400718867180819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31280579036267145911453879 46920868554400718867180819)
  ·
    refine ⟨70381302831601078300771229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46920868554400718867180819 70381302831601078300771229)
    ·
      refine ⟨26392988561850404362789211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70381302831601078300771229 26392988561850404362789211)
      ·
        refine ⟨39589482842775606544183817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26392988561850404362789211 39589482842775606544183817)
        ·
          refine ⟨29692112132081704908137863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39589482842775606544183817 29692112132081704908137863)
          ·
            refine ⟨44538168198122557362206795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29692112132081704908137863 44538168198122557362206795)
            ·
              refine ⟨66807252297183836043310193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44538168198122557362206795 66807252297183836043310193)
              ·
                refine ⟨50105439222887877032482645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66807252297183836043310193 50105439222887877032482645)
                ·
                  refine ⟨293586557946608654487203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50105439222887877032482645 293586557946608654487203)
                  ·
                    rfl

theorem cell21_1286455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_1286455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286455 prefixEnd_1286455 := by exact prefixLift 1286455
  have htrace : WordTrace (prefixWord ++ tailWord_1286455) baseStart_1286455 baseEnd_1286455 := by
    simpa [prefixWord, tailWord_1286455, baseEnd_1286455] using wordTrace_append hprefix tailTrace_1286455
  have hstable : (prefixWord ++ tailWord_1286455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286455).length < 2 ^ (prefixWord ++ tailWord_1286455).sum := by decide
  have hdescent : baseEnd_1286455 < baseStart_1286455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286458 : List Nat := [3, 1, 1, 1, 4, 4, 1, 6]
def baseStart_1286458 : Nat := 118140960795 + 1286458 * 2 ^ 59
def prefixEnd_1286458 : Nat := 4983230072969 + 3 ^ 40 * 1286458 * 2
def baseEnd_1286458 : Nat := 97862414195827105312399

theorem tailTrace_1286458 : CollatzResearch.WordTrace tailWord_1286458 prefixEnd_1286458 97862414195827105312399 := by
  unfold tailWord_1286458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730244493347462594885007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31280651982259900253026685 11730244493347462594885007)
  ·
    refine ⟨17595366740021193892327511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11730244493347462594885007 17595366740021193892327511)
    ·
      refine ⟨26393050110031790838491267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595366740021193892327511 26393050110031790838491267)
      ·
        refine ⟨39589575165047686257736901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26393050110031790838491267 39589575165047686257736901)
        ·
          refine ⟨7423045343446441173325669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39589575165047686257736901 7423045343446441173325669)
          ·
            refine ⟨1391821001896207719998563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7423045343446441173325669 1391821001896207719998563)
            ·
              refine ⟨2087731502844311579997845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391821001896207719998563 2087731502844311579997845)
              ·
                refine ⟨97862414195827105312399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2087731502844311579997845 97862414195827105312399)
                ·
                  rfl

theorem cell21_1286458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_1286458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286458 prefixEnd_1286458 := by exact prefixLift 1286458
  have htrace : WordTrace (prefixWord ++ tailWord_1286458) baseStart_1286458 baseEnd_1286458 := by
    simpa [prefixWord, tailWord_1286458, baseEnd_1286458] using wordTrace_append hprefix tailTrace_1286458
  have hstable : (prefixWord ++ tailWord_1286458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286458).length < 2 ^ (prefixWord ++ tailWord_1286458).sum := by decide
  have hdescent : baseEnd_1286458 < baseStart_1286458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286503 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_1286503 : Nat := 118140960795 + 1286503 * 2 ^ 59
def prefixEnd_1286503 : Nat := 4983230072969 + 3 ^ 40 * 1286503 * 2
def baseEnd_1286503 : Nat := 293597512200571237687105

theorem tailTrace_1286503 : CollatzResearch.WordTrace tailWord_1286503 prefixEnd_1286503 293597512200571237687105 := by
  unfold tailWord_1286503
  simp only [CollatzResearch.WordTrace]
  refine ⟨46922619258226823064928163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31281746172151215376618775 46922619258226823064928163)
  ·
    refine ⟨70383928887340234597392245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46922619258226823064928163 70383928887340234597392245)
    ·
      refine ⟨6598493333188146993505523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70383928887340234597392245 6598493333188146993505523)
      ·
        refine ⟨9897739999782220490258285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598493333188146993505523 9897739999782220490258285)
        ·
          refine ⟨3711652499918332683846857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9897739999782220490258285 3711652499918332683846857)
          ·
            refine ⟨2783739374938749512885143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711652499918332683846857 2783739374938749512885143)
            ·
              refine ⟨4175609062408124269327715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783739374938749512885143 4175609062408124269327715)
              ·
                refine ⟨6263413593612186403991573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175609062408124269327715 6263413593612186403991573)
                ·
                  refine ⟨293597512200571237687105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6263413593612186403991573 293597512200571237687105)
                  ·
                    rfl

theorem cell21_1286503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_1286503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286503 prefixEnd_1286503 := by exact prefixLift 1286503
  have htrace : WordTrace (prefixWord ++ tailWord_1286503) baseStart_1286503 baseEnd_1286503 := by
    simpa [prefixWord, tailWord_1286503, baseEnd_1286503] using wordTrace_append hprefix tailTrace_1286503
  have hstable : (prefixWord ++ tailWord_1286503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286503).length < 2 ^ (prefixWord ++ tailWord_1286503).sum := by decide
  have hdescent : baseEnd_1286503 < baseStart_1286503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286506 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_1286506 : Nat := 118140960795 + 1286506 * 2 ^ 59
def prefixEnd_1286506 : Nat := 4983230072969 + 3 ^ 40 * 1286506 * 2
def baseEnd_1286506 : Nat := 293598196841443899137099

theorem tailTrace_1286506 : CollatzResearch.WordTrace tailWord_1286506 prefixEnd_1286506 293598196841443899137099 := by
  unfold tailWord_1286506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730682169303988644321843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31281819118143969718191581 11730682169303988644321843)
  ·
    refine ⟨17596023253955982966482765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11730682169303988644321843 17596023253955982966482765)
    ·
      refine ⟨6598508720233493612431037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17596023253955982966482765 6598508720233493612431037)
      ·
        refine ⟨2474440770087560104661639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6598508720233493612431037 2474440770087560104661639)
        ·
          refine ⟨3711661155131340156992459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474440770087560104661639 3711661155131340156992459)
          ·
            refine ⟨5567491732697010235488689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711661155131340156992459 5567491732697010235488689)
            ·
              refine ⟨4175618799522757676616517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5567491732697010235488689 4175618799522757676616517)
              ·
                refine ⟨782928524910517064365597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4175618799522757676616517 782928524910517064365597)
                ·
                  refine ⟨293598196841443899137099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782928524910517064365597 293598196841443899137099)
                  ·
                    rfl

theorem cell21_1286506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_1286506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286506 prefixEnd_1286506 := by exact prefixLift 1286506
  have htrace : WordTrace (prefixWord ++ tailWord_1286506) baseStart_1286506 baseEnd_1286506 := by
    simpa [prefixWord, tailWord_1286506, baseEnd_1286506] using wordTrace_append hprefix tailTrace_1286506
  have hstable : (prefixWord ++ tailWord_1286506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286506).length < 2 ^ (prefixWord ++ tailWord_1286506).sum := by decide
  have hdescent : baseEnd_1286506 < baseStart_1286506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286610 : List Nat := [3, 2, 2, 4, 1, 9]
def baseStart_1286610 : Nat := 118140960795 + 1286610 * 2 ^ 59
def prefixEnd_1286610 : Nat := 4983230072969 + 3 ^ 40 * 1286610 * 2
def baseEnd_1286610 : Nat := 10874886335494919607539

theorem tailTrace_1286610 : CollatzResearch.WordTrace tailWord_1286610 prefixEnd_1286610 10874886335494919607539 := by
  unfold tailWord_1286610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731630467209795084768321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31284347912559453559382189 11731630467209795084768321)
  ·
    refine ⟨8798722850407346313576241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11731630467209795084768321 8798722850407346313576241)
    ·
      refine ⟨6599042137805509735182181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8798722850407346313576241 6599042137805509735182181)
      ·
        refine ⟨1237320400838533075346659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6599042137805509735182181 1237320400838533075346659)
        ·
          refine ⟨1855980601257799613019989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237320400838533075346659 1855980601257799613019989)
          ·
            refine ⟨10874886335494919607539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1855980601257799613019989 10874886335494919607539)
            ·
              rfl

theorem cell21_1286610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 9].length) (baseStart_1286610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286610 prefixEnd_1286610 := by exact prefixLift 1286610
  have htrace : WordTrace (prefixWord ++ tailWord_1286610) baseStart_1286610 baseEnd_1286610 := by
    simpa [prefixWord, tailWord_1286610, baseEnd_1286610] using wordTrace_append hprefix tailTrace_1286610
  have hstable : (prefixWord ++ tailWord_1286610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286610).length < 2 ^ (prefixWord ++ tailWord_1286610).sum := by decide
  have hdescent : baseEnd_1286610 < baseStart_1286610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286627 : List Nat := [1, 1, 1, 6, 4, 1, 1, 6]
def baseStart_1286627 : Nat := 118140960795 + 1286627 * 2 ^ 59
def prefixEnd_1286627 : Nat := 4983230072969 + 3 ^ 40 * 1286627 * 2
def baseEnd_1286627 : Nat := 97875270229991525873395

theorem tailTrace_1286627 : CollatzResearch.WordTrace tailWord_1286627 prefixEnd_1286627 97875270229991525873395 := by
  unfold tailWord_1286627
  simp only [CollatzResearch.WordTrace]
  refine ⟨46927141909777592242442135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31284761273185061494961423 46927141909777592242442135)
  ·
    refine ⟨70390712864666388363663203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46927141909777592242442135 70390712864666388363663203)
    ·
      refine ⟨105586069296999582545494805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70390712864666388363663203 105586069296999582545494805)
      ·
        refine ⟨4949346998296855431820069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105586069296999582545494805 4949346998296855431820069)
        ·
          refine ⟨928002562180660393466263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4949346998296855431820069 928002562180660393466263)
          ·
            refine ⟨1392003843270990590199395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928002562180660393466263 1392003843270990590199395)
            ·
              refine ⟨2088005764906485885299093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392003843270990590199395 2088005764906485885299093)
              ·
                refine ⟨97875270229991525873395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2088005764906485885299093 97875270229991525873395)
                ·
                  rfl

theorem cell21_1286627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 6].length) (baseStart_1286627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286627 prefixEnd_1286627 := by exact prefixLift 1286627
  have htrace : WordTrace (prefixWord ++ tailWord_1286627) baseStart_1286627 baseEnd_1286627 := by
    simpa [prefixWord, tailWord_1286627, baseEnd_1286627] using wordTrace_append hprefix tailTrace_1286627
  have hstable : (prefixWord ++ tailWord_1286627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286627).length < 2 ^ (prefixWord ++ tailWord_1286627).sum := by decide
  have hdescent : baseEnd_1286627 < baseStart_1286627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286714 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_1286714 : Nat := 118140960795 + 1286714 * 2 ^ 59
def prefixEnd_1286714 : Nat := 4983230072969 + 3 ^ 40 * 1286714 * 2
def baseEnd_1286714 : Nat := 293645665275281759670007

theorem tailTrace_1286714 : CollatzResearch.WordTrace tailWord_1286714 prefixEnd_1286714 293645665275281759670007 := by
  unfold tailWord_1286714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732578765115601525214799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31286876706974937400572797 11732578765115601525214799)
  ·
    refine ⟨17598868147673402287822199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11732578765115601525214799 17598868147673402287822199)
    ·
      refine ⟨26398302221510103431733299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17598868147673402287822199 26398302221510103431733299)
      ·
        refine ⟨39597453332265155147599949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26398302221510103431733299 39597453332265155147599949)
        ·
          refine ⟨14849044999599433180349981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39597453332265155147599949 14849044999599433180349981)
          ·
            refine ⟨5568391874849787442631243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14849044999599433180349981 5568391874849787442631243)
            ·
              refine ⟨8352587812274681163946865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568391874849787442631243 8352587812274681163946865)
              ·
                refine ⟨6264440859206010872960149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8352587812274681163946865 6264440859206010872960149)
                ·
                  refine ⟨293645665275281759670007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6264440859206010872960149 293645665275281759670007)
                  ·
                    rfl

theorem cell21_1286714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_1286714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286714 prefixEnd_1286714 := by exact prefixLift 1286714
  have htrace : WordTrace (prefixWord ++ tailWord_1286714) baseStart_1286714 baseEnd_1286714 := by
    simpa [prefixWord, tailWord_1286714, baseEnd_1286714] using wordTrace_append hprefix tailTrace_1286714
  have hstable : (prefixWord ++ tailWord_1286714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286714).length < 2 ^ (prefixWord ++ tailWord_1286714).sum := by decide
  have hdescent : baseEnd_1286714 < baseStart_1286714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286748 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1286748 : Nat := 118140960795 + 1286748 * 2 ^ 59
def prefixEnd_1286748 : Nat := 4983230072969 + 3 ^ 40 * 1286748 * 2
def baseEnd_1286748 : Nat := 293653424538505256103271

theorem tailTrace_1286748 : CollatzResearch.WordTrace tailWord_1286748 prefixEnd_1286748 293653424538505256103271 := by
  unfold tailWord_1286748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23465777571169614953798449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31287703428226153271731265 23465777571169614953798449)
  ·
    refine ⟨17599333178377211215348837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23465777571169614953798449 17599333178377211215348837)
    ·
      refine ⟨3299874970945727102877907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17599333178377211215348837 3299874970945727102877907)
      ·
        refine ⟨4949812456418590654316861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299874970945727102877907 4949812456418590654316861)
        ·
          refine ⟨1856179671156971495368823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4949812456418590654316861 1856179671156971495368823)
          ·
            refine ⟨2784269506735457243053235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856179671156971495368823 2784269506735457243053235)
            ·
              refine ⟨4176404260103185864579853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784269506735457243053235 4176404260103185864579853)
              ·
                refine ⟨1566151597538694699217445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176404260103185864579853 1566151597538694699217445)
                ·
                  refine ⟨293653424538505256103271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566151597538694699217445 293653424538505256103271)
                  ·
                    rfl

theorem cell21_1286748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1286748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286748 prefixEnd_1286748 := by exact prefixLift 1286748
  have htrace : WordTrace (prefixWord ++ tailWord_1286748) baseStart_1286748 baseEnd_1286748 := by
    simpa [prefixWord, tailWord_1286748, baseEnd_1286748] using wordTrace_append hprefix tailTrace_1286748
  have hstable : (prefixWord ++ tailWord_1286748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286748).length < 2 ^ (prefixWord ++ tailWord_1286748).sum := by decide
  have hdescent : baseEnd_1286748 < baseStart_1286748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286759 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_1286759 : Nat := 118140960795 + 1286759 * 2 ^ 59
def prefixEnd_1286759 : Nat := 4983230072969 + 3 ^ 40 * 1286759 * 2
def baseEnd_1286759 : Nat := 293655934888371681419915

theorem tailTrace_1286759 : CollatzResearch.WordTrace tailWord_1286759 prefixEnd_1286759 293655934888371681419915 := by
  unfold tailWord_1286759
  simp only [CollatzResearch.WordTrace]
  refine ⟨46931956345299378786247331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31287970896866252524164887 46931956345299378786247331)
  ·
    refine ⟨70397934517949068179370997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46931956345299378786247331 70397934517949068179370997)
    ·
      refine ⟨6599806361057725141816031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70397934517949068179370997 6599806361057725141816031)
      ·
        refine ⟨9899709541586587712724047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599806361057725141816031 9899709541586587712724047)
        ·
          refine ⟨14849564312379881569086071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899709541586587712724047 14849564312379881569086071)
          ·
            refine ⟨22274346468569822353629107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14849564312379881569086071 22274346468569822353629107)
            ·
              refine ⟨33411519702854733530443661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22274346468569822353629107 33411519702854733530443661)
              ·
                refine ⟨12529319888570525073916373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33411519702854733530443661 12529319888570525073916373)
                ·
                  refine ⟨293655934888371681419915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12529319888570525073916373 293655934888371681419915)
                  ·
                    rfl

theorem cell21_1286759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_1286759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286759 prefixEnd_1286759 := by exact prefixLift 1286759
  have htrace : WordTrace (prefixWord ++ tailWord_1286759) baseStart_1286759 baseEnd_1286759 := by
    simpa [prefixWord, tailWord_1286759, baseEnd_1286759] using wordTrace_append hprefix tailTrace_1286759
  have hstable : (prefixWord ++ tailWord_1286759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286759).length < 2 ^ (prefixWord ++ tailWord_1286759).sum := by decide
  have hdescent : baseEnd_1286759 < baseStart_1286759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286852 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1286852 : Nat := 118140960795 + 1286852 * 2 ^ 59
def prefixEnd_1286852 : Nat := 4983230072969 + 3 ^ 40 * 1286852 * 2
def baseEnd_1286852 : Nat := 293677158755424186369725

theorem tailTrace_1286852 : CollatzResearch.WordTrace tailWord_1286852 prefixEnd_1286852 293677158755424186369725 := by
  unfold tailWord_1286852
  simp only [CollatzResearch.WordTrace]
  refine ⟨23467674166981227834691405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31290232222641637112921873 23467674166981227834691405)
  ·
    refine ⟨8800377812617960438009277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23467674166981227834691405 8800377812617960438009277)
    ·
      refine ⟨3300141679731735164253479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8800377812617960438009277 3300141679731735164253479)
      ·
        refine ⟨4950212519597602746380219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300141679731735164253479 4950212519597602746380219)
        ·
          refine ⟨7425318779396404119570329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950212519597602746380219 7425318779396404119570329)
          ·
            refine ⟨5568989084547303089677747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7425318779396404119570329 5568989084547303089677747)
            ·
              refine ⟨8353483626820954634516621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568989084547303089677747 8353483626820954634516621)
              ·
                refine ⟨3132556360057857987943733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8353483626820954634516621 3132556360057857987943733)
                ·
                  refine ⟨293677158755424186369725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132556360057857987943733 293677158755424186369725)
                  ·
                    rfl

theorem cell21_1286852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1286852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286852 prefixEnd_1286852 := by exact prefixLift 1286852
  have htrace : WordTrace (prefixWord ++ tailWord_1286852) baseStart_1286852 baseEnd_1286852 := by
    simpa [prefixWord, tailWord_1286852, baseEnd_1286852] using wordTrace_append hprefix tailTrace_1286852
  have hstable : (prefixWord ++ tailWord_1286852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286852).length < 2 ^ (prefixWord ++ tailWord_1286852).sum := by decide
  have hdescent : baseEnd_1286852 < baseStart_1286852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286914 : List Nat := [3, 4, 1, 1, 1, 3, 2, 6]
def baseStart_1286914 : Nat := 118140960795 + 1286914 * 2 ^ 59
def prefixEnd_1286914 : Nat := 4983230072969 + 3 ^ 40 * 1286914 * 2
def baseEnd_1286914 : Nat := 97897102666708618778755

theorem tailTrace_1286914 : CollatzResearch.WordTrace tailWord_1286914 prefixEnd_1286914 97897102666708618778755 := by
  unfold tailWord_1286914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11734402414934460064534949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31291739773158560172093197 11734402414934460064534949)
  ·
    refine ⟨2200200452800211262100303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11734402414934460064534949 2200200452800211262100303)
    ·
      refine ⟨3300300679200316893150455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200200452800211262100303 3300300679200316893150455)
      ·
        refine ⟨4950451018800475339725683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300300679200316893150455 4950451018800475339725683)
        ·
          refine ⟨7425676528200713009588525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950451018800475339725683 7425676528200713009588525)
          ·
            refine ⟨2784628698075267378595697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7425676528200713009588525 2784628698075267378595697)
            ·
              refine ⟨2088471523556450533946773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784628698075267378595697 2088471523556450533946773)
              ·
                refine ⟨97897102666708618778755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2088471523556450533946773 97897102666708618778755)
                ·
                  rfl

theorem cell21_1286914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_1286914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1286914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1286914 prefixEnd_1286914 := by exact prefixLift 1286914
  have htrace : WordTrace (prefixWord ++ tailWord_1286914) baseStart_1286914 baseEnd_1286914 := by
    simpa [prefixWord, tailWord_1286914, baseEnd_1286914] using wordTrace_append hprefix tailTrace_1286914
  have hstable : (prefixWord ++ tailWord_1286914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286914).length < 2 ^ (prefixWord ++ tailWord_1286914).sum := by decide
  have hdescent : baseEnd_1286914 < baseStart_1286914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287049 : List Nat := [1, 2, 1, 1, 5, 2, 4, 5]
def baseStart_1287049 : Nat := 118140960795 + 1287049 * 2 ^ 59
def prefixEnd_1287049 : Nat := 4983230072969 + 3 ^ 40 * 1287049 * 2
def baseEnd_1287049 : Nat := 97907372279798540528663

theorem tailTrace_1287049 : CollatzResearch.WordTrace tailWord_1287049 prefixEnd_1287049 97907372279798540528663 := by
  unfold tailWord_1287049
  simp only [CollatzResearch.WordTrace]
  refine ⟨46942533514248758314304201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31295022342832505542869467 46942533514248758314304201)
  ·
    refine ⟨35206900135686568735728151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46942533514248758314304201 35206900135686568735728151)
    ·
      refine ⟨52810350203529853103592227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35206900135686568735728151 52810350203529853103592227)
      ·
        refine ⟨79215525305294779655388341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52810350203529853103592227 79215525305294779655388341)
        ·
          refine ⟨7426455497371385592692657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79215525305294779655388341 7426455497371385592692657)
          ·
            refine ⟨5569841623028539194519493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7426455497371385592692657 5569841623028539194519493)
            ·
              refine ⟨1044345304317851098972405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5569841623028539194519493 1044345304317851098972405)
              ·
                refine ⟨97907372279798540528663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044345304317851098972405 97907372279798540528663)
                ·
                  rfl

theorem cell21_1287049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 5].length) (baseStart_1287049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287049 prefixEnd_1287049 := by exact prefixLift 1287049
  have htrace : WordTrace (prefixWord ++ tailWord_1287049) baseStart_1287049 baseEnd_1287049 := by
    simpa [prefixWord, tailWord_1287049, baseEnd_1287049] using wordTrace_append hprefix tailTrace_1287049
  have hstable : (prefixWord ++ tailWord_1287049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287049).length < 2 ^ (prefixWord ++ tailWord_1287049).sum := by decide
  have hdescent : baseEnd_1287049 < baseStart_1287049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287066 : List Nat := [3, 1, 1, 4, 4, 1, 7]
def baseStart_1287066 : Nat := 118140960795 + 1287066 * 2 ^ 59
def prefixEnd_1287066 : Nat := 4983230072969 + 3 ^ 40 * 1287066 * 2
def baseEnd_1287066 : Nat := 32636221830111929978069

theorem tailTrace_1287066 : CollatzResearch.WordTrace tailWord_1287066 prefixEnd_1287066 32636221830111929978069 := by
  unfold tailWord_1287066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735788388796792554418263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31295435703458113478448701 11735788388796792554418263)
  ·
    refine ⟨17603682583195188831627395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11735788388796792554418263 17603682583195188831627395)
    ·
      refine ⟨26405523874792783247441093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17603682583195188831627395 26405523874792783247441093)
      ·
        refine ⟨4951035726523646858895205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26405523874792783247441093 4951035726523646858895205)
        ·
          refine ⟨928319198723183786042851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4951035726523646858895205 928319198723183786042851)
          ·
            refine ⟨1392478798084775679064277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928319198723183786042851 1392478798084775679064277)
            ·
              refine ⟨32636221830111929978069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1392478798084775679064277 32636221830111929978069)
              ·
                rfl

theorem cell21_1287066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 7].length) (baseStart_1287066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287066 prefixEnd_1287066 := by exact prefixLift 1287066
  have htrace : WordTrace (prefixWord ++ tailWord_1287066) baseStart_1287066 baseEnd_1287066 := by
    simpa [prefixWord, tailWord_1287066, baseEnd_1287066] using wordTrace_append hprefix tailTrace_1287066
  have hstable : (prefixWord ++ tailWord_1287066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287066).length < 2 ^ (prefixWord ++ tailWord_1287066).sum := by decide
  have hdescent : baseEnd_1287066 < baseStart_1287066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287125 : List Nat := [1, 3, 2, 3, 4, 8]
def baseStart_1287125 : Nat := 118140960795 + 1287125 * 2 ^ 59
def prefixEnd_1287125 : Nat := 4983230072969 + 3 ^ 40 * 1287125 * 2
def baseEnd_1287125 : Nat := 10879239299068014011821

theorem tailTrace_1287125 : CollatzResearch.WordTrace tailWord_1287125 prefixEnd_1287125 10879239299068014011821 := by
  unfold tailWord_1287125
  simp only [CollatzResearch.WordTrace]
  refine ⟨46945305461973423294070829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31296870307982282196047219 46945305461973423294070829)
  ·
    refine ⟨17604489548240033735276561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46945305461973423294070829 17604489548240033735276561)
    ·
      refine ⟨13203367161180025301457421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17604489548240033735276561 13203367161180025301457421)
      ·
        refine ⟨4951262685442509488046533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13203367161180025301457421 4951262685442509488046533)
        ·
          refine ⟨928361753520470529008725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4951262685442509488046533 928361753520470529008725)
          ·
            refine ⟨10879239299068014011821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 928361753520470529008725 10879239299068014011821)
            ·
              rfl

theorem cell21_1287125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 8].length) (baseStart_1287125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287125 prefixEnd_1287125 := by exact prefixLift 1287125
  have htrace : WordTrace (prefixWord ++ tailWord_1287125) baseStart_1287125 baseEnd_1287125 := by
    simpa [prefixWord, tailWord_1287125, baseEnd_1287125] using wordTrace_append hprefix tailTrace_1287125
  have hstable : (prefixWord ++ tailWord_1287125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287125).length < 2 ^ (prefixWord ++ tailWord_1287125).sum := by decide
  have hdescent : baseEnd_1287125 < baseStart_1287125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287139 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_1287139 : Nat := 118140960795 + 1287139 * 2 ^ 59
def prefixEnd_1287139 : Nat := 4983230072969 + 3 ^ 40 * 1287139 * 2
def baseEnd_1287139 : Nat := 293742656065575465085805

theorem tailTrace_1287139 : CollatzResearch.WordTrace tailWord_1287139 prefixEnd_1287139 293742656065575465085805 := by
  unfold tailWord_1287139
  simp only [CollatzResearch.WordTrace]
  refine ⟨46945816083922703685080471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31297210722615135790053647 46945816083922703685080471)
  ·
    refine ⟨70418724125884055527620707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46945816083922703685080471 70418724125884055527620707)
    ·
      refine ⟨105628086188826083291431061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70418724125884055527620707 105628086188826083291431061)
      ·
        refine ⟨4951316540101222654285831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105628086188826083291431061 4951316540101222654285831)
        ·
          refine ⟨7426974810151833981428747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951316540101222654285831 7426974810151833981428747)
          ·
            refine ⟨11140462215227750972143121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426974810151833981428747 11140462215227750972143121)
            ·
              refine ⟨8355346661420813229107341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11140462215227750972143121 8355346661420813229107341)
              ·
                refine ⟨3133254998032804960915253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8355346661420813229107341 3133254998032804960915253)
                ·
                  refine ⟨293742656065575465085805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3133254998032804960915253 293742656065575465085805)
                  ·
                    rfl

theorem cell21_1287139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_1287139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287139 prefixEnd_1287139 := by exact prefixLift 1287139
  have htrace : WordTrace (prefixWord ++ tailWord_1287139) baseStart_1287139 baseEnd_1287139 := by
    simpa [prefixWord, tailWord_1287139, baseEnd_1287139] using wordTrace_append hprefix tailTrace_1287139
  have hstable : (prefixWord ++ tailWord_1287139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287139).length < 2 ^ (prefixWord ++ tailWord_1287139).sum := by decide
  have hdescent : baseEnd_1287139 < baseStart_1287139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287204 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1287204 : Nat := 118140960795 + 1287204 * 2 ^ 59
def prefixEnd_1287204 : Nat := 4983230072969 + 3 ^ 40 * 1287204 * 2
def baseEnd_1287204 : Nat := 293757489951149796502339

theorem tailTrace_1287204 : CollatzResearch.WordTrace tailWord_1287204 prefixEnd_1287204 293757489951149796502339 := by
  unfold tailWord_1287204
  simp only [CollatzResearch.WordTrace]
  refine ⟨23474093414343609893098333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31298791219124813190797777 23474093414343609893098333)
  ·
    refine ⟨8802785030378853709911875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23474093414343609893098333 8802785030378853709911875)
    ·
      refine ⟨13204177545568280564867813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8802785030378853709911875 13204177545568280564867813)
      ·
        refine ⟨2475783289794052605912715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13204177545568280564867813 2475783289794052605912715)
        ·
          refine ⟨3713674934691078908869073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475783289794052605912715 3713674934691078908869073)
          ·
            refine ⟨2785256201018309181651805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713674934691078908869073 2785256201018309181651805)
            ·
              refine ⟨1044471075381865943119427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2785256201018309181651805 1044471075381865943119427)
              ·
                refine ⟨1566706613072798914679141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044471075381865943119427 1566706613072798914679141)
                ·
                  refine ⟨293757489951149796502339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566706613072798914679141 293757489951149796502339)
                  ·
                    rfl

theorem cell21_1287204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1287204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287204 prefixEnd_1287204 := by exact prefixLift 1287204
  have htrace : WordTrace (prefixWord ++ tailWord_1287204) baseStart_1287204 baseEnd_1287204 := by
    simpa [prefixWord, tailWord_1287204, baseEnd_1287204] using wordTrace_append hprefix tailTrace_1287204
  have hstable : (prefixWord ++ tailWord_1287204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287204).length < 2 ^ (prefixWord ++ tailWord_1287204).sum := by decide
  have hdescent : baseEnd_1287204 < baseStart_1287204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287246 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1287246 : Nat := 118140960795 + 1287246 * 2 ^ 59
def prefixEnd_1287246 : Nat := 4983230072969 + 3 ^ 40 * 1287246 * 2
def baseEnd_1287246 : Nat := 293767074923367056802253

theorem tailTrace_1287246 : CollatzResearch.WordTrace tailWord_1287246 prefixEnd_1287246 293767074923367056802253 := by
  unfold tailWord_1287246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868714836816882619903199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31299812463023373972817061 5868714836816882619903199)
  ·
    refine ⟨8803072255225323929854799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5868714836816882619903199 8803072255225323929854799)
    ·
      refine ⟨13204608382837985894782199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803072255225323929854799 13204608382837985894782199)
      ·
        refine ⟨19806912574256978842173299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13204608382837985894782199 19806912574256978842173299)
        ·
          refine ⟨29710368861385468263259949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19806912574256978842173299 29710368861385468263259949)
          ·
            refine ⟨11141388323019550598722481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29710368861385468263259949 11141388323019550598722481)
            ·
              refine ⟨8356041242264662949041861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141388323019550598722481 8356041242264662949041861)
              ·
                refine ⟨1566757732924624302945349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8356041242264662949041861 1566757732924624302945349)
                ·
                  refine ⟨293767074923367056802253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566757732924624302945349 293767074923367056802253)
                  ·
                    rfl

theorem cell21_1287246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1287246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287246 prefixEnd_1287246 := by exact prefixLift 1287246
  have htrace : WordTrace (prefixWord ++ tailWord_1287246) baseStart_1287246 baseEnd_1287246 := by
    simpa [prefixWord, tailWord_1287246, baseEnd_1287246] using wordTrace_append hprefix tailTrace_1287246
  have hstable : (prefixWord ++ tailWord_1287246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287246).length < 2 ^ (prefixWord ++ tailWord_1287246).sum := by decide
  have hdescent : baseEnd_1287246 < baseStart_1287246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287294 : List Nat := [4, 2, 4, 1, 10]
def baseStart_1287294 : Nat := 118140960795 + 1287294 * 2 ^ 59
def prefixEnd_1287294 : Nat := 4983230072969 + 3 ^ 40 * 1287294 * 2
def baseEnd_1287294 : Nat := 3626889249102835061755

theorem tailTrace_1287294 : CollatzResearch.WordTrace tailWord_1287294 prefixEnd_1287294 3626889249102835061755 := by
  unfold tailWord_1287294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868933674795145644621617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31300979598907443437981957 5868933674795145644621617)
  ·
    refine ⟨4401700256096359233466213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5868933674795145644621617 4401700256096359233466213)
    ·
      refine ⟨825318798018067356274915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4401700256096359233466213 825318798018067356274915)
      ·
        refine ⟨1237978197027101034412373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825318798018067356274915 1237978197027101034412373)
        ·
          refine ⟨3626889249102835061755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1237978197027101034412373 3626889249102835061755)
          ·
            rfl

theorem cell21_1287294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 10].length) (baseStart_1287294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287294 prefixEnd_1287294 := by exact prefixLift 1287294
  have htrace : WordTrace (prefixWord ++ tailWord_1287294) baseStart_1287294 baseEnd_1287294 := by
    simpa [prefixWord, tailWord_1287294, baseEnd_1287294] using wordTrace_append hprefix tailTrace_1287294
  have hstable : (prefixWord ++ tailWord_1287294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287294).length < 2 ^ (prefixWord ++ tailWord_1287294).sum := by decide
  have hdescent : baseEnd_1287294 < baseStart_1287294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287432 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_1287432 : Nat := 118140960795 + 1287432 * 2 ^ 59
def prefixEnd_1287432 : Nat := 4983230072969 + 3 ^ 40 * 1287432 * 2
def baseEnd_1287432 : Nat := 293809522657472066701873

theorem tailTrace_1287432 : CollatzResearch.WordTrace tailWord_1287432 prefixEnd_1287432 293809522657472066701873 := by
  unfold tailWord_1287432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478251335930607362748275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31304335114574143150331033 23478251335930607362748275)
  ·
    refine ⟨35217377003895911044122413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23478251335930607362748275 35217377003895911044122413)
    ·
      refine ⟨13206516376460966641545905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35217377003895911044122413 13206516376460966641545905)
      ·
        refine ⟨9904887282345724981159429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13206516376460966641545905 9904887282345724981159429)
        ·
          refine ⟨1857166365439823433967393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9904887282345724981159429 1857166365439823433967393)
          ·
            refine ⟨1392874774079867575475545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857166365439823433967393 1392874774079867575475545)
            ·
              refine ⟨1044656080559900681606659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392874774079867575475545 1044656080559900681606659)
              ·
                refine ⟨1566984120839851022409989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044656080559900681606659 1566984120839851022409989)
                ·
                  refine ⟨293809522657472066701873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566984120839851022409989 293809522657472066701873)
                  ·
                    rfl

theorem cell21_1287432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_1287432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287432 prefixEnd_1287432 := by exact prefixLift 1287432
  have htrace : WordTrace (prefixWord ++ tailWord_1287432) baseStart_1287432 baseEnd_1287432 := by
    simpa [prefixWord, tailWord_1287432, baseEnd_1287432] using wordTrace_append hprefix tailTrace_1287432
  have hstable : (prefixWord ++ tailWord_1287432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287432).length < 2 ^ (prefixWord ++ tailWord_1287432).sum := by decide
  have hdescent : baseEnd_1287432 < baseStart_1287432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287460 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1287460 : Nat := 118140960795 + 1287460 * 2 ^ 59
def prefixEnd_1287460 : Nat := 4983230072969 + 3 ^ 40 * 1287460 * 2
def baseEnd_1287460 : Nat := 293815912638950240235149

theorem tailTrace_1287460 : CollatzResearch.WordTrace tailWord_1287460 prefixEnd_1287460 293815912638950240235149 := by
  unfold tailWord_1287460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478761957879887753757917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31305015943839850338343889 23478761957879887753757917)
  ·
    refine ⟨8804535734204957907659219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23478761957879887753757917 8804535734204957907659219)
    ·
      refine ⟨13206803601307436861488829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804535734204957907659219 13206803601307436861488829)
      ·
        refine ⟨4952551350490288823058311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13206803601307436861488829 4952551350490288823058311)
        ·
          refine ⟨7428827025735433234587467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952551350490288823058311 7428827025735433234587467)
          ·
            refine ⟨11143240538603149851881201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428827025735433234587467 11143240538603149851881201)
            ·
              refine ⟨8357430403952362388910901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11143240538603149851881201 8357430403952362388910901)
              ·
                refine ⟨783509100370533973960397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8357430403952362388910901 783509100370533973960397)
                ·
                  refine ⟨293815912638950240235149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783509100370533973960397 293815912638950240235149)
                  ·
                    rfl

theorem cell21_1287460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1287460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287460 prefixEnd_1287460 := by exact prefixLift 1287460
  have htrace : WordTrace (prefixWord ++ tailWord_1287460) baseStart_1287460 baseEnd_1287460 := by
    simpa [prefixWord, tailWord_1287460, baseEnd_1287460] using wordTrace_append hprefix tailTrace_1287460
  have hstable : (prefixWord ++ tailWord_1287460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287460).length < 2 ^ (prefixWord ++ tailWord_1287460).sum := by decide
  have hdescent : baseEnd_1287460 < baseStart_1287460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287474 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1287474 : Nat := 118140960795 + 1287474 * 2 ^ 59
def prefixEnd_1287474 : Nat := 4983230072969 + 3 ^ 40 * 1287474 * 2
def baseEnd_1287474 : Nat := 293819107629689327001787

theorem tailTrace_1287474 : CollatzResearch.WordTrace tailWord_1287474 prefixEnd_1287474 293819107629689327001787 := by
  unfold tailWord_1287474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739508634427263974631369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31305356358472703932350317 11739508634427263974631369)
  ·
    refine ⟨8804631475820447980973527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11739508634427263974631369 8804631475820447980973527)
    ·
      refine ⟨13206947213730671971460291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804631475820447980973527 13206947213730671971460291)
      ·
        refine ⟨19810420820596007957190437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206947213730671971460291 19810420820596007957190437)
        ·
          refine ⟨3714453903861751491973207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19810420820596007957190437 3714453903861751491973207)
          ·
            refine ⟨5571680855792627237959811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714453903861751491973207 5571680855792627237959811)
            ·
              refine ⟨8357521283688940856939717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571680855792627237959811 8357521283688940856939717)
              ·
                refine ⟨1567035240691676410676197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8357521283688940856939717 1567035240691676410676197)
                ·
                  refine ⟨293819107629689327001787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1567035240691676410676197 293819107629689327001787)
                  ·
                    rfl

theorem cell21_1287474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1287474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287474 prefixEnd_1287474 := by exact prefixLift 1287474
  have htrace : WordTrace (prefixWord ++ tailWord_1287474) baseStart_1287474 baseEnd_1287474 := by
    simpa [prefixWord, tailWord_1287474, baseEnd_1287474] using wordTrace_append hprefix tailTrace_1287474
  have hstable : (prefixWord ++ tailWord_1287474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287474).length < 2 ^ (prefixWord ++ tailWord_1287474).sum := by decide
  have hdescent : baseEnd_1287474 < baseStart_1287474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
