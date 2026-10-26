import V185TrunkScan20Chunk083

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_511077 : List Nat := [1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_511077 : Nat := 118140960795 + 511077 * 2 ^ 59
def prefixEnd_511077 : Nat := 4983230072969 + 3 ^ 40 * 511077 * 2
def baseEnd_511077 : Nat := 77756489617185820025809

theorem tailTrace_511077 : CollatzResearch.WordTrace tailWord_511077 prefixEnd_511077 77756489617185820025809 := by
  unfold tailWord_511077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640509569462788847595485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12427006379641859231730323 18640509569462788847595485)
  ·
    refine ⟨6990191088548545817848307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18640509569462788847595485 6990191088548545817848307)
    ·
      refine ⟨10485286632822818726772461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990191088548545817848307 10485286632822818726772461)
      ·
        refine ⟨3931982487308557022539673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10485286632822818726772461 3931982487308557022539673)
        ·
          refine ⟨2948986865481417766904755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931982487308557022539673 2948986865481417766904755)
          ·
            refine ⟨4423480298222126650357133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948986865481417766904755 4423480298222126650357133)
            ·
              refine ⟨1658805111833297493883925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4423480298222126650357133 1658805111833297493883925)
              ·
                refine ⟨77756489617185820025809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1658805111833297493883925 77756489617185820025809)
                ·
                  rfl

theorem cell20_511077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_511077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511077 prefixEnd_511077 := by exact prefixLift 511077
  have htrace : WordTrace (prefixWord ++ tailWord_511077) baseStart_511077 baseEnd_511077 := by
    simpa [prefixWord, tailWord_511077, baseEnd_511077] using wordTrace_append hprefix tailTrace_511077
  have hstable : (prefixWord ++ tailWord_511077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511077).length < 2 ^ (prefixWord ++ tailWord_511077).sum := by decide
  have hdescent : baseEnd_511077 < baseStart_511077 := by decide
  rcases family_descends (prefixWord ++ tailWord_511077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511084 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_511084 : Nat := 118140960795 + 511084 * 2 ^ 59
def prefixEnd_511084 : Nat := 4983230072969 + 3 ^ 40 * 511084 * 2
def baseEnd_511084 : Nat := 233272663842296546844065

theorem tailTrace_511084 : CollatzResearch.WordTrace tailWord_511084 prefixEnd_511084 233272663842296546844065 := by
  unfold tailWord_511084
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320382440218714521550153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12427176586958286028733537 9320382440218714521550153)
  ·
    refine ⟨6990286830164035891162615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9320382440218714521550153 6990286830164035891162615)
    ·
      refine ⟨10485430245246053836743923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990286830164035891162615 10485430245246053836743923)
      ·
        refine ⟨15728145367869080755115885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485430245246053836743923 15728145367869080755115885)
        ·
          refine ⟨5898054512950905283168457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15728145367869080755115885 5898054512950905283168457)
          ·
            refine ⟨4423540884713178962376343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898054512950905283168457 4423540884713178962376343)
            ·
              refine ⟨6635311327069768443564515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423540884713178962376343 6635311327069768443564515)
              ·
                refine ⟨9952966990604652665346773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635311327069768443564515 9952966990604652665346773)
                ·
                  refine ⟨233272663842296546844065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9952966990604652665346773 233272663842296546844065)
                  ·
                    rfl

theorem cell20_511084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_511084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511084 prefixEnd_511084 := by exact prefixLift 511084
  have htrace : WordTrace (prefixWord ++ tailWord_511084) baseStart_511084 baseEnd_511084 := by
    simpa [prefixWord, tailWord_511084, baseEnd_511084] using wordTrace_append hprefix tailTrace_511084
  have hstable : (prefixWord ++ tailWord_511084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511084).length < 2 ^ (prefixWord ++ tailWord_511084).sum := by decide
  have hdescent : baseEnd_511084 < baseStart_511084 := by decide
  rcases family_descends (prefixWord ++ tailWord_511084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511101 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_511101 : Nat := 118140960795 + 511101 * 2 ^ 59
def prefixEnd_511101 : Nat := 4983230072969 + 3 ^ 40 * 511101 * 2
def baseEnd_511101 : Nat := 233280423105520043277329

theorem tailTrace_511101 : CollatzResearch.WordTrace tailWord_511101 prefixEnd_511101 233280423105520043277329 := by
  unfold tailWord_511101
  simp only [CollatzResearch.WordTrace]
  refine ⟨18641384921375840946469157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12427589947583893964312771 18641384921375840946469157)
  ·
    refine ⟨3495259672757970177462967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18641384921375840946469157 3495259672757970177462967)
    ·
      refine ⟨5242889509136955266194451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495259672757970177462967 5242889509136955266194451)
      ·
        refine ⟨7864334263705432899291677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242889509136955266194451 7864334263705432899291677)
        ·
          refine ⟨2949125348889537337234379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7864334263705432899291677 2949125348889537337234379)
          ·
            refine ⟨4423688023334306005851569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949125348889537337234379 4423688023334306005851569)
            ·
              refine ⟨3317766017500729504388677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423688023334306005851569 3317766017500729504388677)
              ·
                refine ⟨622081128281386782072877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3317766017500729504388677 622081128281386782072877)
                ·
                  refine ⟨233280423105520043277329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622081128281386782072877 233280423105520043277329)
                  ·
                    rfl

theorem cell20_511101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_511101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511101 prefixEnd_511101 := by exact prefixLift 511101
  have htrace : WordTrace (prefixWord ++ tailWord_511101) baseStart_511101 baseEnd_511101 := by
    simpa [prefixWord, tailWord_511101, baseEnd_511101] using wordTrace_append hprefix tailTrace_511101
  have hstable : (prefixWord ++ tailWord_511101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511101).length < 2 ^ (prefixWord ++ tailWord_511101).sum := by decide
  have hdescent : baseEnd_511101 < baseStart_511101 := by decide
  rcases family_descends (prefixWord ++ tailWord_511101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511118 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_511118 : Nat := 118140960795 + 511118 * 2 ^ 59
def prefixEnd_511118 : Nat := 4983230072969 + 3 ^ 40 * 511118 * 2
def baseEnd_511118 : Nat := 233288182368743539710593

theorem tailTrace_511118 : CollatzResearch.WordTrace tailWord_511118 prefixEnd_511118 233288182368743539710593 := by
  unfold tailWord_511118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330250620289281606229751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12428003308209501899892005 2330250620289281606229751)
  ·
    refine ⟨3495375930433922409344627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330250620289281606229751 3495375930433922409344627)
    ·
      refine ⟨5243063895650883614016941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495375930433922409344627 5243063895650883614016941)
      ·
        refine ⟨1966148960869081355256353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5243063895650883614016941 1966148960869081355256353)
        ·
          refine ⟨1474611720651811016442265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966148960869081355256353 1474611720651811016442265)
          ·
            refine ⟨1105958790488858262331699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474611720651811016442265 1105958790488858262331699)
            ·
              refine ⟨1658938185733287393497549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105958790488858262331699 1658938185733287393497549)
              ·
                refine ⟨622101819649982772561581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1658938185733287393497549 622101819649982772561581)
                ·
                  refine ⟨233288182368743539710593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622101819649982772561581 233288182368743539710593)
                  ·
                    rfl

theorem cell20_511118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_511118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511118 prefixEnd_511118 := by exact prefixLift 511118
  have htrace : WordTrace (prefixWord ++ tailWord_511118) baseStart_511118 baseEnd_511118 := by
    simpa [prefixWord, tailWord_511118, baseEnd_511118] using wordTrace_append hprefix tailTrace_511118
  have hstable : (prefixWord ++ tailWord_511118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511118).length < 2 ^ (prefixWord ++ tailWord_511118).sum := by decide
  have hdescent : baseEnd_511118 < baseStart_511118 := by decide
  rcases family_descends (prefixWord ++ tailWord_511118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511153 : List Nat := [1, 2, 2, 5, 1, 9]
def baseStart_511153 : Nat := 118140960795 + 511153 * 2 ^ 59
def prefixEnd_511153 : Nat := 4983230072969 + 3 ^ 40 * 511153 * 2
def baseEnd_511153 : Nat := 8640894715645887909029

theorem tailTrace_511153 : CollatzResearch.WordTrace tailWord_511153 prefixEnd_511153 8640894715645887909029 := by
  unfold tailWord_511153
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643281517187453827362113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12428854344791635884908075 18643281517187453827362113)
  ·
    refine ⟨13982461137890590370521585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18643281517187453827362113 13982461137890590370521585)
    ·
      refine ⟨10486845853417942777891189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13982461137890590370521585 10486845853417942777891189)
      ·
        refine ⟨983141798757932135427299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10486845853417942777891189 983141798757932135427299)
        ·
          refine ⟨1474712698136898203140949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983141798757932135427299 1474712698136898203140949)
          ·
            refine ⟨8640894715645887909029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1474712698136898203140949 8640894715645887909029)
            ·
              rfl

theorem cell20_511153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 9].length) (baseStart_511153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511153 prefixEnd_511153 := by exact prefixLift 511153
  have htrace : WordTrace (prefixWord ++ tailWord_511153) baseStart_511153 baseEnd_511153 := by
    simpa [prefixWord, tailWord_511153, baseEnd_511153] using wordTrace_append hprefix tailTrace_511153
  have hstable : (prefixWord ++ tailWord_511153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511153).length < 2 ^ (prefixWord ++ tailWord_511153).sum := by decide
  have hdescent : baseEnd_511153 < baseStart_511153 := by decide
  rcases family_descends (prefixWord ++ tailWord_511153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511197 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 2]
def baseStart_511197 : Nat := 118140960795 + 511197 * 2 ^ 59
def prefixEnd_511197 : Nat := 4983230072969 + 3 ^ 40 * 511197 * 2
def baseEnd_511197 : Nat := 233324240121370376076937

theorem tailTrace_511197 : CollatzResearch.WordTrace tailWord_511197 prefixEnd_511197 233324240121370376076937 := by
  unfold tailWord_511197
  simp only [CollatzResearch.WordTrace]
  refine ⟨18644886329028049341963845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12429924219352032894642563 18644886329028049341963845)
  ·
    refine ⟨3495916186692759251618221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18644886329028049341963845 3495916186692759251618221)
    ·
      refine ⟨1310968570009784719356833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3495916186692759251618221 1310968570009784719356833)
      ·
        refine ⟨983226427507338539517625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310968570009784719356833 983226427507338539517625)
        ·
          refine ⟨737419820630503904638219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983226427507338539517625 737419820630503904638219)
          ·
            refine ⟨1106129730945755856957329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737419820630503904638219 1106129730945755856957329)
            ·
              refine ⟨829597298209316892717997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106129730945755856957329 829597298209316892717997)
              ·
                refine ⟨311098986828493834769249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829597298209316892717997 311098986828493834769249)
                ·
                  refine ⟨233324240121370376076937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311098986828493834769249 233324240121370376076937)
                  ·
                    rfl

theorem cell20_511197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_511197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511197 prefixEnd_511197 := by exact prefixLift 511197
  have htrace : WordTrace (prefixWord ++ tailWord_511197) baseStart_511197 baseEnd_511197 := by
    simpa [prefixWord, tailWord_511197, baseEnd_511197] using wordTrace_append hprefix tailTrace_511197
  have hstable : (prefixWord ++ tailWord_511197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511197).length < 2 ^ (prefixWord ++ tailWord_511197).sum := by decide
  have hdescent : baseEnd_511197 < baseStart_511197 := by decide
  rcases family_descends (prefixWord ++ tailWord_511197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511201 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 2]
def baseStart_511201 : Nat := 118140960795 + 511201 * 2 ^ 59
def prefixEnd_511201 : Nat := 4983230072969 + 3 ^ 40 * 511201 * 2
def baseEnd_511201 : Nat := 233326065830364139943587

theorem tailTrace_511201 : CollatzResearch.WordTrace tailWord_511201 prefixEnd_511201 233326065830364139943587 := by
  unfold tailWord_511201
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645032221013558025109457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12430021480675705350072971 18645032221013558025109457)
  ·
    refine ⟨13983774165760168518832093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18645032221013558025109457 13983774165760168518832093)
    ·
      refine ⟨5243915312160063194562035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13983774165760168518832093 5243915312160063194562035)
      ·
        refine ⟨7865872968240094791843053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243915312160063194562035 7865872968240094791843053)
        ·
          refine ⟨2949702363090035546941145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7865872968240094791843053 2949702363090035546941145)
          ·
            refine ⟨2212276772317526660205859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949702363090035546941145 2212276772317526660205859)
            ·
              refine ⟨3318415158476289990308789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212276772317526660205859 3318415158476289990308789)
              ·
                refine ⟨311101421107152186591449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3318415158476289990308789 311101421107152186591449)
                ·
                  refine ⟨233326065830364139943587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311101421107152186591449 233326065830364139943587)
                  ·
                    rfl

theorem cell20_511201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_511201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511201 prefixEnd_511201 := by exact prefixLift 511201
  have htrace : WordTrace (prefixWord ++ tailWord_511201) baseStart_511201 baseEnd_511201 := by
    simpa [prefixWord, tailWord_511201, baseEnd_511201] using wordTrace_append hprefix tailTrace_511201
  have hstable : (prefixWord ++ tailWord_511201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511201).length < 2 ^ (prefixWord ++ tailWord_511201).sum := by decide
  have hdescent : baseEnd_511201 < baseStart_511201 := by decide
  rcases family_descends (prefixWord ++ tailWord_511201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511215 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_511215 : Nat := 118140960795 + 511215 * 2 ^ 59
def prefixEnd_511215 : Nat := 4983230072969 + 3 ^ 40 * 511215 * 2
def baseEnd_511215 : Nat := 233332455811842313476863

theorem tailTrace_511215 : CollatzResearch.WordTrace tailWord_511215 prefixEnd_511215 233332455811842313476863 := by
  unfold tailWord_511215
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645542842962838416119099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12430361895308558944079399 18645542842962838416119099)
  ·
    refine ⟨27968314264444257624178649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18645542842962838416119099 27968314264444257624178649)
    ·
      refine ⟨20976235698333193218133987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27968314264444257624178649 20976235698333193218133987)
      ·
        refine ⟨31464353547499789827200981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20976235698333193218133987 31464353547499789827200981)
        ·
          refine ⟨737445786269526324075023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31464353547499789827200981 737445786269526324075023)
          ·
            refine ⟨1106168679404289486112535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737445786269526324075023 1106168679404289486112535)
            ·
              refine ⟨1659253019106434229168803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106168679404289486112535 1659253019106434229168803)
              ·
                refine ⟨2488879528659651343753205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659253019106434229168803 2488879528659651343753205)
                ·
                  refine ⟨233332455811842313476863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488879528659651343753205 233332455811842313476863)
                  ·
                    rfl

theorem cell20_511215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_511215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511215 prefixEnd_511215 := by exact prefixLift 511215
  have htrace : WordTrace (prefixWord ++ tailWord_511215) baseStart_511215 baseEnd_511215 := by
    simpa [prefixWord, tailWord_511215, baseEnd_511215] using wordTrace_append hprefix tailTrace_511215
  have hstable : (prefixWord ++ tailWord_511215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511215).length < 2 ^ (prefixWord ++ tailWord_511215).sum := by decide
  have hdescent : baseEnd_511215 < baseStart_511215 := by decide
  rcases family_descends (prefixWord ++ tailWord_511215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511246 : List Nat := [4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_511246 : Nat := 118140960795 + 511246 * 2 ^ 59
def prefixEnd_511246 : Nat := 4983230072969 + 3 ^ 40 * 511246 * 2
def baseEnd_511246 : Nat := 77782201685514661147801

theorem tailTrace_511246 : CollatzResearch.WordTrace tailWord_511246 prefixEnd_511246 77782201685514661147801 := by
  unfold tailWord_511246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330834188231316338812199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12431115670567020473665061 2330834188231316338812199)
  ·
    refine ⟨3496251282346974508218299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330834188231316338812199 3496251282346974508218299)
    ·
      refine ⟨5244376923520461762327449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496251282346974508218299 5244376923520461762327449)
      ·
        refine ⟨3933282692640346321745587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5244376923520461762327449 3933282692640346321745587)
        ·
          refine ⟨5899924038960519482618381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933282692640346321745587 5899924038960519482618381)
          ·
            refine ⟨2212471514610194805981893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5899924038960519482618381 2212471514610194805981893)
            ·
              refine ⟨414838408989411526121605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2212471514610194805981893 414838408989411526121605)
              ·
                refine ⟨77782201685514661147801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414838408989411526121605 77782201685514661147801)
                ·
                  rfl

theorem cell20_511246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_511246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511246 prefixEnd_511246 := by exact prefixLift 511246
  have htrace : WordTrace (prefixWord ++ tailWord_511246) baseStart_511246 baseEnd_511246 := by
    simpa [prefixWord, tailWord_511246, baseEnd_511246] using wordTrace_append hprefix tailTrace_511246
  have hstable : (prefixWord ++ tailWord_511246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511246).length < 2 ^ (prefixWord ++ tailWord_511246).sum := by decide
  have hdescent : baseEnd_511246 < baseStart_511246 := by decide
  rcases family_descends (prefixWord ++ tailWord_511246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511256 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_511256 : Nat := 118140960795 + 511256 * 2 ^ 59
def prefixEnd_511256 : Nat := 4983230072969 + 3 ^ 40 * 511256 * 2
def baseEnd_511256 : Nat := 233351169329028393110029

theorem tailTrace_511256 : CollatzResearch.WordTrace tailWord_511256 prefixEnd_511256 233351169329028393110029 := by
  unfold tailWord_511256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323519117907151209180811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12431358823876201612241081 9323519117907151209180811)
  ·
    refine ⟨13985278676860726813771217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9323519117907151209180811 13985278676860726813771217)
    ·
      refine ⟨10488959007645545110328413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13985278676860726813771217 10488959007645545110328413)
      ·
        refine ⟨3933359627867079416373155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10488959007645545110328413 3933359627867079416373155)
        ·
          refine ⟨5900039441800619124559733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933359627867079416373155 5900039441800619124559733)
          ·
            refine ⟨553128697668808042927475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5900039441800619124559733 553128697668808042927475)
            ·
              refine ⟨829693046503212064391213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553128697668808042927475 829693046503212064391213)
              ·
                refine ⟨311134892438704524146705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829693046503212064391213 311134892438704524146705)
                ·
                  refine ⟨233351169329028393110029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311134892438704524146705 233351169329028393110029)
                  ·
                    rfl

theorem cell20_511256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_511256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511256 prefixEnd_511256 := by exact prefixLift 511256
  have htrace : WordTrace (prefixWord ++ tailWord_511256) baseStart_511256 baseEnd_511256 := by
    simpa [prefixWord, tailWord_511256, baseEnd_511256] using wordTrace_append hprefix tailTrace_511256
  have hstable : (prefixWord ++ tailWord_511256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511256).length < 2 ^ (prefixWord ++ tailWord_511256).sum := by decide
  have hdescent : baseEnd_511256 < baseStart_511256 := by decide
  rcases family_descends (prefixWord ++ tailWord_511256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511267 : List Nat := [1, 1, 1, 4, 2, 5, 6]
def baseStart_511267 : Nat := 118140960795 + 511267 * 2 ^ 59
def prefixEnd_511267 : Nat := 4983230072969 + 3 ^ 40 * 511267 * 2
def baseEnd_511267 : Nat := 25928465558751249304813

theorem tailTrace_511267 : CollatzResearch.WordTrace tailWord_511267 prefixEnd_511267 25928465558751249304813 := by
  unfold tailWord_511267
  simp only [CollatzResearch.WordTrace]
  refine ⟨18647439438774451297012055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12431626292516300864674703 18647439438774451297012055)
  ·
    refine ⟨27971159158161676945518083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18647439438774451297012055 27971159158161676945518083)
    ·
      refine ⟨41956738737242515418277125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27971159158161676945518083 41956738737242515418277125)
      ·
        refine ⟨7866888513232971640926961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41956738737242515418277125 7866888513232971640926961)
        ·
          refine ⟨5900166384924728730695221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7866888513232971640926961 5900166384924728730695221)
          ·
            refine ⟨553140598586693318502677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5900166384924728730695221 553140598586693318502677)
            ·
              refine ⟨25928465558751249304813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553140598586693318502677 25928465558751249304813)
              ·
                rfl

theorem cell20_511267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_511267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511267 prefixEnd_511267 := by exact prefixLift 511267
  have htrace : WordTrace (prefixWord ++ tailWord_511267) baseStart_511267 baseEnd_511267 := by
    simpa [prefixWord, tailWord_511267, baseEnd_511267] using wordTrace_append hprefix tailTrace_511267
  have hstable : (prefixWord ++ tailWord_511267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511267).length < 2 ^ (prefixWord ++ tailWord_511267).sum := by decide
  have hdescent : baseEnd_511267 < baseStart_511267 := by decide
  rcases family_descends (prefixWord ++ tailWord_511267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511284 : List Nat := [2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_511284 : Nat := 118140960795 + 511284 * 2 ^ 59
def prefixEnd_511284 : Nat := 4983230072969 + 3 ^ 40 * 511284 * 2
def baseEnd_511284 : Nat := 77787983097328246725527

theorem tailTrace_511284 : CollatzResearch.WordTrace tailWord_511284 prefixEnd_511284 77787983097328246725527 := by
  unfold tailWord_511284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9324029739856431600190453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12432039653141908800253937 9324029739856431600190453)
  ·
    refine ⟨874127788111540462517855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9324029739856431600190453 874127788111540462517855)
    ·
      refine ⟨1311191682167310693776783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874127788111540462517855 1311191682167310693776783)
      ·
        refine ⟨1966787523250966040665175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311191682167310693776783 1966787523250966040665175)
        ·
          refine ⟨2950181284876449060997763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966787523250966040665175 2950181284876449060997763)
          ·
            refine ⟨4425271927314673591496645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950181284876449060997763 4425271927314673591496645)
            ·
              refine ⟨829738486371501298405621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4425271927314673591496645 829738486371501298405621)
              ·
                refine ⟨77787983097328246725527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 829738486371501298405621 77787983097328246725527)
                ·
                  rfl

theorem cell20_511284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_511284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511284 prefixEnd_511284 := by exact prefixLift 511284
  have htrace : WordTrace (prefixWord ++ tailWord_511284) baseStart_511284 baseEnd_511284 := by
    simpa [prefixWord, tailWord_511284, baseEnd_511284] using wordTrace_append hprefix tailTrace_511284
  have hstable : (prefixWord ++ tailWord_511284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511284).length < 2 ^ (prefixWord ++ tailWord_511284).sum := by decide
  have hdescent : baseEnd_511284 < baseStart_511284 := by decide
  rcases family_descends (prefixWord ++ tailWord_511284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511318 : List Nat := [5, 2, 3, 1, 1, 8]
def baseStart_511318 : Nat := 118140960795 + 511318 * 2 ^ 59
def prefixEnd_511318 : Nat := 4983230072969 + 3 ^ 40 * 511318 * 2
def baseEnd_511318 : Nat := 8643683993275249371967

theorem tailTrace_511318 : CollatzResearch.WordTrace tailWord_511318 prefixEnd_511318 8643683993275249371967 := by
  unfold tailWord_511318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165581222599355437944913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12432866374393124671412405 1165581222599355437944913)
  ·
    refine ⟨874185916949516578458685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1165581222599355437944913 874185916949516578458685)
    ·
      refine ⟨327819718856068716922007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 874185916949516578458685 327819718856068716922007)
      ·
        refine ⟨491729578284103075383011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327819718856068716922007 491729578284103075383011)
        ·
          refine ⟨737594367426154613074517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491729578284103075383011 737594367426154613074517)
          ·
            refine ⟨8643683993275249371967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 737594367426154613074517 8643683993275249371967)
            ·
              rfl

theorem cell20_511318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 8].length) (baseStart_511318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511318 prefixEnd_511318 := by exact prefixLift 511318
  have htrace : WordTrace (prefixWord ++ tailWord_511318) baseStart_511318 baseEnd_511318 := by
    simpa [prefixWord, tailWord_511318, baseEnd_511318] using wordTrace_append hprefix tailTrace_511318
  have hstable : (prefixWord ++ tailWord_511318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511318).length < 2 ^ (prefixWord ++ tailWord_511318).sum := by decide
  have hdescent : baseEnd_511318 < baseStart_511318 := by decide
  rcases family_descends (prefixWord ++ tailWord_511318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511332 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_511332 : Nat := 118140960795 + 511332 * 2 ^ 59
def prefixEnd_511332 : Nat := 4983230072969 + 3 ^ 40 * 511332 * 2
def baseEnd_511332 : Nat := 233385857799909906576385

theorem tailTrace_511332 : CollatzResearch.WordTrace tailWord_511332 prefixEnd_511332 233385857799909906576385 := by
  unfold tailWord_511332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9324905091769483699064125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12433206789025978265418833 9324905091769483699064125)
  ·
    refine ⟨3496839409413556387149047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9324905091769483699064125 3496839409413556387149047)
    ·
      refine ⟨5245259114120334580723571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496839409413556387149047 5245259114120334580723571)
      ·
        refine ⟨7867888671180501871085357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245259114120334580723571 7867888671180501871085357)
        ·
          refine ⟨2950458251692688201657009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7867888671180501871085357 2950458251692688201657009)
          ·
            refine ⟨2212843688769516151242757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950458251692688201657009 2212843688769516151242757)
            ·
              refine ⟨414908191644284278358017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2212843688769516151242757 414908191644284278358017)
              ·
                refine ⟨311181143733213208768513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414908191644284278358017 311181143733213208768513)
                ·
                  refine ⟨233385857799909906576385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311181143733213208768513 233385857799909906576385)
                  ·
                    rfl

theorem cell20_511332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_511332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511332 prefixEnd_511332 := by exact prefixLift 511332
  have htrace : WordTrace (prefixWord ++ tailWord_511332) baseStart_511332 baseEnd_511332 := by
    simpa [prefixWord, tailWord_511332, baseEnd_511332] using wordTrace_append hprefix tailTrace_511332
  have hstable : (prefixWord ++ tailWord_511332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511332).length < 2 ^ (prefixWord ++ tailWord_511332).sum := by decide
  have hdescent : baseEnd_511332 < baseStart_511332 := by decide
  rcases family_descends (prefixWord ++ tailWord_511332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511391 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 2]
def baseStart_511391 : Nat := 118140960795 + 511391 * 2 ^ 59
def prefixEnd_511391 : Nat := 4983230072969 + 3 ^ 40 * 511391 * 2
def baseEnd_511391 : Nat := 233412787007567923609477

theorem tailTrace_511391 : CollatzResearch.WordTrace tailWord_511391 prefixEnd_511391 233412787007567923609477 := by
  unfold tailWord_511391
  simp only [CollatzResearch.WordTrace]
  refine ⟨18651962090325220474526027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12434641393550146983017351 18651962090325220474526027)
  ·
    refine ⟨27977943135487830711789041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18651962090325220474526027 27977943135487830711789041)
    ·
      refine ⟨20983457351615873033841781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27977943135487830711789041 20983457351615873033841781)
      ·
        refine ⟨1967199126713988096922667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20983457351615873033841781 1967199126713988096922667)
        ·
          refine ⟨2950798690070982145384001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967199126713988096922667 2950798690070982145384001)
          ·
            refine ⟨2213099017553236609038001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950798690070982145384001 2213099017553236609038001)
            ·
              refine ⟨1659824263164927456778501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213099017553236609038001 1659824263164927456778501)
              ·
                refine ⟨311217049343423898145969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1659824263164927456778501 311217049343423898145969)
                ·
                  refine ⟨233412787007567923609477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311217049343423898145969 233412787007567923609477)
                  ·
                    rfl

theorem cell20_511391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2].length) (baseStart_511391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511391 prefixEnd_511391 := by exact prefixLift 511391
  have htrace : WordTrace (prefixWord ++ tailWord_511391) baseStart_511391 baseEnd_511391 := by
    simpa [prefixWord, tailWord_511391, baseEnd_511391] using wordTrace_append hprefix tailTrace_511391
  have hstable : (prefixWord ++ tailWord_511391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511391).length < 2 ^ (prefixWord ++ tailWord_511391).sum := by decide
  have hdescent : baseEnd_511391 < baseStart_511391 := by decide
  rcases family_descends (prefixWord ++ tailWord_511391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511446 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_511446 : Nat := 118140960795 + 511446 * 2 ^ 59
def prefixEnd_511446 : Nat := 4983230072969 + 3 ^ 40 * 511446 * 2
def baseEnd_511446 : Nat := 233437890506232176775919

theorem tailTrace_511446 : CollatzResearch.WordTrace tailWord_511446 prefixEnd_511446 233437890506232176775919 := by
  unfold tailWord_511446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165873006570372804236137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12435978736750643245185461 1165873006570372804236137)
  ·
    refine ⟨874404754927779603177103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1165873006570372804236137 874404754927779603177103)
    ·
      refine ⟨1311607132391669404765655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874404754927779603177103 1311607132391669404765655)
      ·
        refine ⟨1967410698587504107148483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311607132391669404765655 1967410698587504107148483)
        ·
          refine ⟨2951116047881256160722725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967410698587504107148483 2951116047881256160722725)
          ·
            refine ⟨553334258977735530135511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2951116047881256160722725 553334258977735530135511)
            ·
              refine ⟨830001388466603295203267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553334258977735530135511 830001388466603295203267)
              ·
                refine ⟨1245002082699904942804901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830001388466603295203267 1245002082699904942804901)
                ·
                  refine ⟨233437890506232176775919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245002082699904942804901 233437890506232176775919)
                  ·
                    rfl

theorem cell20_511446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_511446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511446 prefixEnd_511446 := by exact prefixLift 511446
  have htrace : WordTrace (prefixWord ++ tailWord_511446) baseStart_511446 baseEnd_511446 := by
    simpa [prefixWord, tailWord_511446, baseEnd_511446] using wordTrace_append hprefix tailTrace_511446
  have hstable : (prefixWord ++ tailWord_511446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511446).length < 2 ^ (prefixWord ++ tailWord_511446).sum := by decide
  have hdescent : baseEnd_511446 < baseStart_511446 := by decide
  rcases family_descends (prefixWord ++ tailWord_511446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511450 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_511450 : Nat := 118140960795 + 511450 * 2 ^ 59
def prefixEnd_511450 : Nat := 4983230072969 + 3 ^ 40 * 511450 * 2
def baseEnd_511450 : Nat := 233439716215225940642569

theorem tailTrace_511450 : CollatzResearch.WordTrace tailWord_511450 prefixEnd_511450 233439716215225940642569 := by
  unfold tailWord_511450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663528499277868387730951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12436075998074315700615869 4663528499277868387730951)
  ·
    refine ⟨6995292748916802581596427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4663528499277868387730951 6995292748916802581596427)
    ·
      refine ⟨10492939123375203872394641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6995292748916802581596427 10492939123375203872394641)
      ·
        refine ⟨7869704342531402904295981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492939123375203872394641 7869704342531402904295981)
        ·
          refine ⟨2951139128449276089110993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7869704342531402904295981 2951139128449276089110993)
          ·
            refine ⟨2213354346336957066833245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951139128449276089110993 2213354346336957066833245)
            ·
              refine ⟨830007879876358900062467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213354346336957066833245 830007879876358900062467)
              ·
                refine ⟨1245011819814538350093701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830007879876358900062467 1245011819814538350093701)
                ·
                  refine ⟨233439716215225940642569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245011819814538350093701 233439716215225940642569)
                  ·
                    rfl

theorem cell20_511450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_511450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511450 prefixEnd_511450 := by exact prefixLift 511450
  have htrace : WordTrace (prefixWord ++ tailWord_511450) baseStart_511450 baseEnd_511450 := by
    simpa [prefixWord, tailWord_511450, baseEnd_511450] using wordTrace_append hprefix tailTrace_511450
  have hstable : (prefixWord ++ tailWord_511450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511450).length < 2 ^ (prefixWord ++ tailWord_511450).sum := by decide
  have hdescent : baseEnd_511450 < baseStart_511450 := by decide
  rcases family_descends (prefixWord ++ tailWord_511450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511457 : List Nat := [1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_511457 : Nat := 118140960795 + 511457 * 2 ^ 59
def prefixEnd_511457 : Nat := 4983230072969 + 3 ^ 40 * 511457 * 2
def baseEnd_511457 : Nat := 77814303735321675803069

theorem tailTrace_511457 : CollatzResearch.WordTrace tailWord_511457 prefixEnd_511457 77814303735321675803069 := by
  unfold tailWord_511457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654369308086113746428625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12436246205390742497619083 18654369308086113746428625)
  ·
    refine ⟨13990776981064585309821469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18654369308086113746428625 13990776981064585309821469)
    ·
      refine ⟨5246541367899219491183051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13990776981064585309821469 5246541367899219491183051)
      ·
        refine ⟨7869812051848829236774577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246541367899219491183051 7869812051848829236774577)
        ·
          refine ⟨5902359038886621927580933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7869812051848829236774577 5902359038886621927580933)
          ·
            refine ⟨1106692319791241611421425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5902359038886621927580933 1106692319791241611421425)
            ·
              refine ⟨830019239843431208566069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106692319791241611421425 830019239843431208566069)
              ·
                refine ⟨77814303735321675803069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830019239843431208566069 77814303735321675803069)
                ·
                  rfl

theorem cell20_511457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_511457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511457 prefixEnd_511457 := by exact prefixLift 511457
  have htrace : WordTrace (prefixWord ++ tailWord_511457) baseStart_511457 baseEnd_511457 := by
    simpa [prefixWord, tailWord_511457, baseEnd_511457] using wordTrace_append hprefix tailTrace_511457
  have hstable : (prefixWord ++ tailWord_511457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511457).length < 2 ^ (prefixWord ++ tailWord_511457).sum := by decide
  have hdescent : baseEnd_511457 < baseStart_511457 := by decide
  rcases family_descends (prefixWord ++ tailWord_511457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511471 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_511471 : Nat := 118140960795 + 511471 * 2 ^ 59
def prefixEnd_511471 : Nat := 4983230072969 + 3 ^ 40 * 511471 * 2
def baseEnd_511471 : Nat := 233449301187443200942483

theorem tailTrace_511471 : CollatzResearch.WordTrace tailWord_511471 prefixEnd_511471 233449301187443200942483 := by
  unfold tailWord_511471
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654879930035394137438267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12436586620023596091625511 18654879930035394137438267)
  ·
    refine ⟨27982319895053091206157401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18654879930035394137438267 27982319895053091206157401)
    ·
      refine ⟨20986739921289818404618051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27982319895053091206157401 20986739921289818404618051)
      ·
        refine ⟨31480109881934727606927077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20986739921289818404618051 31480109881934727606927077)
        ·
          refine ⟨5902520602862761426298827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31480109881934727606927077 5902520602862761426298827)
          ·
            refine ⟨8853780904294142139448241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902520602862761426298827 8853780904294142139448241)
            ·
              refine ⟨6640335678220606604586181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853780904294142139448241 6640335678220606604586181)
              ·
                refine ⟨1245062939666363738359909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6640335678220606604586181 1245062939666363738359909)
                ·
                  refine ⟨233449301187443200942483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245062939666363738359909 233449301187443200942483)
                  ·
                    rfl

theorem cell20_511471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_511471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511471 prefixEnd_511471 := by exact prefixLift 511471
  have htrace : WordTrace (prefixWord ++ tailWord_511471) baseStart_511471 baseEnd_511471 := by
    simpa [prefixWord, tailWord_511471, baseEnd_511471] using wordTrace_append hprefix tailTrace_511471
  have hstable : (prefixWord ++ tailWord_511471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511471).length < 2 ^ (prefixWord ++ tailWord_511471).sum := by decide
  have hdescent : baseEnd_511471 < baseStart_511471 := by decide
  rcases family_descends (prefixWord ++ tailWord_511471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511508 : List Nat := [2, 4, 3, 1, 3, 1, 1, 5]
def baseStart_511508 : Nat := 118140960795 + 511508 * 2 ^ 59
def prefixEnd_511508 : Nat := 4983230072969 + 3 ^ 40 * 511508 * 2
def baseEnd_511508 : Nat := 77822062998545172236333

theorem tailTrace_511508 : CollatzResearch.WordTrace tailWord_511508 prefixEnd_511508 77822062998545172236333 := by
  unfold tailWord_511508
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328114715450674728267589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12437486287267566304356785 9328114715450674728267589)
  ·
    refine ⟨1749021509147001511550173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9328114715450674728267589 1749021509147001511550173)
    ·
      refine ⟨655883065930125566831315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1749021509147001511550173 655883065930125566831315)
      ·
        refine ⟨983824598895188350246973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655883065930125566831315 983824598895188350246973)
        ·
          refine ⟨368934224585695631342615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983824598895188350246973 368934224585695631342615)
          ·
            refine ⟨553401336878543447013923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368934224585695631342615 553401336878543447013923)
            ·
              refine ⟨830102005317815170520885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553401336878543447013923 830102005317815170520885)
              ·
                refine ⟨77822062998545172236333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830102005317815170520885 77822062998545172236333)
                ·
                  rfl

theorem cell20_511508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_511508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511508 prefixEnd_511508 := by exact prefixLift 511508
  have htrace : WordTrace (prefixWord ++ tailWord_511508) baseStart_511508 baseEnd_511508 := by
    simpa [prefixWord, tailWord_511508, baseEnd_511508] using wordTrace_append hprefix tailTrace_511508
  have hstable : (prefixWord ++ tailWord_511508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511508).length < 2 ^ (prefixWord ++ tailWord_511508).sum := by decide
  have hdescent : baseEnd_511508 < baseStart_511508 := by decide
  rcases family_descends (prefixWord ++ tailWord_511508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511512 : List Nat := [2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_511512 : Nat := 118140960795 + 511512 * 2 ^ 59
def prefixEnd_511512 : Nat := 4983230072969 + 3 ^ 40 * 511512 * 2
def baseEnd_511512 : Nat := 77822671568209760191883

theorem tailTrace_511512 : CollatzResearch.WordTrace tailWord_511512 prefixEnd_511512 77822671568209760191883 := by
  unfold tailWord_511512
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328187661443429069840395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12437583548591238759787193 9328187661443429069840395)
  ·
    refine ⟨13992281492165143604760593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9328187661443429069840395 13992281492165143604760593)
    ·
      refine ⟨10494211119123857703570445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13992281492165143604760593 10494211119123857703570445)
      ·
        refine ⟨3935329169671446638838917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10494211119123857703570445 3935329169671446638838917)
        ·
          refine ⟨737874219313396244782297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3935329169671446638838917 737874219313396244782297)
          ·
            refine ⟨553405664485047183586723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737874219313396244782297 553405664485047183586723)
            ·
              refine ⟨830108496727570775380085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553405664485047183586723 830108496727570775380085)
              ·
                refine ⟨77822671568209760191883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830108496727570775380085 77822671568209760191883)
                ·
                  rfl

theorem cell20_511512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_511512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511512 prefixEnd_511512 := by exact prefixLift 511512
  have htrace : WordTrace (prefixWord ++ tailWord_511512) baseStart_511512 baseEnd_511512 := by
    simpa [prefixWord, tailWord_511512, baseEnd_511512] using wordTrace_append hprefix tailTrace_511512
  have hstable : (prefixWord ++ tailWord_511512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511512).length < 2 ^ (prefixWord ++ tailWord_511512).sum := by decide
  have hdescent : baseEnd_511512 < baseStart_511512 := by decide
  rcases family_descends (prefixWord ++ tailWord_511512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511543 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 2]
def baseStart_511543 : Nat := 118140960795 + 511543 * 2 ^ 59
def prefixEnd_511543 : Nat := 4983230072969 + 3 ^ 40 * 511543 * 2
def baseEnd_511543 : Nat := 233482163949330950542189

theorem tailTrace_511543 : CollatzResearch.WordTrace tailWord_511543 prefixEnd_511543 233482163949330950542189 := by
  unfold tailWord_511543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657505985774550434059283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12438337323849700289372855 18657505985774550434059283)
  ·
    refine ⟨27986258978661825651088925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18657505985774550434059283 27986258978661825651088925)
    ·
      refine ⟨10494847116998184619158347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27986258978661825651088925 10494847116998184619158347)
      ·
        refine ⟨15742270675497276928737521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494847116998184619158347 15742270675497276928737521)
        ·
          refine ⟨11806703006622957696553141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15742270675497276928737521 11806703006622957696553141)
          ·
            refine ⟨1106878406870902284051857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11806703006622957696553141 1106878406870902284051857)
            ·
              refine ⟨830158805153176713038893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106878406870902284051857 830158805153176713038893)
              ·
                refine ⟨311309551932441267389585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830158805153176713038893 311309551932441267389585)
                ·
                  refine ⟨233482163949330950542189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311309551932441267389585 233482163949330950542189)
                  ·
                    rfl

theorem cell20_511543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2].length) (baseStart_511543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511543 prefixEnd_511543 := by exact prefixLift 511543
  have htrace : WordTrace (prefixWord ++ tailWord_511543) baseStart_511543 baseEnd_511543 := by
    simpa [prefixWord, tailWord_511543, baseEnd_511543] using wordTrace_append hprefix tailTrace_511543
  have hstable : (prefixWord ++ tailWord_511543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511543).length < 2 ^ (prefixWord ++ tailWord_511543).sum := by decide
  have hdescent : baseEnd_511543 < baseStart_511543 := by decide
  rcases family_descends (prefixWord ++ tailWord_511543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511564 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_511564 : Nat := 118140960795 + 511564 * 2 ^ 59
def prefixEnd_511564 : Nat := 4983230072969 + 3 ^ 40 * 511564 * 2
def baseEnd_511564 : Nat := 233491748921548210842103

theorem tailTrace_511564 : CollatzResearch.WordTrace tailWord_511564 prefixEnd_511564 233491748921548210842103 := by
  unfold tailWord_511564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329135959349235510286873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12438847945798980680382497 9329135959349235510286873)
  ·
    refine ⟨6996851969511926632715155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9329135959349235510286873 6996851969511926632715155)
    ·
      refine ⟨10495277954267889949072733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996851969511926632715155 10495277954267889949072733)
      ·
        refine ⟨3935729232850458730902275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495277954267889949072733 3935729232850458730902275)
        ·
          refine ⟨5903593849275688096353413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935729232850458730902275 5903593849275688096353413)
          ·
            refine ⟨1106923846739191518066265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5903593849275688096353413 1106923846739191518066265)
            ·
              refine ⟨830192885054393638549699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106923846739191518066265 830192885054393638549699)
              ·
                refine ⟨1245289327581590457824549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830192885054393638549699 1245289327581590457824549)
                ·
                  refine ⟨233491748921548210842103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245289327581590457824549 233491748921548210842103)
                  ·
                    rfl

theorem cell20_511564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_511564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511564 prefixEnd_511564 := by exact prefixLift 511564
  have htrace : WordTrace (prefixWord ++ tailWord_511564) baseStart_511564 baseEnd_511564 := by
    simpa [prefixWord, tailWord_511564, baseEnd_511564] using wordTrace_append hprefix tailTrace_511564
  have hstable : (prefixWord ++ tailWord_511564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511564).length < 2 ^ (prefixWord ++ tailWord_511564).sum := by decide
  have hdescent : baseEnd_511564 < baseStart_511564 := by decide
  rcases family_descends (prefixWord ++ tailWord_511564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511578 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_511578 : Nat := 118140960795 + 511578 * 2 ^ 59
def prefixEnd_511578 : Nat := 4983230072969 + 3 ^ 40 * 511578 * 2
def baseEnd_511578 : Nat := 233498138903026384375379

theorem tailTrace_511578 : CollatzResearch.WordTrace tailWord_511578 prefixEnd_511578 233498138903026384375379 := by
  unfold tailWord_511578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664695635161937852895847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12439188360431834274388925 4664695635161937852895847)
  ·
    refine ⟨6997043452742906779343771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4664695635161937852895847 6997043452742906779343771)
    ·
      refine ⟨10495565179114360169015657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997043452742906779343771 10495565179114360169015657)
      ·
        refine ⟨7871673884335770126761743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10495565179114360169015657 7871673884335770126761743)
        ·
          refine ⟨11807510826503655190142615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871673884335770126761743 11807510826503655190142615)
          ·
            refine ⟨17711266239755482785213923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807510826503655190142615 17711266239755482785213923)
            ·
              refine ⟨26566899359633224177820885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711266239755482785213923 26566899359633224177820885)
              ·
                refine ⟨622661703741403691667677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26566899359633224177820885 622661703741403691667677)
                ·
                  refine ⟨233498138903026384375379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622661703741403691667677 233498138903026384375379)
                  ·
                    rfl

theorem cell20_511578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_511578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511578 prefixEnd_511578 := by exact prefixLift 511578
  have htrace : WordTrace (prefixWord ++ tailWord_511578) baseStart_511578 baseEnd_511578 := by
    simpa [prefixWord, tailWord_511578, baseEnd_511578] using wordTrace_append hprefix tailTrace_511578
  have hstable : (prefixWord ++ tailWord_511578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511578).length < 2 ^ (prefixWord ++ tailWord_511578).sum := by decide
  have hdescent : baseEnd_511578 < baseStart_511578 := by decide
  rcases family_descends (prefixWord ++ tailWord_511578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511585 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_511585 : Nat := 118140960795 + 511585 * 2 ^ 59
def prefixEnd_511585 : Nat := 4983230072969 + 3 ^ 40 * 511585 * 2
def baseEnd_511585 : Nat := 233501333893765471142017

theorem tailTrace_511585 : CollatzResearch.WordTrace tailWord_511585 prefixEnd_511585 233501333893765471142017 := by
  unfold tailWord_511585
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659037851622391607088209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12439358567748261071392139 18659037851622391607088209)
  ·
    refine ⟨13994278388716793705316157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18659037851622391607088209 13994278388716793705316157)
    ·
      refine ⟨5247854395768797639493559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13994278388716793705316157 5247854395768797639493559)
      ·
        refine ⟨7871781593653196459240339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247854395768797639493559 7871781593653196459240339)
        ·
          refine ⟨11807672390479794688860509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871781593653196459240339 11807672390479794688860509)
          ·
            refine ⟨4427877146429923008322691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11807672390479794688860509 4427877146429923008322691)
            ·
              refine ⟨6641815719644884512484037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427877146429923008322691 6641815719644884512484037)
              ·
                refine ⟨1245340447433415846090757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6641815719644884512484037 1245340447433415846090757)
                ·
                  refine ⟨233501333893765471142017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245340447433415846090757 233501333893765471142017)
                  ·
                    rfl

theorem cell20_511585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_511585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511585 prefixEnd_511585 := by exact prefixLift 511585
  have htrace : WordTrace (prefixWord ++ tailWord_511585) baseStart_511585 baseEnd_511585 := by
    simpa [prefixWord, tailWord_511585, baseEnd_511585] using wordTrace_append hprefix tailTrace_511585
  have hstable : (prefixWord ++ tailWord_511585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511585).length < 2 ^ (prefixWord ++ tailWord_511585).sum := by decide
  have hdescent : baseEnd_511585 < baseStart_511585 := by decide
  rcases family_descends (prefixWord ++ tailWord_511585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511588 : List Nat := [2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_511588 : Nat := 118140960795 + 511588 * 2 ^ 59
def prefixEnd_511588 : Nat := 4983230072969 + 3 ^ 40 * 511588 * 2
def baseEnd_511588 : Nat := 77834234391836931347335

theorem tailTrace_511588 : CollatzResearch.WordTrace tailWord_511588 prefixEnd_511588 77834234391836931347335 := by
  unfold tailWord_511588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329573635305761559723709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12439431513741015412964945 9329573635305761559723709)
  ·
    refine ⟨3498590113239660584896391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9329573635305761559723709 3498590113239660584896391)
    ·
      refine ⟨5247885169859490877344587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498590113239660584896391 5247885169859490877344587)
      ·
        refine ⟨7871827754789236316016881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247885169859490877344587 7871827754789236316016881)
        ·
          refine ⟨5903870816091927237012661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7871827754789236316016881 5903870816091927237012661)
          ·
            refine ⟨553487889008618178469937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5903870816091927237012661 553487889008618178469937)
            ·
              refine ⟨415115916756463633852453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553487889008618178469937 415115916756463633852453)
              ·
                refine ⟨77834234391836931347335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415115916756463633852453 77834234391836931347335)
                ·
                  rfl

theorem cell20_511588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_511588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511588 prefixEnd_511588 := by exact prefixLift 511588
  have htrace : WordTrace (prefixWord ++ tailWord_511588) baseStart_511588 baseEnd_511588 := by
    simpa [prefixWord, tailWord_511588, baseEnd_511588] using wordTrace_append hprefix tailTrace_511588
  have hstable : (prefixWord ++ tailWord_511588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511588).length < 2 ^ (prefixWord ++ tailWord_511588).sum := by decide
  have hdescent : baseEnd_511588 < baseStart_511588 := by decide
  rcases family_descends (prefixWord ++ tailWord_511588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511616 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_511616 : Nat := 118140960795 + 511616 * 2 ^ 59
def prefixEnd_511616 : Nat := 4983230072969 + 3 ^ 40 * 511616 * 2
def baseEnd_511616 : Nat := 233515483138467141108557

theorem tailTrace_511616 : CollatzResearch.WordTrace tailWord_511616 prefixEnd_511616 233515483138467141108557 := by
  unfold tailWord_511616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330084257255041950733351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12440112343006722600977801 9330084257255041950733351)
  ·
    refine ⟨13995126385882562926100027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330084257255041950733351 13995126385882562926100027)
    ·
      refine ⟨20992689578823844389150041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995126385882562926100027 20992689578823844389150041)
      ·
        refine ⟨15744517184117883291862531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20992689578823844389150041 15744517184117883291862531)
        ·
          refine ⟨23616775776176824937793797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15744517184117883291862531 23616775776176824937793797)
          ·
            refine ⟨4428145458033154675836337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23616775776176824937793797 4428145458033154675836337)
            ·
              refine ⟨3321109093524866006877253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428145458033154675836337 3321109093524866006877253)
              ·
                refine ⟨622707955035912376289485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3321109093524866006877253 622707955035912376289485)
                ·
                  refine ⟨233515483138467141108557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622707955035912376289485 233515483138467141108557)
                  ·
                    rfl

theorem cell20_511616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_511616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511616 prefixEnd_511616 := by exact prefixLift 511616
  have htrace : WordTrace (prefixWord ++ tailWord_511616) baseStart_511616 baseEnd_511616 := by
    simpa [prefixWord, tailWord_511616, baseEnd_511616] using wordTrace_append hprefix tailTrace_511616
  have hstable : (prefixWord ++ tailWord_511616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511616).length < 2 ^ (prefixWord ++ tailWord_511616).sum := by decide
  have hdescent : baseEnd_511616 < baseStart_511616 := by decide
  rcases family_descends (prefixWord ++ tailWord_511616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511668 : List Nat := [2, 5, 13]
def baseStart_511668 : Nat := 118140960795 + 511668 * 2 ^ 59
def prefixEnd_511668 : Nat := 4983230072969 + 3 ^ 40 * 511668 * 2
def baseEnd_511668 : Nat := 320355579362669508059

theorem tailTrace_511668 : CollatzResearch.WordTrace tailWord_511668 prefixEnd_511668 320355579362669508059 := by
  unfold tailWord_511668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331032555160848391179829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12441376740214464521573105 9331032555160848391179829)
  ·
    refine ⟨874784302046329536673109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9331032555160848391179829 874784302046329536673109)
    ·
      refine ⟨320355579362669508059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 874784302046329536673109 320355579362669508059)
      ·
        rfl

theorem cell20_511668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 13].length) (baseStart_511668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511668 prefixEnd_511668 := by exact prefixLift 511668
  have htrace : WordTrace (prefixWord ++ tailWord_511668) baseStart_511668 baseEnd_511668 := by
    simpa [prefixWord, tailWord_511668, baseEnd_511668] using wordTrace_append hprefix tailTrace_511668
  have hstable : (prefixWord ++ tailWord_511668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511668).length < 2 ^ (prefixWord ++ tailWord_511668).sum := by decide
  have hdescent : baseEnd_511668 < baseStart_511668 := by decide
  rcases family_descends (prefixWord ++ tailWord_511668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511670 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_511670 : Nat := 118140960795 + 511670 * 2 ^ 59
def prefixEnd_511670 : Nat := 4983230072969 + 3 ^ 40 * 511670 * 2
def baseEnd_511670 : Nat := 233540130209882953308337

theorem tailTrace_511670 : CollatzResearch.WordTrace tailWord_511670 prefixEnd_511670 233540130209882953308337 := by
  unfold tailWord_511670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166383628519653195245779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12441425370876300749288309 1166383628519653195245779)
  ·
    refine ⟨1749575442779479792868669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166383628519653195245779 1749575442779479792868669)
    ·
      refine ⟨656090791042304922325751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1749575442779479792868669 656090791042304922325751)
      ·
        refine ⟨984136186563457383488627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656090791042304922325751 984136186563457383488627)
        ·
          refine ⟨1476204279845186075232941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984136186563457383488627 1476204279845186075232941)
          ·
            refine ⟨553576604941944778212353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1476204279845186075232941 553576604941944778212353)
            ·
              refine ⟨415182453706458583659265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553576604941944778212353 415182453706458583659265)
              ·
                refine ⟨311386840279843937744449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415182453706458583659265 311386840279843937744449)
                ·
                  refine ⟨233540130209882953308337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311386840279843937744449 233540130209882953308337)
                  ·
                    rfl

theorem cell20_511670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_511670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511670 prefixEnd_511670 := by exact prefixLift 511670
  have htrace : WordTrace (prefixWord ++ tailWord_511670) baseStart_511670 baseEnd_511670 := by
    simpa [prefixWord, tailWord_511670, baseEnd_511670] using wordTrace_append hprefix tailTrace_511670
  have hstable : (prefixWord ++ tailWord_511670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511670).length < 2 ^ (prefixWord ++ tailWord_511670).sum := by decide
  have hdescent : baseEnd_511670 < baseStart_511670 := by decide
  rcases family_descends (prefixWord ++ tailWord_511670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511671 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_511671 : Nat := 118140960795 + 511671 * 2 ^ 59
def prefixEnd_511671 : Nat := 4983230072969 + 3 ^ 40 * 511671 * 2
def baseEnd_511671 : Nat := 233540586637131394274999

theorem tailTrace_511671 : CollatzResearch.WordTrace tailWord_511671 prefixEnd_511671 233540586637131394274999 := by
  unfold tailWord_511671
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662174529310828294718867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12441449686207218863145911 18662174529310828294718867)
  ·
    refine ⟨27993261793966242442078301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18662174529310828294718867 27993261793966242442078301)
    ·
      refine ⟨10497473172737340915779363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27993261793966242442078301 10497473172737340915779363)
      ·
        refine ⟨15746209759106011373669045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497473172737340915779363 15746209759106011373669045)
        ·
          refine ⟨1476207164916188566281473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15746209759106011373669045 1476207164916188566281473)
          ·
            refine ⟨1107155373687141424711105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476207164916188566281473 1107155373687141424711105)
            ·
              refine ⟨830366530265356068533329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107155373687141424711105 830366530265356068533329)
              ·
                refine ⟨622774897699017051399997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830366530265356068533329 622774897699017051399997)
                ·
                  refine ⟨233540586637131394274999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622774897699017051399997 233540586637131394274999)
                  ·
                    rfl

theorem cell20_511671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_511671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511671 prefixEnd_511671 := by exact prefixLift 511671
  have htrace : WordTrace (prefixWord ++ tailWord_511671) baseStart_511671 baseEnd_511671 := by
    simpa [prefixWord, tailWord_511671, baseEnd_511671] using wordTrace_append hprefix tailTrace_511671
  have hstable : (prefixWord ++ tailWord_511671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511671).length < 2 ^ (prefixWord ++ tailWord_511671).sum := by decide
  have hdescent : baseEnd_511671 < baseStart_511671 := by decide
  rcases family_descends (prefixWord ++ tailWord_511671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511674 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_511674 : Nat := 118140960795 + 511674 * 2 ^ 59
def prefixEnd_511674 : Nat := 4983230072969 + 3 ^ 40 * 511674 * 2
def baseEnd_511674 : Nat := 233541955918876717174987

theorem tailTrace_511674 : CollatzResearch.WordTrace tailWord_511674 prefixEnd_511674 233541955918876717174987 := by
  unfold tailWord_511674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665570987074989951769519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12441522632199973204718717 4665570987074989951769519)
  ·
    refine ⟨6998356480612484927654279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665570987074989951769519 6998356480612484927654279)
    ·
      refine ⟨10497534720918727391481419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998356480612484927654279 10497534720918727391481419)
      ·
        refine ⟨15746302081378091087222129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497534720918727391481419 15746302081378091087222129)
        ·
          refine ⟨11809726561033568315416597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15746302081378091087222129 11809726561033568315416597)
          ·
            refine ⟨553580932548448514785153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11809726561033568315416597 553580932548448514785153)
            ·
              refine ⟨415185699411336386088865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553580932548448514785153 415185699411336386088865)
              ·
                refine ⟨311389274558502289566649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415185699411336386088865 311389274558502289566649)
                ·
                  refine ⟨233541955918876717174987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311389274558502289566649 233541955918876717174987)
                  ·
                    rfl

theorem cell20_511674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_511674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511674 prefixEnd_511674 := by exact prefixLift 511674
  have htrace : WordTrace (prefixWord ++ tailWord_511674) baseStart_511674 baseEnd_511674 := by
    simpa [prefixWord, tailWord_511674, baseEnd_511674] using wordTrace_append hprefix tailTrace_511674
  have hstable : (prefixWord ++ tailWord_511674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511674).length < 2 ^ (prefixWord ++ tailWord_511674).sum := by decide
  have hdescent : baseEnd_511674 < baseStart_511674 := by decide
  rcases family_descends (prefixWord ++ tailWord_511674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511675 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_511675 : Nat := 118140960795 + 511675 * 2 ^ 59
def prefixEnd_511675 : Nat := 4983230072969 + 3 ^ 40 * 511675 * 2
def baseEnd_511675 : Nat := 233542412346125158141649

theorem tailTrace_511675 : CollatzResearch.WordTrace tailWord_511675 prefixEnd_511675 233542412346125158141649 := by
  unfold tailWord_511675
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662320421296336977864479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12441546947530891318576319 18662320421296336977864479)
  ·
    refine ⟨27993480631944505466796719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18662320421296336977864479 27993480631944505466796719)
    ·
      refine ⟨41990220947916758200195079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993480631944505466796719 41990220947916758200195079)
      ·
        refine ⟨62985331421875137300292619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41990220947916758200195079 62985331421875137300292619)
        ·
          refine ⟨94477997132812705950438929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62985331421875137300292619 94477997132812705950438929)
          ·
            refine ⟨70858497849609529462829197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94477997132812705950438929 70858497849609529462829197)
            ·
              refine ⟨26571936693603573548560949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70858497849609529462829197 26571936693603573548560949)
              ·
                refine ⟨2491119065025335020177589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26571936693603573548560949 2491119065025335020177589)
                ·
                  refine ⟨233542412346125158141649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491119065025335020177589 233542412346125158141649)
                  ·
                    rfl

theorem cell20_511675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_511675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511675 prefixEnd_511675 := by exact prefixLift 511675
  have htrace : WordTrace (prefixWord ++ tailWord_511675) baseStart_511675 baseEnd_511675 := by
    simpa [prefixWord, tailWord_511675, baseEnd_511675] using wordTrace_append hprefix tailTrace_511675
  have hstable : (prefixWord ++ tailWord_511675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511675).length < 2 ^ (prefixWord ++ tailWord_511675).sum := by decide
  have hdescent : baseEnd_511675 < baseStart_511675 := by decide
  rcases family_descends (prefixWord ++ tailWord_511675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511730 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_511730 : Nat := 118140960795 + 511730 * 2 ^ 59
def prefixEnd_511730 : Nat := 4983230072969 + 3 ^ 40 * 511730 * 2
def baseEnd_511730 : Nat := 233567515844789411308091

theorem tailTrace_511730 : CollatzResearch.WordTrace tailWord_511730 prefixEnd_511730 233567515844789411308091 := by
  unfold tailWord_511730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666081609024270342779161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12442884290731387580744429 4666081609024270342779161)
  ·
    refine ⟨3499561206768202757084371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4666081609024270342779161 3499561206768202757084371)
    ·
      refine ⟨5249341810152304135626557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499561206768202757084371 5249341810152304135626557)
      ·
        refine ⟨1968503178807114050859959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5249341810152304135626557 1968503178807114050859959)
        ·
          refine ⟨2952754768210671076289939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968503178807114050859959 2952754768210671076289939)
          ·
            refine ⟨4429132152316006614434909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952754768210671076289939 4429132152316006614434909)
            ·
              refine ⟨1660924557118502480413091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4429132152316006614434909 1660924557118502480413091)
              ·
                refine ⟨2491386835677753720619637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660924557118502480413091 2491386835677753720619637)
                ·
                  refine ⟨233567515844789411308091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491386835677753720619637 233567515844789411308091)
                  ·
                    rfl

theorem cell20_511730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_511730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511730 prefixEnd_511730 := by exact prefixLift 511730
  have htrace : WordTrace (prefixWord ++ tailWord_511730) baseStart_511730 baseEnd_511730 := by
    simpa [prefixWord, tailWord_511730, baseEnd_511730] using wordTrace_append hprefix tailTrace_511730
  have hstable : (prefixWord ++ tailWord_511730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511730).length < 2 ^ (prefixWord ++ tailWord_511730).sum := by decide
  have hdescent : baseEnd_511730 < baseStart_511730 := by decide
  rcases family_descends (prefixWord ++ tailWord_511730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511774 : List Nat := [4, 3, 2, 2, 2, 1, 6]
def baseStart_511774 : Nat := 118140960795 + 511774 * 2 ^ 59
def prefixEnd_511774 : Nat := 4983230072969 + 3 ^ 40 * 511774 * 2
def baseEnd_511774 : Nat := 25954177627080090426805

theorem tailTrace_511774 : CollatzResearch.WordTrace tailWord_511774 prefixEnd_511774 25954177627080090426805 := by
  unfold tailWord_511774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333241405992209610714797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12443954165291784590478917 2333241405992209610714797)
  ·
    refine ⟨874965527247078604018049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2333241405992209610714797 874965527247078604018049)
    ·
      refine ⟨656224145435308953013537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874965527247078604018049 656224145435308953013537)
      ·
        refine ⟨492168109076481714760153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656224145435308953013537 492168109076481714760153)
        ·
          refine ⟨369126081807361286070115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492168109076481714760153 369126081807361286070115)
          ·
            refine ⟨553689122711041929105173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369126081807361286070115 553689122711041929105173)
            ·
              refine ⟨25954177627080090426805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553689122711041929105173 25954177627080090426805)
              ·
                rfl

theorem cell20_511774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 6].length) (baseStart_511774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511774 prefixEnd_511774 := by exact prefixLift 511774
  have htrace : WordTrace (prefixWord ++ tailWord_511774) baseStart_511774 baseEnd_511774 := by
    simpa [prefixWord, tailWord_511774, baseEnd_511774] using wordTrace_append hprefix tailTrace_511774
  have hstable : (prefixWord ++ tailWord_511774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511774).length < 2 ^ (prefixWord ++ tailWord_511774).sum := by decide
  have hdescent : baseEnd_511774 < baseStart_511774 := by decide
  rcases family_descends (prefixWord ++ tailWord_511774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511802 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_511802 : Nat := 118140960795 + 511802 * 2 ^ 59
def prefixEnd_511802 : Nat := 4983230072969 + 3 ^ 40 * 511802 * 2
def baseEnd_511802 : Nat := 233600378606677160907797

theorem tailTrace_511802 : CollatzResearch.WordTrace tailWord_511802 prefixEnd_511802 233600378606677160907797 := by
  unfold tailWord_511802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666738122959059416934415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12444634994557491778491773 4666738122959059416934415)
  ·
    refine ⟨7000107184438589125401623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666738122959059416934415 7000107184438589125401623)
    ·
      refine ⟨10500160776657883688102435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7000107184438589125401623 10500160776657883688102435)
      ·
        refine ⟨15750241164986825532153653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10500160776657883688102435 15750241164986825532153653)
        ·
          refine ⟨1476585109217514893639405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15750241164986825532153653 1476585109217514893639405)
          ·
            refine ⟨553719415956568085114777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1476585109217514893639405 553719415956568085114777)
            ·
              refine ⟨415289561967426063836083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553719415956568085114777 415289561967426063836083)
              ·
                refine ⟨622934342951139095754125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415289561967426063836083 622934342951139095754125)
                ·
                  refine ⟨233600378606677160907797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622934342951139095754125 233600378606677160907797)
                  ·
                    rfl

theorem cell20_511802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_511802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511802 prefixEnd_511802 := by exact prefixLift 511802
  have htrace : WordTrace (prefixWord ++ tailWord_511802) baseStart_511802 baseEnd_511802 := by
    simpa [prefixWord, tailWord_511802, baseEnd_511802] using wordTrace_append hprefix tailTrace_511802
  have hstable : (prefixWord ++ tailWord_511802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511802).length < 2 ^ (prefixWord ++ tailWord_511802).sum := by decide
  have hdescent : baseEnd_511802 < baseStart_511802 := by decide
  rcases family_descends (prefixWord ++ tailWord_511802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511843 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 2]
def baseStart_511843 : Nat := 118140960795 + 511843 * 2 ^ 59
def prefixEnd_511843 : Nat := 4983230072969 + 3 ^ 40 * 511843 * 2
def baseEnd_511843 : Nat := 233619092123863240540963

theorem tailTrace_511843 : CollatzResearch.WordTrace tailWord_511843 prefixEnd_511843 233619092123863240540963 := by
  unfold tailWord_511843
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668447884687701669980183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12445631923125134446653455 18668447884687701669980183)
  ·
    refine ⟨28002671827031552504970275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18668447884687701669980183 28002671827031552504970275)
    ·
      refine ⟨42004007740547328757455413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28002671827031552504970275 42004007740547328757455413)
      ·
        refine ⟨3937875725676312071011445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42004007740547328757455413 3937875725676312071011445)
        ·
          refine ⟨369175849282154256657323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3937875725676312071011445 369175849282154256657323)
          ·
            refine ⟨553763773923231384985985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369175849282154256657323 553763773923231384985985)
            ·
              refine ⟨415322830442423538739489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553763773923231384985985 415322830442423538739489)
              ·
                refine ⟨311492122831817654054617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415322830442423538739489 311492122831817654054617)
                ·
                  refine ⟨233619092123863240540963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311492122831817654054617 233619092123863240540963)
                  ·
                    rfl

theorem cell20_511843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2].length) (baseStart_511843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511843 prefixEnd_511843 := by exact prefixLift 511843
  have htrace : WordTrace (prefixWord ++ tailWord_511843) baseStart_511843 baseEnd_511843 := by
    simpa [prefixWord, tailWord_511843, baseEnd_511843] using wordTrace_append hprefix tailTrace_511843
  have hstable : (prefixWord ++ tailWord_511843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511843).length < 2 ^ (prefixWord ++ tailWord_511843).sum := by decide
  have hdescent : baseEnd_511843 < baseStart_511843 := by decide
  rcases family_descends (prefixWord ++ tailWord_511843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511854 : List Nat := [4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_511854 : Nat := 118140960795 + 511854 * 2 ^ 59
def prefixEnd_511854 : Nat := 4983230072969 + 3 ^ 40 * 511854 * 2
def baseEnd_511854 : Nat := 77874704274532030391417

theorem tailTrace_511854 : CollatzResearch.WordTrace tailWord_511854 prefixEnd_511854 77874704274532030391417 := by
  unfold tailWord_511854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333606135955981318578827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12445899391765233699087077 2333606135955981318578827)
  ·
    refine ⟨3500409203933971977868241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333606135955981318578827 3500409203933971977868241)
    ·
      refine ⟨2625306902950478983401181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500409203933971977868241 2625306902950478983401181)
      ·
        refine ⟨984490088606429618775443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2625306902950478983401181 984490088606429618775443)
        ·
          refine ⟨1476735132909644428163165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984490088606429618775443 1476735132909644428163165)
          ·
            refine ⟨553775674841116660561187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1476735132909644428163165 553775674841116660561187)
            ·
              refine ⟨830663512261674990841781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553775674841116660561187 830663512261674990841781)
              ·
                refine ⟨77874704274532030391417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830663512261674990841781 77874704274532030391417)
                ·
                  rfl

theorem cell20_511854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_511854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511854 prefixEnd_511854 := by exact prefixLift 511854
  have htrace : WordTrace (prefixWord ++ tailWord_511854) baseStart_511854 baseEnd_511854 := by
    simpa [prefixWord, tailWord_511854, baseEnd_511854] using wordTrace_append hprefix tailTrace_511854
  have hstable : (prefixWord ++ tailWord_511854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511854).length < 2 ^ (prefixWord ++ tailWord_511854).sum := by decide
  have hdescent : baseEnd_511854 < baseStart_511854 := by decide
  rcases family_descends (prefixWord ++ tailWord_511854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511875 : List Nat := [1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_511875 : Nat := 118140960795 + 511875 * 2 ^ 59
def prefixEnd_511875 : Nat := 4983230072969 + 3 ^ 40 * 511875 * 2
def baseEnd_511875 : Nat := 77877899265271117158055

theorem tailTrace_511875 : CollatzResearch.WordTrace tailWord_511875 prefixEnd_511875 77877899265271117158055 := by
  unfold tailWord_511875
  simp only [CollatzResearch.WordTrace]
  refine ⟨18669615020571771135145079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12446410013714514090096719 18669615020571771135145079)
  ·
    refine ⟨28004422530857656702717619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18669615020571771135145079 28004422530857656702717619)
    ·
      refine ⟨42006633796286485054076429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28004422530857656702717619 42006633796286485054076429)
      ·
        refine ⟨15752487673607431895278661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42006633796286485054076429 15752487673607431895278661)
        ·
          refine ⟨2953591438801393480364749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15752487673607431895278661 2953591438801393480364749)
          ·
            refine ⟨1107596789550522555136781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2953591438801393480364749 1107596789550522555136781)
            ·
              refine ⟨415348796081445958176293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1107596789550522555136781 415348796081445958176293)
              ·
                refine ⟨77877899265271117158055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415348796081445958176293 77877899265271117158055)
                ·
                  rfl

theorem cell20_511875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_511875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511875 prefixEnd_511875 := by exact prefixLift 511875
  have htrace : WordTrace (prefixWord ++ tailWord_511875) baseStart_511875 baseEnd_511875 := by
    simpa [prefixWord, tailWord_511875, baseEnd_511875] using wordTrace_append hprefix tailTrace_511875
  have hstable : (prefixWord ++ tailWord_511875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511875).length < 2 ^ (prefixWord ++ tailWord_511875).sum := by decide
  have hdescent : baseEnd_511875 < baseStart_511875 := by decide
  rcases family_descends (prefixWord ++ tailWord_511875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511902 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_511902 : Nat := 118140960795 + 511902 * 2 ^ 59
def prefixEnd_511902 : Nat := 4983230072969 + 3 ^ 40 * 511902 * 2
def baseEnd_511902 : Nat := 233646021331521257574055

theorem tailTrace_511902 : CollatzResearch.WordTrace tailWord_511902 prefixEnd_511902 233646021331521257574055 := by
  unfold tailWord_511902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333824973934244343297245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12447066527649303164251973 2333824973934244343297245)
  ·
    refine ⟨875184365225341628736467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2333824973934244343297245 875184365225341628736467)
    ·
      refine ⟨1312776547838012443104701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875184365225341628736467 1312776547838012443104701)
      ·
        refine ⟨492291205439254666164263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1312776547838012443104701 492291205439254666164263)
        ·
          refine ⟨738436808158881999246395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492291205439254666164263 738436808158881999246395)
          ·
            refine ⟨1107655212238322998869593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738436808158881999246395 1107655212238322998869593)
            ·
              refine ⟨830741409178742249152195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107655212238322998869593 830741409178742249152195)
              ·
                refine ⟨1246112113768113373728293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830741409178742249152195 1246112113768113373728293)
                ·
                  refine ⟨233646021331521257574055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246112113768113373728293 233646021331521257574055)
                  ·
                    rfl

theorem cell20_511902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_511902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511902 prefixEnd_511902 := by exact prefixLift 511902
  have htrace : WordTrace (prefixWord ++ tailWord_511902) baseStart_511902 baseEnd_511902 := by
    simpa [prefixWord, tailWord_511902, baseEnd_511902] using wordTrace_append hprefix tailTrace_511902
  have hstable : (prefixWord ++ tailWord_511902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511902).length < 2 ^ (prefixWord ++ tailWord_511902).sum := by decide
  have hdescent : baseEnd_511902 < baseStart_511902 := by decide
  rcases family_descends (prefixWord ++ tailWord_511902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511961 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 4]
def baseStart_511961 : Nat := 118140960795 + 511961 * 2 ^ 59
def prefixEnd_511961 : Nat := 4983230072969 + 3 ^ 40 * 511961 * 2
def baseEnd_511961 : Nat := 233672950539179274607147

theorem tailTrace_511961 : CollatzResearch.WordTrace tailWord_511961 prefixEnd_511961 233672950539179274607147 := by
  unfold tailWord_511961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672751698260207822775737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12448501132173471881850491 18672751698260207822775737)
  ·
    refine ⟨14004563773695155867081803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18672751698260207822775737 14004563773695155867081803)
    ·
      refine ⟨21006845660542733800622705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14004563773695155867081803 21006845660542733800622705)
      ·
        refine ⟨15755134245407050350467029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21006845660542733800622705 15755134245407050350467029)
        ·
          refine ⟨369260958876727742589071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15755134245407050350467029 369260958876727742589071)
          ·
            refine ⟨553891438315091613883607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369260958876727742589071 553891438315091613883607)
            ·
              refine ⟨830837157472637420825411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553891438315091613883607 830837157472637420825411)
              ·
                refine ⟨1246255736208956131238117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830837157472637420825411 1246255736208956131238117)
                ·
                  refine ⟨233672950539179274607147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246255736208956131238117 233672950539179274607147)
                  ·
                    rfl

theorem cell20_511961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_511961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511961 prefixEnd_511961 := by exact prefixLift 511961
  have htrace : WordTrace (prefixWord ++ tailWord_511961) baseStart_511961 baseEnd_511961 := by
    simpa [prefixWord, tailWord_511961, baseEnd_511961] using wordTrace_append hprefix tailTrace_511961
  have hstable : (prefixWord ++ tailWord_511961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511961).length < 2 ^ (prefixWord ++ tailWord_511961).sum := by decide
  have hdescent : baseEnd_511961 < baseStart_511961 := by decide
  rcases family_descends (prefixWord ++ tailWord_511961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511972 : List Nat := [2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_511972 : Nat := 118140960795 + 511972 * 2 ^ 59
def prefixEnd_511972 : Nat := 4983230072969 + 3 ^ 40 * 511972 * 2
def baseEnd_511972 : Nat := 77892657079637375080145

theorem tailTrace_511972 : CollatzResearch.WordTrace tailWord_511972 prefixEnd_511972 77892657079637375080145 := by
  unfold tailWord_511972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336576450610178350713085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12448768600813571134284113 9336576450610178350713085)
  ·
    refine ⟨3501216168978816881517407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9336576450610178350713085 3501216168978816881517407)
    ·
      refine ⟨5251824253468225322276111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501216168978816881517407 5251824253468225322276111)
      ·
        refine ⟨7877736380202337983414167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251824253468225322276111 7877736380202337983414167)
        ·
          refine ⟨11816604570303506975121251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877736380202337983414167 11816604570303506975121251)
          ·
            refine ⟨17724906855455260462681877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816604570303506975121251 17724906855455260462681877)
            ·
              refine ⟨830855008849465334188213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17724906855455260462681877 830855008849465334188213)
              ·
                refine ⟨77892657079637375080145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830855008849465334188213 77892657079637375080145)
                ·
                  rfl

theorem cell20_511972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_511972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511972 prefixEnd_511972 := by exact prefixLift 511972
  have htrace : WordTrace (prefixWord ++ tailWord_511972) baseStart_511972 baseEnd_511972 := by
    simpa [prefixWord, tailWord_511972, baseEnd_511972] using wordTrace_append hprefix tailTrace_511972
  have hstable : (prefixWord ++ tailWord_511972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511972).length < 2 ^ (prefixWord ++ tailWord_511972).sum := by decide
  have hdescent : baseEnd_511972 < baseStart_511972 := by decide
  rcases family_descends (prefixWord ++ tailWord_511972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511975 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_511975 : Nat := 118140960795 + 511975 * 2 ^ 59
def prefixEnd_511975 : Nat := 4983230072969 + 3 ^ 40 * 511975 * 2
def baseEnd_511975 : Nat := 233679340520657448140423

theorem tailTrace_511975 : CollatzResearch.WordTrace tailWord_511975 prefixEnd_511975 233679340520657448140423 := by
  unfold tailWord_511975
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673262320209488213785379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12448841546806325475856919 18673262320209488213785379)
  ·
    refine ⟨28009893480314232320678069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673262320209488213785379 28009893480314232320678069)
    ·
      refine ⟨2625927513779459280063569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28009893480314232320678069 2625927513779459280063569)
      ·
        refine ⟨1969445635334594460047677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625927513779459280063569 1969445635334594460047677)
        ·
          refine ⟨738542113250472922517879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1969445635334594460047677 738542113250472922517879)
          ·
            refine ⟨1107813169875709383776819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738542113250472922517879 1107813169875709383776819)
            ·
              refine ⟨1661719754813564075665229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107813169875709383776819 1661719754813564075665229)
              ·
                refine ⟨623144908055086528374461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661719754813564075665229 623144908055086528374461)
                ·
                  refine ⟨233679340520657448140423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623144908055086528374461 233679340520657448140423)
                  ·
                    rfl

theorem cell20_511975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_511975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511975 prefixEnd_511975 := by exact prefixLift 511975
  have htrace : WordTrace (prefixWord ++ tailWord_511975) baseStart_511975 baseEnd_511975 := by
    simpa [prefixWord, tailWord_511975, baseEnd_511975] using wordTrace_append hprefix tailTrace_511975
  have hstable : (prefixWord ++ tailWord_511975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511975).length < 2 ^ (prefixWord ++ tailWord_511975).sum := by decide
  have hdescent : baseEnd_511975 < baseStart_511975 := by decide
  rcases family_descends (prefixWord ++ tailWord_511975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512010 : List Nat := [3, 1, 2, 2, 4, 8]
def baseStart_512010 : Nat := 118140960795 + 512010 * 2 ^ 59
def prefixEnd_512010 : Nat := 4983230072969 + 3 ^ 40 * 512010 * 2
def baseEnd_512010 : Nat := 8655382054605662295319

theorem tailTrace_512010 : CollatzResearch.WordTrace tailWord_512010 prefixEnd_512010 8655382054605662295319 := by
  unfold tailWord_512010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668634718770672297827371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12449692583388459460872989 4668634718770672297827371)
  ·
    refine ⟨7002952078156008446741057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4668634718770672297827371 7002952078156008446741057)
    ·
      refine ⟨5252214058617006335055793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7002952078156008446741057 5252214058617006335055793)
      ·
        refine ⟨3939160543962754751291845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5252214058617006335055793 3939160543962754751291845)
        ·
          refine ⟨738592601993016515867221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3939160543962754751291845 738592601993016515867221)
          ·
            refine ⟨8655382054605662295319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 738592601993016515867221 8655382054605662295319)
            ·
              rfl

theorem cell20_512010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 8].length) (baseStart_512010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512010 prefixEnd_512010 := by exact prefixLift 512010
  have htrace : WordTrace (prefixWord ++ tailWord_512010) baseStart_512010 baseEnd_512010 := by
    simpa [prefixWord, tailWord_512010, baseEnd_512010] using wordTrace_append hprefix tailTrace_512010
  have hstable : (prefixWord ++ tailWord_512010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512010).length < 2 ^ (prefixWord ++ tailWord_512010).sum := by decide
  have hdescent : baseEnd_512010 < baseStart_512010 := by decide
  rcases family_descends (prefixWord ++ tailWord_512010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512034 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_512034 : Nat := 118140960795 + 512034 * 2 ^ 59
def prefixEnd_512034 : Nat := 4983230072969 + 3 ^ 40 * 512034 * 2
def baseEnd_512034 : Nat := 233706269728315465173515

theorem tailTrace_512034 : CollatzResearch.WordTrace tailWord_512034 prefixEnd_512034 233706269728315465173515 := by
  unfold tailWord_512034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668853556748935322545789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12450276151330494193455437 4668853556748935322545789)
  ·
    refine ⟨1750820083780850745954671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4668853556748935322545789 1750820083780850745954671)
    ·
      refine ⟨2626230125671276118932007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750820083780850745954671 2626230125671276118932007)
      ·
        refine ⟨3939345188506914178398011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626230125671276118932007 3939345188506914178398011)
        ·
          refine ⟨5909017782760371267597017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939345188506914178398011 5909017782760371267597017)
          ·
            refine ⟨4431763337070278450697763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5909017782760371267597017 4431763337070278450697763)
            ·
              refine ⟨6647645005605417676046645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431763337070278450697763 6647645005605417676046645)
              ·
                refine ⟨623216719275507907129373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6647645005605417676046645 623216719275507907129373)
                ·
                  refine ⟨233706269728315465173515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623216719275507907129373 233706269728315465173515)
                  ·
                    rfl

theorem cell20_512034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_512034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512034 prefixEnd_512034 := by exact prefixLift 512034
  have htrace : WordTrace (prefixWord ++ tailWord_512034) baseStart_512034 baseEnd_512034 := by
    simpa [prefixWord, tailWord_512034, baseEnd_512034] using wordTrace_append hprefix tailTrace_512034
  have hstable : (prefixWord ++ tailWord_512034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512034).length < 2 ^ (prefixWord ++ tailWord_512034).sum := by decide
  have hdescent : baseEnd_512034 < baseStart_512034 := by decide
  rcases family_descends (prefixWord ++ tailWord_512034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512124 : List Nat := [2, 2, 2, 1, 1, 6, 6]
def baseStart_512124 : Nat := 118140960795 + 512124 * 2 ^ 59
def prefixEnd_512124 : Nat := 4983230072969 + 3 ^ 40 * 512124 * 2
def baseEnd_512124 : Nat := 25971927575630572463683

theorem tailTrace_512124 : CollatzResearch.WordTrace tailWord_512124 prefixEnd_512124 25971927575630572463683 := by
  unfold tailWord_512124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9339348398334843330479713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12452464531113124440639617 9339348398334843330479713)
  ·
    refine ⟨7004511298751132497859785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9339348398334843330479713 7004511298751132497859785)
    ·
      refine ⟨5253383474063349373394839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7004511298751132497859785 5253383474063349373394839)
      ·
        refine ⟨7880075211095024060092259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253383474063349373394839 7880075211095024060092259)
        ·
          refine ⟨11820112816642536090138389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7880075211095024060092259 11820112816642536090138389)
          ·
            refine ⟨554067788280118879225237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11820112816642536090138389 554067788280118879225237)
            ·
              refine ⟨25971927575630572463683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554067788280118879225237 25971927575630572463683)
              ·
                rfl

theorem cell20_512124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_512124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512124 prefixEnd_512124 := by exact prefixLift 512124
  have htrace : WordTrace (prefixWord ++ tailWord_512124) baseStart_512124 baseEnd_512124 := by
    simpa [prefixWord, tailWord_512124, baseEnd_512124] using wordTrace_append hprefix tailTrace_512124
  have hstable : (prefixWord ++ tailWord_512124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512124).length < 2 ^ (prefixWord ++ tailWord_512124).sum := by decide
  have hdescent : baseEnd_512124 < baseStart_512124 := by decide
  rcases family_descends (prefixWord ++ tailWord_512124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512131 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_512131 : Nat := 118140960795 + 512131 * 2 ^ 59
def prefixEnd_512131 : Nat := 4983230072969 + 3 ^ 40 * 512131 * 2
def baseEnd_512131 : Nat := 233750543171414238939785

theorem tailTrace_512131 : CollatzResearch.WordTrace tailWord_512131 prefixEnd_512131 233750543171414238939785 := by
  unfold tailWord_512131
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678952107644326856464247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12452634738429551237642831 18678952107644326856464247)
  ·
    refine ⟨28018428161466490284696371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18678952107644326856464247 28018428161466490284696371)
    ·
      refine ⟨42027642242199735427044557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28018428161466490284696371 42027642242199735427044557)
      ·
        refine ⟨15760365840824900785141709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42027642242199735427044557 15760365840824900785141709)
        ·
          refine ⟨5910137190309337794428141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15760365840824900785141709 5910137190309337794428141)
          ·
            refine ⟨2216301446366001672910553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5910137190309337794428141 2216301446366001672910553)
            ·
              refine ⟨1662226084774501254682915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216301446366001672910553 1662226084774501254682915)
              ·
                refine ⟨2493339127161751882024373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662226084774501254682915 2493339127161751882024373)
                ·
                  refine ⟨233750543171414238939785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493339127161751882024373 233750543171414238939785)
                  ·
                    rfl

theorem cell20_512131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_512131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512131 prefixEnd_512131 := by exact prefixLift 512131
  have htrace : WordTrace (prefixWord ++ tailWord_512131) baseStart_512131 baseEnd_512131 := by
    simpa [prefixWord, tailWord_512131, baseEnd_512131] using wordTrace_append hprefix tailTrace_512131
  have hstable : (prefixWord ++ tailWord_512131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512131).length < 2 ^ (prefixWord ++ tailWord_512131).sum := by decide
  have hdescent : baseEnd_512131 < baseStart_512131 := by decide
  rcases family_descends (prefixWord ++ tailWord_512131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512183 : List Nat := [1, 1, 3, 1, 4, 10]
def baseStart_512183 : Nat := 118140960795 + 512183 * 2 ^ 59
def prefixEnd_512183 : Nat := 4983230072969 + 3 ^ 40 * 512183 * 2
def baseEnd_512183 : Nat := 8658306569938265526157

theorem tailTrace_512183 : CollatzResearch.WordTrace tailWord_512183 prefixEnd_512183 8658306569938265526157 := by
  unfold tailWord_512183
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680848703455939737357203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12453899135637293158238135 18680848703455939737357203)
  ·
    refine ⟨28021273055183909606035805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680848703455939737357203 28021273055183909606035805)
    ·
      refine ⟨10507977395693966102263427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28021273055183909606035805 10507977395693966102263427)
      ·
        refine ⟨15761966093540949153395141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10507977395693966102263427 15761966093540949153395141)
        ·
          refine ⟨2955368642538927966261589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15761966093540949153395141 2955368642538927966261589)
          ·
            refine ⟨8658306569938265526157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2955368642538927966261589 8658306569938265526157)
            ·
              rfl

theorem cell20_512183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 10].length) (baseStart_512183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512183 prefixEnd_512183 := by exact prefixLift 512183
  have htrace : WordTrace (prefixWord ++ tailWord_512183) baseStart_512183 baseEnd_512183 := by
    simpa [prefixWord, tailWord_512183, baseEnd_512183] using wordTrace_append hprefix tailTrace_512183
  have hstable : (prefixWord ++ tailWord_512183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512183).length < 2 ^ (prefixWord ++ tailWord_512183).sum := by decide
  have hdescent : baseEnd_512183 < baseStart_512183 := by decide
  rcases family_descends (prefixWord ++ tailWord_512183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512207 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_512207 : Nat := 118140960795 + 512207 * 2 ^ 59
def prefixEnd_512207 : Nat := 4983230072969 + 3 ^ 40 * 512207 * 2
def baseEnd_512207 : Nat := 233785231642295752406141

theorem tailTrace_512207 : CollatzResearch.WordTrace tailWord_512207 prefixEnd_512207 233785231642295752406141 := by
  unfold tailWord_512207
  simp only [CollatzResearch.WordTrace]
  refine ⟨18681724055368991836230875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12454482703579327890820583 18681724055368991836230875)
  ·
    refine ⟨28022586083053487754346313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18681724055368991836230875 28022586083053487754346313)
    ·
      refine ⟨21016939562290115815759735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28022586083053487754346313 21016939562290115815759735)
      ·
        refine ⟨31525409343435173723639603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21016939562290115815759735 31525409343435173723639603)
        ·
          refine ⟨47288114015152760585459405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31525409343435173723639603 47288114015152760585459405)
          ·
            refine ⟨17733042755682285219547277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47288114015152760585459405 17733042755682285219547277)
            ·
              refine ⟨6649891033380856957330229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17733042755682285219547277 6649891033380856957330229)
              ·
                refine ⟨623427284379455339749709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6649891033380856957330229 623427284379455339749709)
                ·
                  refine ⟨233785231642295752406141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623427284379455339749709 233785231642295752406141)
                  ·
                    rfl

theorem cell20_512207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_512207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512207 prefixEnd_512207 := by exact prefixLift 512207
  have htrace : WordTrace (prefixWord ++ tailWord_512207) baseStart_512207 baseEnd_512207 := by
    simpa [prefixWord, tailWord_512207, baseEnd_512207] using wordTrace_append hprefix tailTrace_512207
  have hstable : (prefixWord ++ tailWord_512207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512207).length < 2 ^ (prefixWord ++ tailWord_512207).sum := by decide
  have hdescent : baseEnd_512207 < baseStart_512207 := by decide
  rcases family_descends (prefixWord ++ tailWord_512207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512258 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_512258 : Nat := 118140960795 + 512258 * 2 ^ 59
def prefixEnd_512258 : Nat := 4983230072969 + 3 ^ 40 * 512258 * 2
def baseEnd_512258 : Nat := 233808509431966241705933

theorem tailTrace_512258 : CollatzResearch.WordTrace tailWord_512258 prefixEnd_512258 233808509431966241705933 := by
  unfold tailWord_512258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670896044546056886584357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12455722785456151697558285 4670896044546056886584357)
  ·
    refine ⟨875793008352385666234567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4670896044546056886584357 875793008352385666234567)
    ·
      refine ⟨1313689512528578499351851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875793008352385666234567 1313689512528578499351851)
      ·
        refine ⟨1970534268792867749027777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313689512528578499351851 1970534268792867749027777)
        ·
          refine ⟨1477900701594650811770833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970534268792867749027777 1477900701594650811770833)
          ·
            refine ⟨1108425526195988108828125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477900701594650811770833 1108425526195988108828125)
            ·
              refine ⟨415659572323495540810547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108425526195988108828125 415659572323495540810547)
              ·
                refine ⟨623489358485243311215821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415659572323495540810547 623489358485243311215821)
                ·
                  refine ⟨233808509431966241705933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623489358485243311215821 233808509431966241705933)
                  ·
                    rfl

theorem cell20_512258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_512258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512258 prefixEnd_512258 := by exact prefixLift 512258
  have htrace : WordTrace (prefixWord ++ tailWord_512258) baseStart_512258 baseEnd_512258 := by
    simpa [prefixWord, tailWord_512258, baseEnd_512258] using wordTrace_append hprefix tailTrace_512258
  have hstable : (prefixWord ++ tailWord_512258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512258).length < 2 ^ (prefixWord ++ tailWord_512258).sum := by decide
  have hdescent : baseEnd_512258 < baseStart_512258 := by decide
  rcases family_descends (prefixWord ++ tailWord_512258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512259 : List Nat := [1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_512259 : Nat := 118140960795 + 512259 * 2 ^ 59
def prefixEnd_512259 : Nat := 4983230072969 + 3 ^ 40 * 512259 * 2
def baseEnd_512259 : Nat := 77936321953071560890865

theorem tailTrace_512259 : CollatzResearch.WordTrace tailWord_512259 prefixEnd_512259 77936321953071560890865 := by
  unfold tailWord_512259
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683620651180604717123831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12455747100787069811415887 18683620651180604717123831)
  ·
    refine ⟨28025430976770907075685747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18683620651180604717123831 28025430976770907075685747)
    ·
      refine ⟨42038146465156360613528621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28025430976770907075685747 42038146465156360613528621)
      ·
        refine ⟨15764304924433635230073233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42038146465156360613528621 15764304924433635230073233)
        ·
          refine ⟨11823228693325226422554925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15764304924433635230073233 11823228693325226422554925)
          ·
            refine ⟨4433710759996959908458097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11823228693325226422554925 4433710759996959908458097)
            ·
              refine ⟨3325283069997719931343573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433710759996959908458097 3325283069997719931343573)
              ·
                refine ⟨77936321953071560890865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3325283069997719931343573 77936321953071560890865)
                ·
                  rfl

theorem cell20_512259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_512259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512259 prefixEnd_512259 := by exact prefixLift 512259
  have htrace : WordTrace (prefixWord ++ tailWord_512259) baseStart_512259 baseEnd_512259 := by
    simpa [prefixWord, tailWord_512259, baseEnd_512259] using wordTrace_append hprefix tailTrace_512259
  have hstable : (prefixWord ++ tailWord_512259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512259).length < 2 ^ (prefixWord ++ tailWord_512259).sum := by decide
  have hdescent : baseEnd_512259 < baseStart_512259 := by decide
  rcases family_descends (prefixWord ++ tailWord_512259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512282 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_512282 : Nat := 118140960795 + 512282 * 2 ^ 59
def prefixEnd_512282 : Nat := 4983230072969 + 3 ^ 40 * 512282 * 2
def baseEnd_512282 : Nat := 233819463685928824905835

theorem tailTrace_512282 : CollatzResearch.WordTrace tailWord_512282 prefixEnd_512282 233819463685928824905835 := by
  unfold tailWord_512282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671114882524319911302775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12456306353398186430140733 4671114882524319911302775)
  ·
    refine ⟨7006672323786479866954163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4671114882524319911302775 7006672323786479866954163)
    ·
      refine ⟨10510008485679719800431245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006672323786479866954163 10510008485679719800431245)
      ·
        refine ⟨3941253182129894925161717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10510008485679719800431245 3941253182129894925161717)
        ·
          refine ⟨369492485824677649233911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3941253182129894925161717 369492485824677649233911)
          ·
            refine ⟨554238728737016473850867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369492485824677649233911 554238728737016473850867)
            ·
              refine ⟨831358093105524710776301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554238728737016473850867 831358093105524710776301)
              ·
                refine ⟨311759284914571766541113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831358093105524710776301 311759284914571766541113)
                ·
                  refine ⟨233819463685928824905835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311759284914571766541113 233819463685928824905835)
                  ·
                    rfl

theorem cell20_512282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_512282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512282 prefixEnd_512282 := by exact prefixLift 512282
  have htrace : WordTrace (prefixWord ++ tailWord_512282) baseStart_512282 baseEnd_512282 := by
    simpa [prefixWord, tailWord_512282, baseEnd_512282] using wordTrace_append hprefix tailTrace_512282
  have hstable : (prefixWord ++ tailWord_512282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512282).length < 2 ^ (prefixWord ++ tailWord_512282).sum := by decide
  have hdescent : baseEnd_512282 < baseStart_512282 := by decide
  rcases family_descends (prefixWord ++ tailWord_512282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512293 : List Nat := [1, 3, 1, 2, 6, 1, 6]
def baseStart_512293 : Nat := 118140960795 + 512293 * 2 ^ 59
def prefixEnd_512293 : Nat := 4983230072969 + 3 ^ 40 * 512293 * 2
def baseEnd_512293 : Nat := 25980498265073519504347

theorem tailTrace_512293 : CollatzResearch.WordTrace tailWord_512293 prefixEnd_512293 25980498265073519504347 := by
  unfold tailWord_512293
  simp only [CollatzResearch.WordTrace]
  refine ⟨18684860733057428523861533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12456573822038285682574355 18684860733057428523861533)
  ·
    refine ⟨7006822774896535696448075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18684860733057428523861533 7006822774896535696448075)
    ·
      refine ⟨10510234162344803544672113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006822774896535696448075 10510234162344803544672113)
      ·
        refine ⟨7882675621758602658504085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10510234162344803544672113 7882675621758602658504085)
        ·
          refine ⟨369500419769934499617379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7882675621758602658504085 369500419769934499617379)
          ·
            refine ⟨554250629654901749426069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369500419769934499617379 554250629654901749426069)
            ·
              refine ⟨25980498265073519504347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554250629654901749426069 25980498265073519504347)
              ·
                rfl

theorem cell20_512293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 6].length) (baseStart_512293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512293 prefixEnd_512293 := by exact prefixLift 512293
  have htrace : WordTrace (prefixWord ++ tailWord_512293) baseStart_512293 baseEnd_512293 := by
    simpa [prefixWord, tailWord_512293, baseEnd_512293] using wordTrace_append hprefix tailTrace_512293
  have hstable : (prefixWord ++ tailWord_512293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512293).length < 2 ^ (prefixWord ++ tailWord_512293).sum := by decide
  have hdescent : baseEnd_512293 < baseStart_512293 := by decide
  rcases family_descends (prefixWord ++ tailWord_512293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512314 : List Nat := [3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_512314 : Nat := 118140960795 + 512314 * 2 ^ 59
def prefixEnd_512314 : Nat := 4983230072969 + 3 ^ 40 * 512314 * 2
def baseEnd_512314 : Nat := 77944689785959645279679

theorem tailTrace_512314 : CollatzResearch.WordTrace tailWord_512314 prefixEnd_512314 77944689785959645279679 := by
  unfold tailWord_512314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671406666495337277593999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12457084443987566073583997 4671406666495337277593999)
  ·
    refine ⟨7007109999743005916390999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4671406666495337277593999 7007109999743005916390999)
    ·
      refine ⟨10510664999614508874586499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007109999743005916390999 10510664999614508874586499)
      ·
        refine ⟨15765997499421763311879749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10510664999614508874586499 15765997499421763311879749)
        ·
          refine ⟨2956124531141580620977453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15765997499421763311879749 2956124531141580620977453)
          ·
            refine ⟨1108546699178092732866545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2956124531141580620977453 1108546699178092732866545)
            ·
              refine ⟨831410024383569549649909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108546699178092732866545 831410024383569549649909)
              ·
                refine ⟨77944689785959645279679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 831410024383569549649909 77944689785959645279679)
                ·
                  rfl

theorem cell20_512314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_512314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512314 prefixEnd_512314 := by exact prefixLift 512314
  have htrace : WordTrace (prefixWord ++ tailWord_512314) baseStart_512314 baseEnd_512314 := by
    simpa [prefixWord, tailWord_512314, baseEnd_512314] using wordTrace_append hprefix tailTrace_512314
  have hstable : (prefixWord ++ tailWord_512314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512314).length < 2 ^ (prefixWord ++ tailWord_512314).sum := by decide
  have hdescent : baseEnd_512314 < baseStart_512314 := by decide
  rcases family_descends (prefixWord ++ tailWord_512314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512328 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_512328 : Nat := 118140960795 + 512328 * 2 ^ 59
def prefixEnd_512328 : Nat := 4983230072969 + 3 ^ 40 * 512328 * 2
def baseEnd_512328 : Nat := 233840459339357109372313

theorem tailTrace_512328 : CollatzResearch.WordTrace tailWord_512328 prefixEnd_512328 233840459339357109372313 := by
  unfold tailWord_512328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343068643965314750692819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12457424858620419667590425 9343068643965314750692819)
  ·
    refine ⟨14014602965947972126039229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9343068643965314750692819 14014602965947972126039229)
    ·
      refine ⟨5255476112230489547264711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14014602965947972126039229 5255476112230489547264711)
      ·
        refine ⟨7883214168345734320897067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255476112230489547264711 7883214168345734320897067)
        ·
          refine ⟨11824821252518601481345601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883214168345734320897067 11824821252518601481345601)
          ·
            refine ⟨8868615939388951111009201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11824821252518601481345601 8868615939388951111009201)
            ·
              refine ⟨6651461954541713333256901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868615939388951111009201 6651461954541713333256901)
              ·
                refine ⟨1247149116476571249985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651461954541713333256901 1247149116476571249985669)
                ·
                  refine ⟨233840459339357109372313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1247149116476571249985669 233840459339357109372313)
                  ·
                    rfl

theorem cell20_512328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_512328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512328 prefixEnd_512328 := by exact prefixLift 512328
  have htrace : WordTrace (prefixWord ++ tailWord_512328) baseStart_512328 baseEnd_512328 := by
    simpa [prefixWord, tailWord_512328, baseEnd_512328] using wordTrace_append hprefix tailTrace_512328
  have hstable : (prefixWord ++ tailWord_512328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512328).length < 2 ^ (prefixWord ++ tailWord_512328).sum := by decide
  have hdescent : baseEnd_512328 < baseStart_512328 := by decide
  rcases family_descends (prefixWord ++ tailWord_512328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512345 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 2]
def baseStart_512345 : Nat := 118140960795 + 512345 * 2 ^ 59
def prefixEnd_512345 : Nat := 4983230072969 + 3 ^ 40 * 512345 * 2
def baseEnd_512345 : Nat := 233848218602580605805577

theorem tailTrace_512345 : CollatzResearch.WordTrace tailWord_512345 prefixEnd_512345 233848218602580605805577 := by
  unfold tailWord_512345
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686757328869041404754489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12457838219246027603169659 18686757328869041404754489)
  ·
    refine ⟨14015067996651781053565867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18686757328869041404754489 14015067996651781053565867)
    ·
      refine ⟨21022601994977671580348801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015067996651781053565867 21022601994977671580348801)
      ·
        refine ⟨15766951496233253685261601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21022601994977671580348801 15766951496233253685261601)
        ·
          refine ⟨11825213622174940263946201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15766951496233253685261601 11825213622174940263946201)
          ·
            refine ⟨8868910216631205197959651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11825213622174940263946201 8868910216631205197959651)
            ·
              refine ⟨13303365324946807796939477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868910216631205197959651 13303365324946807796939477)
              ·
                refine ⟨311797624803440807740769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13303365324946807796939477 311797624803440807740769)
                ·
                  refine ⟨233848218602580605805577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311797624803440807740769 233848218602580605805577)
                  ·
                    rfl

theorem cell20_512345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_512345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512345 prefixEnd_512345 := by exact prefixLift 512345
  have htrace : WordTrace (prefixWord ++ tailWord_512345) baseStart_512345 baseEnd_512345 := by
    simpa [prefixWord, tailWord_512345, baseEnd_512345] using wordTrace_append hprefix tailTrace_512345
  have hstable : (prefixWord ++ tailWord_512345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512345).length < 2 ^ (prefixWord ++ tailWord_512345).sum := by decide
  have hdescent : baseEnd_512345 < baseStart_512345 := by decide
  rcases family_descends (prefixWord ++ tailWord_512345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512350 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_512350 : Nat := 118140960795 + 512350 * 2 ^ 59
def prefixEnd_512350 : Nat := 4983230072969 + 3 ^ 40 * 512350 * 2
def baseEnd_512350 : Nat := 233850500738822810638891

theorem tailTrace_512350 : CollatzResearch.WordTrace tailWord_512350 prefixEnd_512350 233850500738822810638891 := by
  unfold tailWord_512350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335867461731365907335813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12457959795900618172457669 2335867461731365907335813)
  ·
    refine ⟨437975149074631107625465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2335867461731365907335813 437975149074631107625465)
    ·
      refine ⟨328481361805973330719099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437975149074631107625465 328481361805973330719099)
      ·
        refine ⟨492722042708959996078649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328481361805973330719099 492722042708959996078649)
        ·
          refine ⟨369541532031719997058987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492722042708959996078649 369541532031719997058987)
          ·
            refine ⟨554312298047579995588481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369541532031719997058987 554312298047579995588481)
            ·
              refine ⟨415734223535684996691361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554312298047579995588481 415734223535684996691361)
              ·
                refine ⟨311800667651763747518521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415734223535684996691361 311800667651763747518521)
                ·
                  refine ⟨233850500738822810638891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311800667651763747518521 233850500738822810638891)
                  ·
                    rfl

theorem cell20_512350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_512350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512350 prefixEnd_512350 := by exact prefixLift 512350
  have htrace : WordTrace (prefixWord ++ tailWord_512350) baseStart_512350 baseEnd_512350 := by
    simpa [prefixWord, tailWord_512350, baseEnd_512350] using wordTrace_append hprefix tailTrace_512350
  have hstable : (prefixWord ++ tailWord_512350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512350).length < 2 ^ (prefixWord ++ tailWord_512350).sum := by decide
  have hdescent : baseEnd_512350 < baseStart_512350 := by decide
  rcases family_descends (prefixWord ++ tailWord_512350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512352 : List Nat := [2, 1, 1, 3, 6, 7]
def baseStart_512352 : Nat := 118140960795 + 512352 * 2 ^ 59
def prefixEnd_512352 : Nat := 4983230072969 + 3 ^ 40 * 512352 * 2
def baseEnd_512352 : Nat := 8661163466419247873045

theorem tailTrace_512352 : CollatzResearch.WordTrace tailWord_512352 prefixEnd_512352 8661163466419247873045 := by
  unfold tailWord_512352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343506319921840800129655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12458008426562454400172873 9343506319921840800129655)
  ·
    refine ⟨14015259479882761200194483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9343506319921840800129655 14015259479882761200194483)
    ·
      refine ⟨21022889219824141800291725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015259479882761200194483 21022889219824141800291725)
      ·
        refine ⟨7883583457434053175109397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21022889219824141800291725 7883583457434053175109397)
        ·
          refine ⟨369542974567221242583253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7883583457434053175109397 369542974567221242583253)
          ·
            refine ⟨8661163466419247873045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 369542974567221242583253 8661163466419247873045)
            ·
              rfl

theorem cell20_512352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 7].length) (baseStart_512352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512352 prefixEnd_512352 := by exact prefixLift 512352
  have htrace : WordTrace (prefixWord ++ tailWord_512352) baseStart_512352 baseEnd_512352 := by
    simpa [prefixWord, tailWord_512352, baseEnd_512352] using wordTrace_append hprefix tailTrace_512352
  have hstable : (prefixWord ++ tailWord_512352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512352).length < 2 ^ (prefixWord ++ tailWord_512352).sum := by decide
  have hdescent : baseEnd_512352 < baseStart_512352 := by decide
  rcases family_descends (prefixWord ++ tailWord_512352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512406 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_512406 : Nat := 118140960795 + 512406 * 2 ^ 59
def prefixEnd_512406 : Nat := 4983230072969 + 3 ^ 40 * 512406 * 2
def baseEnd_512406 : Nat := 233876060664735504771995

theorem tailTrace_512406 : CollatzResearch.WordTrace tailWord_512406 prefixEnd_512406 233876060664735504771995 := by
  unfold tailWord_512406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168061386353003051420317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12459321454432032548483381 1168061386353003051420317)
  ·
    refine ⟨438023019882376144282619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1168061386353003051420317 438023019882376144282619)
    ·
      refine ⟨657034529823564216423929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438023019882376144282619 657034529823564216423929)
      ·
        refine ⟨492775897367673162317947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657034529823564216423929 492775897367673162317947)
        ·
          refine ⟨739163846051509743476921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492775897367673162317947 739163846051509743476921)
          ·
            refine ⟨554372884538632307607691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739163846051509743476921 554372884538632307607691)
            ·
              refine ⟨831559326807948461411537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554372884538632307607691 831559326807948461411537)
              ·
                refine ⟨623669495105961346058653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831559326807948461411537 623669495105961346058653)
                ·
                  refine ⟨233876060664735504771995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623669495105961346058653 233876060664735504771995)
                  ·
                    rfl

theorem cell20_512406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_512406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512406 prefixEnd_512406 := by exact prefixLift 512406
  have htrace : WordTrace (prefixWord ++ tailWord_512406) baseStart_512406 baseEnd_512406 := by
    simpa [prefixWord, tailWord_512406, baseEnd_512406] using wordTrace_append hprefix tailTrace_512406
  have hstable : (prefixWord ++ tailWord_512406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512406).length < 2 ^ (prefixWord ++ tailWord_512406).sum := by decide
  have hdescent : baseEnd_512406 < baseStart_512406 := by decide
  rcases family_descends (prefixWord ++ tailWord_512406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512421 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 2]
def baseStart_512421 : Nat := 118140960795 + 512421 * 2 ^ 59
def prefixEnd_512421 : Nat := 4983230072969 + 3 ^ 40 * 512421 * 2
def baseEnd_512421 : Nat := 233882907073462119271933

theorem tailTrace_512421 : CollatzResearch.WordTrace tailWord_512421 prefixEnd_512421 233882907073462119271933 := by
  unfold tailWord_512421
  simp only [CollatzResearch.WordTrace]
  refine ⟨18689529276593706384521117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12459686184395804256347411 18689529276593706384521117)
  ·
    refine ⟨7008573478722639894195419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18689529276593706384521117 7008573478722639894195419)
    ·
      refine ⟨10512860218083959841293129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008573478722639894195419 10512860218083959841293129)
      ·
        refine ⟨7884645163562969880969847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10512860218083959841293129 7884645163562969880969847)
        ·
          refine ⟨11826967745344454821454771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884645163562969880969847 11826967745344454821454771)
          ·
            refine ⟨17740451618016682232182157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826967745344454821454771 17740451618016682232182157)
            ·
              refine ⟨6652669356756255837068309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17740451618016682232182157 6652669356756255837068309)
              ·
                refine ⟨311843876097949492362577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6652669356756255837068309 311843876097949492362577)
                ·
                  refine ⟨233882907073462119271933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311843876097949492362577 233882907073462119271933)
                  ·
                    rfl

theorem cell20_512421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_512421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512421 prefixEnd_512421 := by exact prefixLift 512421
  have htrace : WordTrace (prefixWord ++ tailWord_512421) baseStart_512421 baseEnd_512421 := by
    simpa [prefixWord, tailWord_512421, baseEnd_512421] using wordTrace_append hprefix tailTrace_512421
  have hstable : (prefixWord ++ tailWord_512421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512421).length < 2 ^ (prefixWord ++ tailWord_512421).sum := by decide
  have hdescent : baseEnd_512421 < baseStart_512421 := by decide
  rcases family_descends (prefixWord ++ tailWord_512421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512445 : List Nat := [1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_512445 : Nat := 118140960795 + 512445 * 2 ^ 59
def prefixEnd_512445 : Nat := 4983230072969 + 3 ^ 40 * 512445 * 2
def baseEnd_512445 : Nat := 77964620442474900823945

theorem tailTrace_512445 : CollatzResearch.WordTrace tailWord_512445 prefixEnd_512445 77964620442474900823945 := by
  unfold tailWord_512445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690404628506758483394789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12460269752337838988929859 18690404628506758483394789)
  ·
    refine ⟨3504450867845017215636523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18690404628506758483394789 3504450867845017215636523)
    ·
      refine ⟨5256676301767525823454785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504450867845017215636523 5256676301767525823454785)
      ·
        refine ⟨3942507226325644367591089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256676301767525823454785 3942507226325644367591089)
        ·
          refine ⟨2956880419744233275693317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942507226325644367591089 2956880419744233275693317)
          ·
            refine ⟨554415078702043739192497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2956880419744233275693317 554415078702043739192497)
            ·
              refine ⟨415811309026532804394373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554415078702043739192497 415811309026532804394373)
              ·
                refine ⟨77964620442474900823945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415811309026532804394373 77964620442474900823945)
                ·
                  rfl

theorem cell20_512445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_512445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512445 prefixEnd_512445 := by exact prefixLift 512445
  have htrace : WordTrace (prefixWord ++ tailWord_512445) baseStart_512445 baseEnd_512445 := by
    simpa [prefixWord, tailWord_512445, baseEnd_512445] using wordTrace_append hprefix tailTrace_512445
  have hstable : (prefixWord ++ tailWord_512445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512445).length < 2 ^ (prefixWord ++ tailWord_512445).sum := by decide
  have hdescent : baseEnd_512445 < baseStart_512445 := by decide
  rcases family_descends (prefixWord ++ tailWord_512445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512473 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_512473 : Nat := 118140960795 + 512473 * 2 ^ 59
def prefixEnd_512473 : Nat := 4983230072969 + 3 ^ 40 * 512473 * 2
def baseEnd_512473 : Nat := 233906641290381049538387

theorem tailTrace_512473 : CollatzResearch.WordTrace tailWord_512473 prefixEnd_512473 233906641290381049538387 := by
  unfold tailWord_512473
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691425872405319265414073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12460950581603546176942715 18691425872405319265414073)
  ·
    refine ⟨14018569404303989449060555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18691425872405319265414073 14018569404303989449060555)
    ·
      refine ⟨21027854106455984173590833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14018569404303989449060555 21027854106455984173590833)
      ·
        refine ⟨15770890579841988130193125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21027854106455984173590833 15770890579841988130193125)
        ·
          refine ⟨2957041983720372774411211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15770890579841988130193125 2957041983720372774411211)
          ·
            refine ⟨4435562975580559161616817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957041983720372774411211 4435562975580559161616817)
            ·
              refine ⟨3326672231685419371212613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435562975580559161616817 3326672231685419371212613)
              ·
                refine ⟨623751043441016132102365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3326672231685419371212613 623751043441016132102365)
                ·
                  refine ⟨233906641290381049538387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623751043441016132102365 233906641290381049538387)
                  ·
                    rfl

theorem cell20_512473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_512473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512473 prefixEnd_512473 := by exact prefixLift 512473
  have htrace : WordTrace (prefixWord ++ tailWord_512473) baseStart_512473 baseEnd_512473 := by
    simpa [prefixWord, tailWord_512473, baseEnd_512473] using wordTrace_append hprefix tailTrace_512473
  have hstable : (prefixWord ++ tailWord_512473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512473).length < 2 ^ (prefixWord ++ tailWord_512473).sum := by decide
  have hdescent : baseEnd_512473 < baseStart_512473 := by decide
  rcases family_descends (prefixWord ++ tailWord_512473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512482 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_512482 : Nat := 118140960795 + 512482 * 2 ^ 59
def prefixEnd_512482 : Nat := 4983230072969 + 3 ^ 40 * 512482 * 2
def baseEnd_512482 : Nat := 233910749135617018238351

theorem tailTrace_512482 : CollatzResearch.WordTrace tailWord_512482 prefixEnd_512482 233910749135617018238351 := by
  unfold tailWord_512482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672938532343178450622925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12461169419581809201661133 4672938532343178450622925)
  ·
    refine ⟨1752351949628691918983597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4672938532343178450622925 1752351949628691918983597)
    ·
      refine ⟨657131981110759469618849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1752351949628691918983597 657131981110759469618849)
      ·
        refine ⟨492848985833069602214137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657131981110759469618849 492848985833069602214137)
        ·
          refine ⟨369636739374802201660603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492848985833069602214137 369636739374802201660603)
          ·
            refine ⟨554455109062203302490905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369636739374802201660603 554455109062203302490905)
            ·
              refine ⟨415841331796652476868179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554455109062203302490905 415841331796652476868179)
              ·
                refine ⟨623761997694978715302269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415841331796652476868179 623761997694978715302269)
                ·
                  refine ⟨233910749135617018238351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623761997694978715302269 233910749135617018238351)
                  ·
                    rfl

theorem cell20_512482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_512482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512482 prefixEnd_512482 := by exact prefixLift 512482
  have htrace : WordTrace (prefixWord ++ tailWord_512482) baseStart_512482 baseEnd_512482 := by
    simpa [prefixWord, tailWord_512482, baseEnd_512482] using wordTrace_append hprefix tailTrace_512482
  have hstable : (prefixWord ++ tailWord_512482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512482).length < 2 ^ (prefixWord ++ tailWord_512482).sum := by decide
  have hdescent : baseEnd_512482 < baseStart_512482 := by decide
  rcases family_descends (prefixWord ++ tailWord_512482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512490 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_512490 : Nat := 118140960795 + 512490 * 2 ^ 59
def prefixEnd_512490 : Nat := 4983230072969 + 3 ^ 40 * 512490 * 2
def baseEnd_512490 : Nat := 233914400553604545971651

theorem tailTrace_512490 : CollatzResearch.WordTrace tailWord_512490 prefixEnd_512490 233914400553604545971651 := by
  unfold tailWord_512490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673011478335932792195731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12461363942229154112521949 4673011478335932792195731)
  ·
    refine ⟨7009517217503899188293597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4673011478335932792195731 7009517217503899188293597)
    ·
      refine ⟨2628568956563962195610099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7009517217503899188293597 2628568956563962195610099)
      ·
        refine ⟨3942853434845943293415149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628568956563962195610099 3942853434845943293415149)
        ·
          refine ⟨1478570038067228735030681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3942853434845943293415149 1478570038067228735030681)
          ·
            refine ⟨1108927528550421551273011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478570038067228735030681 1108927528550421551273011)
            ·
              refine ⟨1663391292825632326909517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108927528550421551273011 1663391292825632326909517)
              ·
                refine ⟨623771734809612122591069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663391292825632326909517 623771734809612122591069)
                ·
                  refine ⟨233914400553604545971651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623771734809612122591069 233914400553604545971651)
                  ·
                    rfl

theorem cell20_512490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_512490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512490 prefixEnd_512490 := by exact prefixLift 512490
  have htrace : WordTrace (prefixWord ++ tailWord_512490) baseStart_512490 baseEnd_512490 := by
    simpa [prefixWord, tailWord_512490, baseEnd_512490] using wordTrace_append hprefix tailTrace_512490
  have hstable : (prefixWord ++ tailWord_512490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512490).length < 2 ^ (prefixWord ++ tailWord_512490).sum := by decide
  have hdescent : baseEnd_512490 < baseStart_512490 := by decide
  rcases family_descends (prefixWord ++ tailWord_512490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512539 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_512539 : Nat := 118140960795 + 512539 * 2 ^ 59
def prefixEnd_512539 : Nat := 4983230072969 + 3 ^ 40 * 512539 * 2
def baseEnd_512539 : Nat := 233936765488778153338117

theorem tailTrace_512539 : CollatzResearch.WordTrace tailWord_512539 prefixEnd_512539 233936765488778153338117 := by
  unfold tailWord_512539
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693833090166212537316671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12462555393444141691544447 18693833090166212537316671)
  ·
    refine ⟨28040749635249318805975007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18693833090166212537316671 28040749635249318805975007)
    ·
      refine ⟨42061124452873978208962511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28040749635249318805975007 42061124452873978208962511)
      ·
        refine ⟨63091686679310967313443767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42061124452873978208962511 63091686679310967313443767)
        ·
          refine ⟨94637530018966450970165651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63091686679310967313443767 94637530018966450970165651)
          ·
            refine ⟨141956295028449676455248477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94637530018966450970165651 141956295028449676455248477)
            ·
              refine ⟨53233610635668628670718179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141956295028449676455248477 53233610635668628670718179)
              ·
                refine ⟨79850415953502943006077269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53233610635668628670718179 79850415953502943006077269)
                ·
                  refine ⟨233936765488778153338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79850415953502943006077269 233936765488778153338117)
                  ·
                    rfl

theorem cell20_512539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_512539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512539 prefixEnd_512539 := by exact prefixLift 512539
  have htrace : WordTrace (prefixWord ++ tailWord_512539) baseStart_512539 baseEnd_512539 := by
    simpa [prefixWord, tailWord_512539, baseEnd_512539] using wordTrace_append hprefix tailTrace_512539
  have hstable : (prefixWord ++ tailWord_512539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512539).length < 2 ^ (prefixWord ++ tailWord_512539).sum := by decide
  have hdescent : baseEnd_512539 < baseStart_512539 := by decide
  rcases family_descends (prefixWord ++ tailWord_512539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512549 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_512549 : Nat := 118140960795 + 512549 * 2 ^ 59
def prefixEnd_512549 : Nat := 4983230072969 + 3 ^ 40 * 512549 * 2
def baseEnd_512549 : Nat := 233941329761262563004743

theorem tailTrace_512549 : CollatzResearch.WordTrace tailWord_512549 prefixEnd_512549 233941329761262563004743 := by
  unfold tailWord_512549
  simp only [CollatzResearch.WordTrace]
  refine ⟨18694197820129984245180701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12462798546753322830120467 18694197820129984245180701)
  ·
    refine ⟨7010324182548744091942763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18694197820129984245180701 7010324182548744091942763)
    ·
      refine ⟨10515486273823116137914145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7010324182548744091942763 10515486273823116137914145)
      ·
        refine ⟨7886614705367337103435609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10515486273823116137914145 7886614705367337103435609)
        ·
          refine ⟨5914961029025502827576707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7886614705367337103435609 5914961029025502827576707)
          ·
            refine ⟨8872441543538254241365061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914961029025502827576707 8872441543538254241365061)
            ·
              refine ⟨1663582789413422670255949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8872441543538254241365061 1663582789413422670255949)
              ·
                refine ⟨623843546030033501345981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663582789413422670255949 623843546030033501345981)
                ·
                  refine ⟨233941329761262563004743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623843546030033501345981 233941329761262563004743)
                  ·
                    rfl

theorem cell20_512549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_512549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512549 prefixEnd_512549 := by exact prefixLift 512549
  have htrace : WordTrace (prefixWord ++ tailWord_512549) baseStart_512549 baseEnd_512549 := by
    simpa [prefixWord, tailWord_512549, baseEnd_512549] using wordTrace_append hprefix tailTrace_512549
  have hstable : (prefixWord ++ tailWord_512549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512549).length < 2 ^ (prefixWord ++ tailWord_512549).sum := by decide
  have hdescent : baseEnd_512549 < baseStart_512549 := by decide
  rcases family_descends (prefixWord ++ tailWord_512549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512587 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_512587 : Nat := 118140960795 + 512587 * 2 ^ 59
def prefixEnd_512587 : Nat := 4983230072969 + 3 ^ 40 * 512587 * 2
def baseEnd_512587 : Nat := 233958673996703319737921

theorem tailTrace_512587 : CollatzResearch.WordTrace tailWord_512587 prefixEnd_512587 233958673996703319737921 := by
  unfold tailWord_512587
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695583793992316735064015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12463722529328211156709343 18695583793992316735064015)
  ·
    refine ⟨28043375690988475102596023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18695583793992316735064015 28043375690988475102596023)
    ·
      refine ⟨42065063536482712653894035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28043375690988475102596023 42065063536482712653894035)
      ·
        refine ⟨63097595304724068980841053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42065063536482712653894035 63097595304724068980841053)
        ·
          refine ⟨23661598239271525867815395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63097595304724068980841053 23661598239271525867815395)
          ·
            refine ⟨35492397358907288801723093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23661598239271525867815395 35492397358907288801723093)
            ·
              refine ⟨831853063099389581290385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35492397358907288801723093 831853063099389581290385)
              ·
                refine ⟨623889797324542185967789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831853063099389581290385 623889797324542185967789)
                ·
                  refine ⟨233958673996703319737921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623889797324542185967789 233958673996703319737921)
                  ·
                    rfl

theorem cell20_512587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_512587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512587 prefixEnd_512587 := by exact prefixLift 512587
  have htrace : WordTrace (prefixWord ++ tailWord_512587) baseStart_512587 baseEnd_512587 := by
    simpa [prefixWord, tailWord_512587, baseEnd_512587] using wordTrace_append hprefix tailTrace_512587
  have hstable : (prefixWord ++ tailWord_512587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512587).length < 2 ^ (prefixWord ++ tailWord_512587).sum := by decide
  have hdescent : baseEnd_512587 < baseStart_512587 := by decide
  rcases family_descends (prefixWord ++ tailWord_512587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512663 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_512663 : Nat := 118140960795 + 512663 * 2 ^ 59
def prefixEnd_512663 : Nat := 4983230072969 + 3 ^ 40 * 512663 * 2
def baseEnd_512663 : Nat := 233993362467584833204277

theorem tailTrace_512663 : CollatzResearch.WordTrace tailWord_512663 prefixEnd_512663 233993362467584833204277 := by
  unfold tailWord_512663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18698355741716981714830643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12465570494477987809887095 18698355741716981714830643)
  ·
    refine ⟨28047533612575472572245965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18698355741716981714830643 28047533612575472572245965)
    ·
      refine ⟨10517825104715802214592237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28047533612575472572245965 10517825104715802214592237)
      ·
        refine ⟨3944184414268425830472089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10517825104715802214592237 3944184414268425830472089)
        ·
          refine ⟨2958138310701319372854067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944184414268425830472089 2958138310701319372854067)
          ·
            refine ⟨4437207466051979059281101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958138310701319372854067 4437207466051979059281101)
            ·
              refine ⟨1663952799769492147230413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4437207466051979059281101 1663952799769492147230413)
              ·
                refine ⟨623982299913559555211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663952799769492147230413 623982299913559555211405)
                ·
                  refine ⟨233993362467584833204277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623982299913559555211405 233993362467584833204277)
                  ·
                    rfl

theorem cell20_512663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_512663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512663 prefixEnd_512663 := by exact prefixLift 512663
  have htrace : WordTrace (prefixWord ++ tailWord_512663) baseStart_512663 baseEnd_512663 := by
    simpa [prefixWord, tailWord_512663, baseEnd_512663] using wordTrace_append hprefix tailTrace_512663
  have hstable : (prefixWord ++ tailWord_512663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512663).length < 2 ^ (prefixWord ++ tailWord_512663).sum := by decide
  have hdescent : baseEnd_512663 < baseStart_512663 := by decide
  rcases family_descends (prefixWord ++ tailWord_512663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512694 : List Nat := [5, 1, 3, 1, 10]
def baseStart_512694 : Nat := 118140960795 + 512694 * 2 ^ 59
def prefixEnd_512694 : Nat := 4983230072969 + 3 ^ 40 * 512694 * 2
def baseEnd_512694 : Nat := 2888981626077611150257

theorem tailTrace_512694 : CollatzResearch.WordTrace tailWord_512694 prefixEnd_512694 2888981626077611150257 := by
  unfold tailWord_512694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168717900287792125575571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12466324269736449339472757 1168717900287792125575571)
  ·
    refine ⟨1753076850431688188363357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168717900287792125575571 1753076850431688188363357)
    ·
      refine ⟨657403818911883070636259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1753076850431688188363357 657403818911883070636259)
      ·
        refine ⟨986105728367824605954389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657403818911883070636259 986105728367824605954389)
        ·
          refine ⟨2888981626077611150257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 986105728367824605954389 2888981626077611150257)
          ·
            rfl

theorem cell20_512694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 10].length) (baseStart_512694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512694 prefixEnd_512694 := by exact prefixLift 512694
  have htrace : WordTrace (prefixWord ++ tailWord_512694) baseStart_512694 baseEnd_512694 := by
    simpa [prefixWord, tailWord_512694, baseEnd_512694] using wordTrace_append hprefix tailTrace_512694
  have hstable : (prefixWord ++ tailWord_512694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512694).length < 2 ^ (prefixWord ++ tailWord_512694).sum := by decide
  have hdescent : baseEnd_512694 < baseStart_512694 := by decide
  rcases family_descends (prefixWord ++ tailWord_512694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512701 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_512701 : Nat := 118140960795 + 512701 * 2 ^ 59
def prefixEnd_512701 : Nat := 4983230072969 + 3 ^ 40 * 512701 * 2
def baseEnd_512701 : Nat := 234010706703025589937455

theorem tailTrace_512701 : CollatzResearch.WordTrace tailWord_512701 prefixEnd_512701 234010706703025589937455 := by
  unfold tailWord_512701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18699741715579314204713957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12466494477052876136475971 18699741715579314204713957)
  ·
    refine ⟨3506201571671121413383867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18699741715579314204713957 3506201571671121413383867)
    ·
      refine ⟨5259302357506682120075801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3506201571671121413383867 5259302357506682120075801)
      ·
        refine ⟨3944476768130011590056851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5259302357506682120075801 3944476768130011590056851)
        ·
          refine ⟨5916715152195017385085277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944476768130011590056851 5916715152195017385085277)
          ·
            refine ⟨2218768182073131519406979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5916715152195017385085277 2218768182073131519406979)
            ·
              refine ⟨3328152273109697279110469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218768182073131519406979 3328152273109697279110469)
              ·
                refine ⟨624028551208068239833213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3328152273109697279110469 624028551208068239833213)
                ·
                  refine ⟨234010706703025589937455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624028551208068239833213 234010706703025589937455)
                  ·
                    rfl

theorem cell20_512701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_512701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512701 prefixEnd_512701 := by exact prefixLift 512701
  have htrace : WordTrace (prefixWord ++ tailWord_512701) baseStart_512701 baseEnd_512701 := by
    simpa [prefixWord, tailWord_512701, baseEnd_512701] using wordTrace_append hprefix tailTrace_512701
  have hstable : (prefixWord ++ tailWord_512701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512701).length < 2 ^ (prefixWord ++ tailWord_512701).sum := by decide
  have hdescent : baseEnd_512701 < baseStart_512701 := by decide
  rcases family_descends (prefixWord ++ tailWord_512701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512704 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_512704 : Nat := 118140960795 + 512704 * 2 ^ 59
def prefixEnd_512704 : Nat := 4983230072969 + 3 ^ 40 * 512704 * 2
def baseEnd_512704 : Nat := 234012075984770912837443

theorem tailTrace_512704 : CollatzResearch.WordTrace tailWord_512704 prefixEnd_512704 234012075984770912837443 := by
  unfold tailWord_512704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349925567284222858536583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12466567423045630478048777 9349925567284222858536583)
  ·
    refine ⟨14024888350926334287804875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9349925567284222858536583 14024888350926334287804875)
    ·
      refine ⟨21037332526389501431707313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024888350926334287804875 21037332526389501431707313)
      ·
        refine ⟨15777999394792126073780485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21037332526389501431707313 15777999394792126073780485)
        ·
          refine ⟨2958374886523523638833841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15777999394792126073780485 2958374886523523638833841)
          ·
            refine ⟨2218781164892642729125381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958374886523523638833841 2218781164892642729125381)
            ·
              refine ⟨416021468417370511711009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2218781164892642729125381 416021468417370511711009)
              ·
                refine ⟨312016101313027883783257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416021468417370511711009 312016101313027883783257)
                ·
                  refine ⟨234012075984770912837443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312016101313027883783257 234012075984770912837443)
                  ·
                    rfl

theorem cell20_512704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_512704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512704 prefixEnd_512704 := by exact prefixLift 512704
  have htrace : WordTrace (prefixWord ++ tailWord_512704) baseStart_512704 baseEnd_512704 := by
    simpa [prefixWord, tailWord_512704, baseEnd_512704] using wordTrace_append hprefix tailTrace_512704
  have hstable : (prefixWord ++ tailWord_512704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512704).length < 2 ^ (prefixWord ++ tailWord_512704).sum := by decide
  have hdescent : baseEnd_512704 < baseStart_512704 := by decide
  rcases family_descends (prefixWord ++ tailWord_512704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512760 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_512760 : Nat := 118140960795 + 512760 * 2 ^ 59
def prefixEnd_512760 : Nat := 4983230072969 + 3 ^ 40 * 512760 * 2
def baseEnd_512760 : Nat := 234037635910683606970547

theorem tailTrace_512760 : CollatzResearch.WordTrace tailWord_512760 prefixEnd_512760 234037635910683606970547 := by
  unfold tailWord_512760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350946811182783640555867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12467929081577044854074489 9350946811182783640555867)
  ·
    refine ⟨14026420216774175460833801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9350946811182783640555867 14026420216774175460833801)
    ·
      refine ⟨10519815162580631595625351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14026420216774175460833801 10519815162580631595625351)
      ·
        refine ⟨15779722743870947393438027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519815162580631595625351 15779722743870947393438027)
        ·
          refine ⟨23669584115806421090157041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15779722743870947393438027 23669584115806421090157041)
          ·
            refine ⟨17752188086854815817617781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23669584115806421090157041 17752188086854815817617781)
            ·
              refine ⟨1664267633142638982901667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17752188086854815817617781 1664267633142638982901667)
              ·
                refine ⟨2496401449713958474352501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664267633142638982901667 2496401449713958474352501)
                ·
                  refine ⟨234037635910683606970547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2496401449713958474352501 234037635910683606970547)
                  ·
                    rfl

theorem cell20_512760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_512760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512760 prefixEnd_512760 := by exact prefixLift 512760
  have htrace : WordTrace (prefixWord ++ tailWord_512760) baseStart_512760 baseEnd_512760 := by
    simpa [prefixWord, tailWord_512760, baseEnd_512760] using wordTrace_append hprefix tailTrace_512760
  have hstable : (prefixWord ++ tailWord_512760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512760).length < 2 ^ (prefixWord ++ tailWord_512760).sum := by decide
  have hdescent : baseEnd_512760 < baseStart_512760 := by decide
  rcases family_descends (prefixWord ++ tailWord_512760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512818 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_512818 : Nat := 118140960795 + 512818 * 2 ^ 59
def prefixEnd_512818 : Nat := 4983230072969 + 3 ^ 40 * 512818 * 2
def baseEnd_512818 : Nat := 234064108691093183036977

theorem tailTrace_512818 : CollatzResearch.WordTrace tailWord_512818 prefixEnd_512818 234064108691093183036977 := by
  unfold tailWord_512818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676002264038860796680777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12469339370770295457815405 4676002264038860796680777)
  ·
    refine ⟨3507001698029145597510583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4676002264038860796680777 3507001698029145597510583)
    ·
      refine ⟨5260502547043718396265875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507001698029145597510583 5260502547043718396265875)
      ·
        refine ⟨7890753820565577594398813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5260502547043718396265875 7890753820565577594398813)
        ·
          refine ⟨2959032682712091597899555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7890753820565577594398813 2959032682712091597899555)
          ·
            refine ⟨4438549024068137396849333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959032682712091597899555 4438549024068137396849333)
            ·
              refine ⟨416113971006387880954625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4438549024068137396849333 416113971006387880954625)
              ·
                refine ⟨312085478254790910715969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416113971006387880954625 312085478254790910715969)
                ·
                  refine ⟨234064108691093183036977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312085478254790910715969 234064108691093183036977)
                  ·
                    rfl

theorem cell20_512818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_512818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512818 prefixEnd_512818 := by exact prefixLift 512818
  have htrace : WordTrace (prefixWord ++ tailWord_512818) baseStart_512818 baseEnd_512818 := by
    simpa [prefixWord, tailWord_512818, baseEnd_512818] using wordTrace_append hprefix tailTrace_512818
  have hstable : (prefixWord ++ tailWord_512818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512818).length < 2 ^ (prefixWord ++ tailWord_512818).sum := by decide
  have hdescent : baseEnd_512818 < baseStart_512818 := by decide
  rcases family_descends (prefixWord ++ tailWord_512818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512888 : List Nat := [2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_512888 : Nat := 118140960795 + 512888 * 2 ^ 59
def prefixEnd_512888 : Nat := 4983230072969 + 3 ^ 40 * 512888 * 2
def baseEnd_512888 : Nat := 78032019532828016901119

theorem tailTrace_512888 : CollatzResearch.WordTrace tailWord_512888 prefixEnd_512888 78032019532828016901119 := by
  unfold tailWord_512888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353281082950922570885659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12471041443934563427847545 9353281082950922570885659)
  ·
    refine ⟨14029921624426383856328489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353281082950922570885659 14029921624426383856328489)
    ·
      refine ⟨10522441218319787892246367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14029921624426383856328489 10522441218319787892246367)
      ·
        refine ⟨15783661827479681838369551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522441218319787892246367 15783661827479681838369551)
        ·
          refine ⟨23675492741219522757554327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783661827479681838369551 23675492741219522757554327)
          ·
            refine ⟨35513239111829284136331491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23675492741219522757554327 35513239111829284136331491)
            ·
              refine ⟨53269858667743926204497237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35513239111829284136331491 53269858667743926204497237)
              ·
                refine ⟨78032019532828016901119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53269858667743926204497237 78032019532828016901119)
                ·
                  rfl

theorem cell20_512888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_512888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512888 prefixEnd_512888 := by exact prefixLift 512888
  have htrace : WordTrace (prefixWord ++ tailWord_512888) baseStart_512888 baseEnd_512888 := by
    simpa [prefixWord, tailWord_512888, baseEnd_512888] using wordTrace_append hprefix tailTrace_512888
  have hstable : (prefixWord ++ tailWord_512888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512888).length < 2 ^ (prefixWord ++ tailWord_512888).sum := by decide
  have hdescent : baseEnd_512888 < baseStart_512888 := by decide
  rcases family_descends (prefixWord ++ tailWord_512888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512894 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_512894 : Nat := 118140960795 + 512894 * 2 ^ 59
def prefixEnd_512894 : Nat := 4983230072969 + 3 ^ 40 * 512894 * 2
def baseEnd_512894 : Nat := 234098797161974696503333

theorem tailTrace_512894 : CollatzResearch.WordTrace tailWord_512894 prefixEnd_512894 234098797161974696503333 := by
  unfold tailWord_512894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338347625485013520811217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12471187335920072110993157 2338347625485013520811217)
  ·
    refine ⟨1753760719113760140608413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2338347625485013520811217 1753760719113760140608413)
    ·
      refine ⟨657660269667660052728155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1753760719113760140608413 657660269667660052728155)
      ·
        refine ⟨986490404501490079092233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657660269667660052728155 986490404501490079092233)
        ·
          refine ⟨739867803376117559319175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 986490404501490079092233 739867803376117559319175)
          ·
            refine ⟨1109801705064176338978763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739867803376117559319175 1109801705064176338978763)
            ·
              refine ⟨1664702557596264508468145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109801705064176338978763 1664702557596264508468145)
              ·
                refine ⟨1248526918197198381351109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664702557596264508468145 1248526918197198381351109)
                ·
                  refine ⟨234098797161974696503333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248526918197198381351109 234098797161974696503333)
                  ·
                    rfl

theorem cell20_512894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_512894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512894 prefixEnd_512894 := by exact prefixLift 512894
  have htrace : WordTrace (prefixWord ++ tailWord_512894) baseStart_512894 baseEnd_512894 := by
    simpa [prefixWord, tailWord_512894, baseEnd_512894] using wordTrace_append hprefix tailTrace_512894
  have hstable : (prefixWord ++ tailWord_512894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512894).length < 2 ^ (prefixWord ++ tailWord_512894).sum := by decide
  have hdescent : baseEnd_512894 < baseStart_512894 := by decide
  rcases family_descends (prefixWord ++ tailWord_512894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512919 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_512919 : Nat := 118140960795 + 512919 * 2 ^ 59
def prefixEnd_512919 : Nat := 4983230072969 + 3 ^ 40 * 512919 * 2
def baseEnd_512919 : Nat := 234110207843185720669897

theorem tailTrace_512919 : CollatzResearch.WordTrace tailWord_512919 prefixEnd_512919 234110207843185720669897 := by
  unfold tailWord_512919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707692828789537436149811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12471795219193024957433207 18707692828789537436149811)
  ·
    refine ⟨28061539243184306154224717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707692828789537436149811 28061539243184306154224717)
    ·
      refine ⟨10523077216194114807834269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28061539243184306154224717 10523077216194114807834269)
      ·
        refine ⟨3946153956072793052937851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10523077216194114807834269 3946153956072793052937851)
        ·
          refine ⟨5919230934109189579406777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946153956072793052937851 5919230934109189579406777)
          ·
            refine ⟨4439423200581892184555083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5919230934109189579406777 4439423200581892184555083)
            ·
              refine ⟨6659134800872838276832625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439423200581892184555083 6659134800872838276832625)
              ·
                refine ⟨4994351100654628707624469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659134800872838276832625 4994351100654628707624469)
                ·
                  refine ⟨234110207843185720669897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4994351100654628707624469 234110207843185720669897)
                  ·
                    rfl

theorem cell20_512919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_512919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512919 prefixEnd_512919 := by exact prefixLift 512919
  have htrace : WordTrace (prefixWord ++ tailWord_512919) baseStart_512919 baseEnd_512919 := by
    simpa [prefixWord, tailWord_512919, baseEnd_512919] using wordTrace_append hprefix tailTrace_512919
  have hstable : (prefixWord ++ tailWord_512919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512919).length < 2 ^ (prefixWord ++ tailWord_512919).sum := by decide
  have hdescent : baseEnd_512919 < baseStart_512919 := by decide
  rcases family_descends (prefixWord ++ tailWord_512919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512929 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_512929 : Nat := 118140960795 + 512929 * 2 ^ 59
def prefixEnd_512929 : Nat := 4983230072969 + 3 ^ 40 * 512929 * 2
def baseEnd_512929 : Nat := 234114772115670130336523

theorem tailTrace_512929 : CollatzResearch.WordTrace tailWord_512929 prefixEnd_512929 234114772115670130336523 := by
  unfold tailWord_512929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18708057558753309144013841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12472038372502206096009227 18708057558753309144013841)
  ·
    refine ⟨14031043169064981858010381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18708057558753309144013841 14031043169064981858010381)
    ·
      refine ⟨5261641188399368196753893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14031043169064981858010381 5261641188399368196753893)
      ·
        refine ⟨986557722824881536891355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5261641188399368196753893 986557722824881536891355)
        ·
          refine ⟨1479836584237322305337033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986557722824881536891355 1479836584237322305337033)
          ·
            refine ⟨1109877438177991729002775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479836584237322305337033 1109877438177991729002775)
            ·
              refine ⟨1664816157266987593504163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109877438177991729002775 1664816157266987593504163)
              ·
                refine ⟨2497224235900481390256245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664816157266987593504163 2497224235900481390256245)
                ·
                  refine ⟨234114772115670130336523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2497224235900481390256245 234114772115670130336523)
                  ·
                    rfl

theorem cell20_512929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_512929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512929 prefixEnd_512929 := by exact prefixLift 512929
  have htrace : WordTrace (prefixWord ++ tailWord_512929) baseStart_512929 baseEnd_512929 := by
    simpa [prefixWord, tailWord_512929, baseEnd_512929] using wordTrace_append hprefix tailTrace_512929
  have hstable : (prefixWord ++ tailWord_512929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512929).length < 2 ^ (prefixWord ++ tailWord_512929).sum := by decide
  have hdescent : baseEnd_512929 < baseStart_512929 := by decide
  rcases family_descends (prefixWord ++ tailWord_512929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512960 : List Nat := [2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_512960 : Nat := 118140960795 + 512960 * 2 ^ 59
def prefixEnd_512960 : Nat := 4983230072969 + 3 ^ 40 * 512960 * 2
def baseEnd_512960 : Nat := 78042973786790600101021

theorem tailTrace_512960 : CollatzResearch.WordTrace tailWord_512960 prefixEnd_512960 78042973786790600101021 := by
  unfold tailWord_512960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354594110820500719196167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12472792147760667625594889 9354594110820500719196167)
  ·
    refine ⟨14031891166230751078794251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354594110820500719196167 14031891166230751078794251)
    ·
      refine ⟨21047836749346126618191377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14031891166230751078794251 21047836749346126618191377)
      ·
        refine ⟨15785877562009594963643533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21047836749346126618191377 15785877562009594963643533)
        ·
          refine ⟨5919704085753598111366325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15785877562009594963643533 5919704085753598111366325)
          ·
            refine ⟨554972258039399822940593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5919704085753598111366325 554972258039399822940593)
            ·
              refine ⟨416229193529549867205445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554972258039399822940593 416229193529549867205445)
              ·
                refine ⟨78042973786790600101021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416229193529549867205445 78042973786790600101021)
                ·
                  rfl

theorem cell20_512960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_512960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512960 prefixEnd_512960 := by exact prefixLift 512960
  have htrace : WordTrace (prefixWord ++ tailWord_512960) baseStart_512960 baseEnd_512960 := by
    simpa [prefixWord, tailWord_512960, baseEnd_512960] using wordTrace_append hprefix tailTrace_512960
  have hstable : (prefixWord ++ tailWord_512960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512960).length < 2 ^ (prefixWord ++ tailWord_512960).sum := by decide
  have hdescent : baseEnd_512960 < baseStart_512960 := by decide
  rcases family_descends (prefixWord ++ tailWord_512960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512973 : List Nat := [1, 6, 3, 1, 2, 1, 6]
def baseStart_512973 : Nat := 118140960795 + 512973 * 2 ^ 59
def prefixEnd_512973 : Nat := 4983230072969 + 3 ^ 40 * 512973 * 2
def baseEnd_512973 : Nat := 26014983879400170318853

theorem tailTrace_512973 : CollatzResearch.WordTrace tailWord_512973 prefixEnd_512973 26014983879400170318853 := by
  unfold tailWord_512973
  simp only [CollatzResearch.WordTrace]
  refine ⟨18709662370593904658615573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12473108247062603105743715 18709662370593904658615573)
  ·
    refine ⟨877015423621589280872605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18709662370593904658615573 877015423621589280872605)
    ·
      refine ⟨328880783858095980327227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 877015423621589280872605 328880783858095980327227)
      ·
        refine ⟨493321175787143970490841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328880783858095980327227 493321175787143970490841)
        ·
          refine ⟨369990881840357977868131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493321175787143970490841 369990881840357977868131)
          ·
            refine ⟨554986322760536966802197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369990881840357977868131 554986322760536966802197)
            ·
              refine ⟨26014983879400170318853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554986322760536966802197 26014983879400170318853)
              ·
                rfl

theorem cell20_512973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 6].length) (baseStart_512973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512973 prefixEnd_512973 := by exact prefixLift 512973
  have htrace : WordTrace (prefixWord ++ tailWord_512973) baseStart_512973 baseEnd_512973 := by
    simpa [prefixWord, tailWord_512973, baseEnd_512973] using wordTrace_append hprefix tailTrace_512973
  have hstable : (prefixWord ++ tailWord_512973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512973).length < 2 ^ (prefixWord ++ tailWord_512973).sum := by decide
  have hdescent : baseEnd_512973 < baseStart_512973 := by decide
  rcases family_descends (prefixWord ++ tailWord_512973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512991 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_512991 : Nat := 118140960795 + 512991 * 2 ^ 59
def prefixEnd_512991 : Nat := 4983230072969 + 3 ^ 40 * 512991 * 2
def baseEnd_512991 : Nat := 234143070605073470269603

theorem tailTrace_512991 : CollatzResearch.WordTrace tailWord_512991 prefixEnd_512991 234143070605073470269603 := by
  unfold tailWord_512991
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710318884528693732770827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12473545923019129155180551 18710318884528693732770827)
  ·
    refine ⟨28065478326793040599156241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18710318884528693732770827 28065478326793040599156241)
    ·
      refine ⟨21049108745094780449367181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28065478326793040599156241 21049108745094780449367181)
      ·
        refine ⟨7893415779410542668512693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21049108745094780449367181 7893415779410542668512693)
        ·
          refine ⟨740007729319738375173065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7893415779410542668512693 740007729319738375173065)
          ·
            refine ⟨555005796989803781379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740007729319738375173065 555005796989803781379799)
            ·
              refine ⟨832508695484705672069699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555005796989803781379799 832508695484705672069699)
              ·
                refine ⟨1248763043227058508104549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832508695484705672069699 1248763043227058508104549)
                ·
                  refine ⟨234143070605073470269603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248763043227058508104549 234143070605073470269603)
                  ·
                    rfl

theorem cell20_512991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_512991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_512991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_512991 prefixEnd_512991 := by exact prefixLift 512991
  have htrace : WordTrace (prefixWord ++ tailWord_512991) baseStart_512991 baseEnd_512991 := by
    simpa [prefixWord, tailWord_512991, baseEnd_512991] using wordTrace_append hprefix tailTrace_512991
  have hstable : (prefixWord ++ tailWord_512991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512991).length < 2 ^ (prefixWord ++ tailWord_512991).sum := by decide
  have hdescent : baseEnd_512991 < baseStart_512991 := by decide
  rcases family_descends (prefixWord ++ tailWord_512991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513042 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_513042 : Nat := 118140960795 + 513042 * 2 ^ 59
def prefixEnd_513042 : Nat := 4983230072969 + 3 ^ 40 * 513042 * 2
def baseEnd_513042 : Nat := 234166348394743959569395

theorem tailTrace_513042 : CollatzResearch.WordTrace tailWord_513042 prefixEnd_513042 234166348394743959569395 := by
  unfold tailWord_513042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678044751835982360719345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12474786004895952961918253 4678044751835982360719345)
  ·
    refine ⟨3508533563876986770539509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4678044751835982360719345 3508533563876986770539509)
    ·
      refine ⟨328925021613467509738079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3508533563876986770539509 328925021613467509738079)
      ·
        refine ⟨493387532420201264607119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328925021613467509738079 493387532420201264607119)
        ·
          refine ⟨740081298630301896910679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493387532420201264607119 740081298630301896910679)
          ·
            refine ⟨1110121947945452845366019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740081298630301896910679 1110121947945452845366019)
            ·
              refine ⟨1665182921918179268049029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110121947945452845366019 1665182921918179268049029)
              ·
                refine ⟨312221797859658612759193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1665182921918179268049029 312221797859658612759193)
                ·
                  refine ⟨234166348394743959569395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312221797859658612759193 234166348394743959569395)
                  ·
                    rfl

theorem cell20_513042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_513042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513042 prefixEnd_513042 := by exact prefixLift 513042
  have htrace : WordTrace (prefixWord ++ tailWord_513042) baseStart_513042 baseEnd_513042 := by
    simpa [prefixWord, tailWord_513042, baseEnd_513042] using wordTrace_append hprefix tailTrace_513042
  have hstable : (prefixWord ++ tailWord_513042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513042).length < 2 ^ (prefixWord ++ tailWord_513042).sum := by decide
  have hdescent : baseEnd_513042 < baseStart_513042 := by decide
  rcases family_descends (prefixWord ++ tailWord_513042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513053 : List Nat := [1, 4, 2, 2, 4, 1, 1, 5]
def baseStart_513053 : Nat := 118140960795 + 513053 * 2 ^ 59
def prefixEnd_513053 : Nat := 4983230072969 + 3 ^ 40 * 513053 * 2
def baseEnd_513053 : Nat := 78057123031492270067561

theorem tailTrace_513053 : CollatzResearch.WordTrace tailWord_513053 prefixEnd_513053 78057123031492270067561 := by
  unfold tailWord_513053
  simp only [CollatzResearch.WordTrace]
  refine ⟨18712580210304078321527813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12475053473536052214351875 18712580210304078321527813)
  ·
    refine ⟨3508608789432014685286465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18712580210304078321527813 3508608789432014685286465)
    ·
      refine ⟨2631456592074011013964849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3508608789432014685286465 2631456592074011013964849)
      ·
        refine ⟨1973592444055508260473637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631456592074011013964849 1973592444055508260473637)
        ·
          refine ⟨370048583260407798838807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1973592444055508260473637 370048583260407798838807)
          ·
            refine ⟨555072874890611698258211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370048583260407798838807 555072874890611698258211)
            ·
              refine ⟨832609312335917547387317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555072874890611698258211 832609312335917547387317)
              ·
                refine ⟨78057123031492270067561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 832609312335917547387317 78057123031492270067561)
                ·
                  rfl

theorem cell20_513053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_513053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513053 prefixEnd_513053 := by exact prefixLift 513053
  have htrace : WordTrace (prefixWord ++ tailWord_513053) baseStart_513053 baseEnd_513053 := by
    simpa [prefixWord, tailWord_513053, baseEnd_513053] using wordTrace_append hprefix tailTrace_513053
  have hstable : (prefixWord ++ tailWord_513053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513053).length < 2 ^ (prefixWord ++ tailWord_513053).sum := by decide
  have hdescent : baseEnd_513053 < baseStart_513053 := by decide
  rcases family_descends (prefixWord ++ tailWord_513053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513057 : List Nat := [1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_513057 : Nat := 118140960795 + 513057 * 2 ^ 59
def prefixEnd_513057 : Nat := 4983230072969 + 3 ^ 40 * 513057 * 2
def baseEnd_513057 : Nat := 78057731601156858023111

theorem tailTrace_513057 : CollatzResearch.WordTrace tailWord_513057 prefixEnd_513057 78057731601156858023111 := by
  unfold tailWord_513057
  simp only [CollatzResearch.WordTrace]
  refine ⟨18712726102289587004673425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12475150734859724669782283 18712726102289587004673425)
  ·
    refine ⟨14034544576717190253505069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18712726102289587004673425 14034544576717190253505069)
    ·
      refine ⟨5262954216268946345064401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14034544576717190253505069 5262954216268946345064401)
      ·
        refine ⟨3947215662201709758798301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5262954216268946345064401 3947215662201709758798301)
        ·
          refine ⟨1480205873325641159549363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3947215662201709758798301 1480205873325641159549363)
          ·
            refine ⟨2220308809988461739324045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480205873325641159549363 2220308809988461739324045)
            ·
              refine ⟨832615803745673152246517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2220308809988461739324045 832615803745673152246517)
              ·
                refine ⟨78057731601156858023111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 832615803745673152246517 78057731601156858023111)
                ·
                  rfl

theorem cell20_513057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_513057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513057 prefixEnd_513057 := by exact prefixLift 513057
  have htrace : WordTrace (prefixWord ++ tailWord_513057) baseStart_513057 baseEnd_513057 := by
    simpa [prefixWord, tailWord_513057, baseEnd_513057] using wordTrace_append hprefix tailTrace_513057
  have hstable : (prefixWord ++ tailWord_513057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513057).length < 2 ^ (prefixWord ++ tailWord_513057).sum := by decide
  have hdescent : baseEnd_513057 < baseStart_513057 := by decide
  rcases family_descends (prefixWord ++ tailWord_513057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513102 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_513102 : Nat := 118140960795 + 513102 * 2 ^ 59
def prefixEnd_513102 : Nat := 4983230072969 + 3 ^ 40 * 513102 * 2
def baseEnd_513102 : Nat := 234193734029650417569149

theorem tailTrace_513102 : CollatzResearch.WordTrace tailWord_513102 prefixEnd_513102 234193734029650417569149 := by
  unfold tailWord_513102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339295923390819961257695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12476244924751039793374373 2339295923390819961257695)
  ·
    refine ⟨3508943885086229941886543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2339295923390819961257695 3508943885086229941886543)
    ·
      refine ⟨5263415827629344912829815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508943885086229941886543 5263415827629344912829815)
      ·
        refine ⟨7895123741444017369244723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263415827629344912829815 7895123741444017369244723)
        ·
          refine ⟨11842685612166026053867085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895123741444017369244723 11842685612166026053867085)
          ·
            refine ⟨4441007104562259770200157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11842685612166026053867085 4441007104562259770200157)
            ·
              refine ⟨1665377664210847413825059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4441007104562259770200157 1665377664210847413825059)
              ·
                refine ⟨2498066496316271120737589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665377664210847413825059 2498066496316271120737589)
                ·
                  refine ⟨234193734029650417569149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2498066496316271120737589 234193734029650417569149)
                  ·
                    rfl

theorem cell20_513102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_513102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513102 prefixEnd_513102 := by exact prefixLift 513102
  have htrace : WordTrace (prefixWord ++ tailWord_513102) baseStart_513102 baseEnd_513102 := by
    simpa [prefixWord, tailWord_513102, baseEnd_513102] using wordTrace_append hprefix tailTrace_513102
  have hstable : (prefixWord ++ tailWord_513102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513102).length < 2 ^ (prefixWord ++ tailWord_513102).sum := by decide
  have hdescent : baseEnd_513102 < baseStart_513102 := by decide
  rcases family_descends (prefixWord ++ tailWord_513102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513119 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 3]
def baseStart_513119 : Nat := 118140960795 + 513119 * 2 ^ 59
def prefixEnd_513119 : Nat := 4983230072969 + 3 ^ 40 * 513119 * 2
def baseEnd_513119 : Nat := 234201493292873914002413

theorem tailTrace_513119 : CollatzResearch.WordTrace tailWord_513119 prefixEnd_513119 234201493292873914002413 := by
  unfold tailWord_513119
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714987428064971593430411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12476658285376647728953607 18714987428064971593430411)
  ·
    refine ⟨28072481142097457390145617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18714987428064971593430411 28072481142097457390145617)
    ·
      refine ⟨21054360856573093042609213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28072481142097457390145617 21054360856573093042609213)
      ·
        refine ⟨7895385321214909890978455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21054360856573093042609213 7895385321214909890978455)
        ·
          refine ⟨11843077981822364836467683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895385321214909890978455 11843077981822364836467683)
          ·
            refine ⟨17764616972733547254701525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843077981822364836467683 17764616972733547254701525)
            ·
              refine ⟨416358210298442513782067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17764616972733547254701525 416358210298442513782067)
              ·
                refine ⟨624537315447663770673101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416358210298442513782067 624537315447663770673101)
                ·
                  refine ⟨234201493292873914002413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624537315447663770673101 234201493292873914002413)
                  ·
                    rfl

theorem cell20_513119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_513119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513119 prefixEnd_513119 := by exact prefixLift 513119
  have htrace : WordTrace (prefixWord ++ tailWord_513119) baseStart_513119 baseEnd_513119 := by
    simpa [prefixWord, tailWord_513119, baseEnd_513119] using wordTrace_append hprefix tailTrace_513119
  have hstable : (prefixWord ++ tailWord_513119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513119).length < 2 ^ (prefixWord ++ tailWord_513119).sum := by decide
  have hdescent : baseEnd_513119 < baseStart_513119 := by decide
  rcases family_descends (prefixWord ++ tailWord_513119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513133 : List Nat := [1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_513133 : Nat := 118140960795 + 513133 * 2 ^ 59
def prefixEnd_513133 : Nat := 4983230072969 + 3 ^ 40 * 513133 * 2
def baseEnd_513133 : Nat := 78069294424784029178563

theorem tailTrace_513133 : CollatzResearch.WordTrace tailWord_513133 prefixEnd_513133 78069294424784029178563 := by
  unfold tailWord_513133
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715498050014251984440053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12476998700009501322960035 18715498050014251984440053)
  ·
    refine ⟨1754577942188836123541255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18715498050014251984440053 1754577942188836123541255)
    ·
      refine ⟨2631866913283254185311883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754577942188836123541255 2631866913283254185311883)
      ·
        refine ⟨3947800369924881277967825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631866913283254185311883 3947800369924881277967825)
        ·
          refine ⟨2960850277443660958475869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947800369924881277967825 2960850277443660958475869)
          ·
            refine ⟨1110318854041372859428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2960850277443660958475869 1110318854041372859428451)
            ·
              refine ⟨1665478281062059289142677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110318854041372859428451 1665478281062059289142677)
              ·
                refine ⟨78069294424784029178563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1665478281062059289142677 78069294424784029178563)
                ·
                  rfl

theorem cell20_513133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_513133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513133 prefixEnd_513133 := by exact prefixLift 513133
  have htrace : WordTrace (prefixWord ++ tailWord_513133) baseStart_513133 baseEnd_513133 := by
    simpa [prefixWord, tailWord_513133, baseEnd_513133] using wordTrace_append hprefix tailTrace_513133
  have hstable : (prefixWord ++ tailWord_513133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513133).length < 2 ^ (prefixWord ++ tailWord_513133).sum := by decide
  have hdescent : baseEnd_513133 < baseStart_513133 := by decide
  rcases family_descends (prefixWord ++ tailWord_513133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513160 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_513160 : Nat := 118140960795 + 513160 * 2 ^ 59
def prefixEnd_513160 : Nat := 4983230072969 + 3 ^ 40 * 513160 * 2
def baseEnd_513160 : Nat := 234220206810059993635579

theorem tailTrace_513160 : CollatzResearch.WordTrace tailWord_513160 prefixEnd_513160 234220206810059993635579 := by
  unfold tailWord_513160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358241410458217797836467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12477655213944290397115289 9358241410458217797836467)
  ·
    refine ⟨14037362115687326696754701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9358241410458217797836467 14037362115687326696754701)
    ·
      refine ⟨5264010793382747511283013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14037362115687326696754701 5264010793382747511283013)
      ·
        refine ⟨987002023759265158365565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5264010793382747511283013 987002023759265158365565)
        ·
          refine ⟨370125758909724434387087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987002023759265158365565 370125758909724434387087)
          ·
            refine ⟨555188638364586651580631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370125758909724434387087 555188638364586651580631)
            ·
              refine ⟨832782957546879977370947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555188638364586651580631 832782957546879977370947)
              ·
                refine ⟨1249174436320319966056421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832782957546879977370947 1249174436320319966056421)
                ·
                  refine ⟨234220206810059993635579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249174436320319966056421 234220206810059993635579)
                  ·
                    rfl

theorem cell20_513160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_513160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513160 prefixEnd_513160 := by exact prefixLift 513160
  have htrace : WordTrace (prefixWord ++ tailWord_513160) baseStart_513160 baseEnd_513160 := by
    simpa [prefixWord, tailWord_513160, baseEnd_513160] using wordTrace_append hprefix tailTrace_513160
  have hstable : (prefixWord ++ tailWord_513160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513160).length < 2 ^ (prefixWord ++ tailWord_513160).sum := by decide
  have hdescent : baseEnd_513160 < baseStart_513160 := by decide
  rcases family_descends (prefixWord ++ tailWord_513160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513164 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_513164 : Nat := 118140960795 + 513164 * 2 ^ 59
def prefixEnd_513164 : Nat := 4983230072969 + 3 ^ 40 * 513164 * 2
def baseEnd_513164 : Nat := 234222032519053757502229

theorem tailTrace_513164 : CollatzResearch.WordTrace tailWord_513164 prefixEnd_513164 234222032519053757502229 := by
  unfold tailWord_513164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358314356450972139409273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12477752475267962852545697 9358314356450972139409273)
  ·
    refine ⟨7018735767338229104556955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9358314356450972139409273 7018735767338229104556955)
    ·
      refine ⟨10528103651007343656835433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018735767338229104556955 10528103651007343656835433)
      ·
        refine ⟨7896077738255507742626575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10528103651007343656835433 7896077738255507742626575)
        ·
          refine ⟨11844116607383261613939863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896077738255507742626575 11844116607383261613939863)
          ·
            refine ⟨17766174911074892420909795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11844116607383261613939863 17766174911074892420909795)
            ·
              refine ⟨26649262366612338631364693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17766174911074892420909795 26649262366612338631364693)
              ·
                refine ⟨312296043358738343336305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 26649262366612338631364693 312296043358738343336305)
                ·
                  refine ⟨234222032519053757502229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312296043358738343336305 234222032519053757502229)
                  ·
                    rfl

theorem cell20_513164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_513164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513164 prefixEnd_513164 := by exact prefixLift 513164
  have htrace : WordTrace (prefixWord ++ tailWord_513164) baseStart_513164 baseEnd_513164 := by
    simpa [prefixWord, tailWord_513164, baseEnd_513164] using wordTrace_append hprefix tailTrace_513164
  have hstable : (prefixWord ++ tailWord_513164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513164).length < 2 ^ (prefixWord ++ tailWord_513164).sum := by decide
  have hdescent : baseEnd_513164 < baseStart_513164 := by decide
  rcases family_descends (prefixWord ++ tailWord_513164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513185 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_513185 : Nat := 118140960795 + 513185 * 2 ^ 59
def prefixEnd_513185 : Nat := 4983230072969 + 3 ^ 40 * 513185 * 2
def baseEnd_513185 : Nat := 234231617491271017802143

theorem tailTrace_513185 : CollatzResearch.WordTrace tailWord_513185 prefixEnd_513185 234231617491271017802143 := by
  unfold tailWord_513185
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717394645825864865333009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12478263097217243243555339 18717394645825864865333009)
  ·
    refine ⟨14038045984369398648999757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18717394645825864865333009 14038045984369398648999757)
    ·
      refine ⟨5264267244138524493374909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14038045984369398648999757 5264267244138524493374909)
      ·
        refine ⟨1974100216551946685015591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5264267244138524493374909 1974100216551946685015591)
        ·
          refine ⟨2961150324827920027523387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974100216551946685015591 2961150324827920027523387)
          ·
            refine ⟨4441725487241880041285081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961150324827920027523387 4441725487241880041285081)
            ·
              refine ⟨3331294115431410030963811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4441725487241880041285081 3331294115431410030963811)
              ·
                refine ⟨4996941173147115046445717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331294115431410030963811 4996941173147115046445717)
                ·
                  refine ⟨234231617491271017802143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4996941173147115046445717 234231617491271017802143)
                  ·
                    rfl

theorem cell20_513185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_513185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513185 prefixEnd_513185 := by exact prefixLift 513185
  have htrace : WordTrace (prefixWord ++ tailWord_513185) baseStart_513185 baseEnd_513185 := by
    simpa [prefixWord, tailWord_513185, baseEnd_513185] using wordTrace_append hprefix tailTrace_513185
  have hstable : (prefixWord ++ tailWord_513185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513185).length < 2 ^ (prefixWord ++ tailWord_513185).sum := by decide
  have hdescent : baseEnd_513185 < baseStart_513185 := by decide
  rcases family_descends (prefixWord ++ tailWord_513185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513199 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_513199 : Nat := 118140960795 + 513199 * 2 ^ 59
def prefixEnd_513199 : Nat := 4983230072969 + 3 ^ 40 * 513199 * 2
def baseEnd_513199 : Nat := 234238007472749191335419

theorem tailTrace_513199 : CollatzResearch.WordTrace tailWord_513199 prefixEnd_513199 234238007472749191335419 := by
  unfold tailWord_513199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717905267775145256342651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12478603511850096837561767 18717905267775145256342651)
  ·
    refine ⟨28076857901662717884513977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18717905267775145256342651 28076857901662717884513977)
    ·
      refine ⟨21057643426247038413385483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28076857901662717884513977 21057643426247038413385483)
      ·
        refine ⟨31586465139370557620078225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21057643426247038413385483 31586465139370557620078225)
        ·
          refine ⟨23689848854527918215058669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31586465139370557620078225 23689848854527918215058669)
          ·
            refine ⟨8883693320447969330647001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23689848854527918215058669 8883693320447969330647001)
            ·
              refine ⟨6662769990335976997985251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8883693320447969330647001 6662769990335976997985251)
              ·
                refine ⟨9994154985503965496977877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662769990335976997985251 9994154985503965496977877)
                ·
                  refine ⟨234238007472749191335419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9994154985503965496977877 234238007472749191335419)
                  ·
                    rfl

theorem cell20_513199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_513199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513199 prefixEnd_513199 := by exact prefixLift 513199
  have htrace : WordTrace (prefixWord ++ tailWord_513199) baseStart_513199 baseEnd_513199 := by
    simpa [prefixWord, tailWord_513199, baseEnd_513199] using wordTrace_append hprefix tailTrace_513199
  have hstable : (prefixWord ++ tailWord_513199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513199).length < 2 ^ (prefixWord ++ tailWord_513199).sum := by decide
  have hdescent : baseEnd_513199 < baseStart_513199 := by decide
  rcases family_descends (prefixWord ++ tailWord_513199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513240 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_513240 : Nat := 118140960795 + 513240 * 2 ^ 59
def prefixEnd_513240 : Nat := 4983230072969 + 3 ^ 40 * 513240 * 2
def baseEnd_513240 : Nat := 234256720989935270968585

theorem tailTrace_513240 : CollatzResearch.WordTrace tailWord_513240 prefixEnd_513240 234256720989935270968585 := by
  unfold tailWord_513240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359700330313304629292587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12479600440417739505723449 9359700330313304629292587)
  ·
    refine ⟨14039550495469956943938881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9359700330313304629292587 14039550495469956943938881)
    ·
      refine ⟨10529662871602467707954161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14039550495469956943938881 10529662871602467707954161)
      ·
        refine ⟨7897247153701850780965621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10529662871602467707954161 7897247153701850780965621)
        ·
          refine ⟨740366920659548510715527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7897247153701850780965621 740366920659548510715527)
          ·
            refine ⟨1110550380989322766073291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740366920659548510715527 1110550380989322766073291)
            ·
              refine ⟨1665825571483984149109937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110550380989322766073291 1665825571483984149109937)
              ·
                refine ⟨1249369178612988111832453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665825571483984149109937 1249369178612988111832453)
                ·
                  refine ⟨234256720989935270968585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249369178612988111832453 234256720989935270968585)
                  ·
                    rfl

theorem cell20_513240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_513240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513240 prefixEnd_513240 := by exact prefixLift 513240
  have htrace : WordTrace (prefixWord ++ tailWord_513240) baseStart_513240 baseEnd_513240 := by
    simpa [prefixWord, tailWord_513240, baseEnd_513240] using wordTrace_append hprefix tailTrace_513240
  have hstable : (prefixWord ++ tailWord_513240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513240).length < 2 ^ (prefixWord ++ tailWord_513240).sum := by decide
  have hdescent : baseEnd_513240 < baseStart_513240 := by decide
  rcases family_descends (prefixWord ++ tailWord_513240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513278 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_513278 : Nat := 118140960795 + 513278 * 2 ^ 59
def prefixEnd_513278 : Nat := 4983230072969 + 3 ^ 40 * 513278 * 2
def baseEnd_513278 : Nat := 234274065225376027701763

theorem tailTrace_513278 : CollatzResearch.WordTrace tailWord_513278 prefixEnd_513278 234274065225376027701763 := by
  unfold tailWord_513278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340098329311117718558561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12480524422992627832312325 2340098329311117718558561)
  ·
    refine ⟨1755073746983338288918921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2340098329311117718558561 1755073746983338288918921)
    ·
      refine ⟨1316305310237503716689191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755073746983338288918921 1316305310237503716689191)
      ·
        refine ⟨1974457965356255575033787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316305310237503716689191 1974457965356255575033787)
        ·
          refine ⟨2961686948034383362550681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974457965356255575033787 2961686948034383362550681)
          ·
            refine ⟨2221265211025787521913011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961686948034383362550681 2221265211025787521913011)
            ·
              refine ⟨3331897816538681282869517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221265211025787521913011 3331897816538681282869517)
              ·
                refine ⟨1249461681202005481076069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331897816538681282869517 1249461681202005481076069)
                ·
                  refine ⟨234274065225376027701763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249461681202005481076069 234274065225376027701763)
                  ·
                    rfl

theorem cell20_513278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_513278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513278 prefixEnd_513278 := by exact prefixLift 513278
  have htrace : WordTrace (prefixWord ++ tailWord_513278) baseStart_513278 baseEnd_513278 := by
    simpa [prefixWord, tailWord_513278, baseEnd_513278] using wordTrace_append hprefix tailTrace_513278
  have hstable : (prefixWord ++ tailWord_513278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513278).length < 2 ^ (prefixWord ++ tailWord_513278).sum := by decide
  have hdescent : baseEnd_513278 < baseStart_513278 := by decide
  rcases family_descends (prefixWord ++ tailWord_513278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513288 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_513288 : Nat := 118140960795 + 513288 * 2 ^ 59
def prefixEnd_513288 : Nat := 4983230072969 + 3 ^ 40 * 513288 * 2
def baseEnd_513288 : Nat := 234278629497860437368389

theorem tailTrace_513288 : CollatzResearch.WordTrace tailWord_513288 prefixEnd_513288 234278629497860437368389 := by
  unfold tailWord_513288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360575682226356728166259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12480767576301808970888345 9360575682226356728166259)
  ·
    refine ⟨14040863523339535092249389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360575682226356728166259 14040863523339535092249389)
    ·
      refine ⟨5265323821252325659593521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14040863523339535092249389 5265323821252325659593521)
      ·
        refine ⟨3948992865939244244695141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5265323821252325659593521 3948992865939244244695141)
        ·
          refine ⟨740436162363608295880339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3948992865939244244695141 740436162363608295880339)
          ·
            refine ⟨1110654243545412443820509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740436162363608295880339 1110654243545412443820509)
            ·
              refine ⟨416495341329529666432691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110654243545412443820509 416495341329529666432691)
              ·
                refine ⟨624743011994294499649037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416495341329529666432691 624743011994294499649037)
                ·
                  refine ⟨234278629497860437368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624743011994294499649037 234278629497860437368389)
                  ·
                    rfl

theorem cell20_513288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_513288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513288 prefixEnd_513288 := by exact prefixLift 513288
  have htrace : WordTrace (prefixWord ++ tailWord_513288) baseStart_513288 baseEnd_513288 := by
    simpa [prefixWord, tailWord_513288, baseEnd_513288] using wordTrace_append hprefix tailTrace_513288
  have hstable : (prefixWord ++ tailWord_513288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513288).length < 2 ^ (prefixWord ++ tailWord_513288).sum := by decide
  have hdescent : baseEnd_513288 < baseStart_513288 := by decide
  rcases family_descends (prefixWord ++ tailWord_513288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513298 : List Nat := [3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_513298 : Nat := 118140960795 + 513298 * 2 ^ 59
def prefixEnd_513298 : Nat := 4983230072969 + 3 ^ 40 * 513298 * 2
def baseEnd_513298 : Nat := 78094397923448282345005

theorem tailTrace_513298 : CollatzResearch.WordTrace tailWord_513298 prefixEnd_513298 78094397923448282345005 := by
  unfold tailWord_513298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680379023604121291049137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12481010729610990109464365 4680379023604121291049137)
  ·
    refine ⟨3510284267703090968286853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4680379023604121291049137 3510284267703090968286853)
    ·
      refine ⟨658178300194329556553785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3510284267703090968286853 658178300194329556553785)
      ·
        refine ⟨493633725145747167415339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658178300194329556553785 493633725145747167415339)
        ·
          refine ⟨740450587718620751123009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493633725145747167415339 740450587718620751123009)
          ·
            refine ⟨555337940788965563342257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740450587718620751123009 555337940788965563342257)
            ·
              refine ⟨416503455591724172506693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555337940788965563342257 416503455591724172506693)
              ·
                refine ⟨78094397923448282345005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416503455591724172506693 78094397923448282345005)
                ·
                  rfl

theorem cell20_513298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_513298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513298 prefixEnd_513298 := by exact prefixLift 513298
  have htrace : WordTrace (prefixWord ++ tailWord_513298) baseStart_513298 baseEnd_513298 := by
    simpa [prefixWord, tailWord_513298, baseEnd_513298] using wordTrace_append hprefix tailTrace_513298
  have hstable : (prefixWord ++ tailWord_513298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513298).length < 2 ^ (prefixWord ++ tailWord_513298).sum := by decide
  have hdescent : baseEnd_513298 < baseStart_513298 := by decide
  rcases family_descends (prefixWord ++ tailWord_513298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513312 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_513312 : Nat := 118140960795 + 513312 * 2 ^ 59
def prefixEnd_513312 : Nat := 4983230072969 + 3 ^ 40 * 513312 * 2
def baseEnd_513312 : Nat := 234289583751823020568291

theorem tailTrace_513312 : CollatzResearch.WordTrace tailWord_513312 prefixEnd_513312 234289583751823020568291 := by
  unfold tailWord_513312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361013358182882777603095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12481351144243843703470793 9361013358182882777603095)
  ·
    refine ⟨14041520037274324166404643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9361013358182882777603095 14041520037274324166404643)
    ·
      refine ⟨21062280055911486249606965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041520037274324166404643 21062280055911486249606965)
      ·
        refine ⟨1974588755241701835900653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21062280055911486249606965 1974588755241701835900653)
        ·
          refine ⟨740470783215638188462745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1974588755241701835900653 740470783215638188462745)
          ·
            refine ⟨555353087411728641347059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740470783215638188462745 555353087411728641347059)
            ·
              refine ⟨833029631117592962020589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555353087411728641347059 833029631117592962020589)
              ·
                refine ⟨312386111669097360757721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833029631117592962020589 312386111669097360757721)
                ·
                  refine ⟨234289583751823020568291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312386111669097360757721 234289583751823020568291)
                  ·
                    rfl

theorem cell20_513312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_513312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513312 prefixEnd_513312 := by exact prefixLift 513312
  have htrace : WordTrace (prefixWord ++ tailWord_513312) baseStart_513312 baseEnd_513312 := by
    simpa [prefixWord, tailWord_513312, baseEnd_513312] using wordTrace_append hprefix tailTrace_513312
  have hstable : (prefixWord ++ tailWord_513312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513312).length < 2 ^ (prefixWord ++ tailWord_513312).sum := by decide
  have hdescent : baseEnd_513312 < baseStart_513312 := by decide
  rcases family_descends (prefixWord ++ tailWord_513312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513330 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_513330 : Nat := 118140960795 + 513330 * 2 ^ 59
def prefixEnd_513330 : Nat := 4983230072969 + 3 ^ 40 * 513330 * 2
def baseEnd_513330 : Nat := 234297799442294957968217

theorem tailTrace_513330 : CollatzResearch.WordTrace tailWord_513330 prefixEnd_513330 234297799442294957968217 := by
  unfold tailWord_513330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680670807575138657340361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12481788820200369752907629 4680670807575138657340361)
  ·
    refine ⟨3510503105681353993005271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4680670807575138657340361 3510503105681353993005271)
    ·
      refine ⟨5265754658522030989507907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510503105681353993005271 5265754658522030989507907)
      ·
        refine ⟨7898631987783046484261861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265754658522030989507907 7898631987783046484261861)
        ·
          refine ⟨1480993497709321215799099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7898631987783046484261861 1480993497709321215799099)
          ·
            refine ⟨2221490246563981823698649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480993497709321215799099 2221490246563981823698649)
            ·
              refine ⟨1666117684922986367773987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221490246563981823698649 1666117684922986367773987)
              ·
                refine ⟨2499176527384479551660981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666117684922986367773987 2499176527384479551660981)
                ·
                  refine ⟨234297799442294957968217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499176527384479551660981 234297799442294957968217)
                  ·
                    rfl

theorem cell20_513330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_513330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513330 prefixEnd_513330 := by exact prefixLift 513330
  have htrace : WordTrace (prefixWord ++ tailWord_513330) baseStart_513330 baseEnd_513330 := by
    simpa [prefixWord, tailWord_513330, baseEnd_513330] using wordTrace_append hprefix tailTrace_513330
  have hstable : (prefixWord ++ tailWord_513330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513330).length < 2 ^ (prefixWord ++ tailWord_513330).sum := by decide
  have hdescent : baseEnd_513330 < baseStart_513330 := by decide
  rcases family_descends (prefixWord ++ tailWord_513330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513344 : List Nat := [2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_513344 : Nat := 118140960795 + 513344 * 2 ^ 59
def prefixEnd_513344 : Nat := 4983230072969 + 3 ^ 40 * 513344 * 2
def baseEnd_513344 : Nat := 78101396474591043833831

theorem tailTrace_513344 : CollatzResearch.WordTrace tailWord_513344 prefixEnd_513344 78101396474591043833831 := by
  unfold tailWord_513344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361596926124917510185543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12482129234833223346914057 9361596926124917510185543)
  ·
    refine ⟨14042395389187376265278315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9361596926124917510185543 14042395389187376265278315)
    ·
      refine ⟨21063593083781064397917473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14042395389187376265278315 21063593083781064397917473)
      ·
        refine ⟨15797694812835798298438105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21063593083781064397917473 15797694812835798298438105)
        ·
          refine ⟨11848271109626848723828579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15797694812835798298438105 11848271109626848723828579)
          ·
            refine ⟨17772406664440273085742869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11848271109626848723828579 17772406664440273085742869)
            ·
              refine ⟨833081562395637800894197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17772406664440273085742869 833081562395637800894197)
              ·
                refine ⟨78101396474591043833831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833081562395637800894197 78101396474591043833831)
                ·
                  rfl

theorem cell20_513344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_513344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513344 prefixEnd_513344 := by exact prefixLift 513344
  have htrace : WordTrace (prefixWord ++ tailWord_513344) baseStart_513344 baseEnd_513344 := by
    simpa [prefixWord, tailWord_513344, baseEnd_513344] using wordTrace_append hprefix tailTrace_513344
  have hstable : (prefixWord ++ tailWord_513344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513344).length < 2 ^ (prefixWord ++ tailWord_513344).sum := by decide
  have hdescent : baseEnd_513344 < baseStart_513344 := by decide
  rcases family_descends (prefixWord ++ tailWord_513344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513388 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_513388 : Nat := 118140960795 + 513388 * 2 ^ 59
def prefixEnd_513388 : Nat := 4983230072969 + 3 ^ 40 * 513388 * 2
def baseEnd_513388 : Nat := 234324272222704534034647

theorem tailTrace_513388 : CollatzResearch.WordTrace tailWord_513388 prefixEnd_513388 234324272222704534034647 := by
  unfold tailWord_513388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362399332045215267486409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12483199109393620356648545 9362399332045215267486409)
  ·
    refine ⟨7021799499033911450614807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9362399332045215267486409 7021799499033911450614807)
    ·
      refine ⟨10532699248550867175922211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021799499033911450614807 10532699248550867175922211)
      ·
        refine ⟨15799048872826300763883317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532699248550867175922211 15799048872826300763883317)
        ·
          refine ⟨1481160831827465696614061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15799048872826300763883317 1481160831827465696614061)
          ·
            refine ⟨555435311935299636230273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1481160831827465696614061 555435311935299636230273)
            ·
              refine ⟨416576483951474727172705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555435311935299636230273 416576483951474727172705)
              ·
                refine ⟨312432362963606045379529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416576483951474727172705 312432362963606045379529)
                ·
                  refine ⟨234324272222704534034647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312432362963606045379529 234324272222704534034647)
                  ·
                    rfl

theorem cell20_513388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_513388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513388 prefixEnd_513388 := by exact prefixLift 513388
  have htrace : WordTrace (prefixWord ++ tailWord_513388) baseStart_513388 baseEnd_513388 := by
    simpa [prefixWord, tailWord_513388, baseEnd_513388] using wordTrace_append hprefix tailTrace_513388
  have hstable : (prefixWord ++ tailWord_513388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513388).length < 2 ^ (prefixWord ++ tailWord_513388).sum := by decide
  have hdescent : baseEnd_513388 < baseStart_513388 := by decide
  rcases family_descends (prefixWord ++ tailWord_513388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513392 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_513392 : Nat := 118140960795 + 513392 * 2 ^ 59
def prefixEnd_513392 : Nat := 4983230072969 + 3 ^ 40 * 513392 * 2
def baseEnd_513392 : Nat := 234326097931698297901297

theorem tailTrace_513392 : CollatzResearch.WordTrace tailWord_513392 prefixEnd_513392 234326097931698297901297 := by
  unfold tailWord_513392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362472278037969609059215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12483296370717292812078953 9362472278037969609059215)
  ·
    refine ⟨14043708417056954413588823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362472278037969609059215 14043708417056954413588823)
    ·
      refine ⟨21065562625585431620383235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043708417056954413588823 21065562625585431620383235)
      ·
        refine ⟨31598343938378147430574853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065562625585431620383235 31598343938378147430574853)
        ·
          refine ⟨5924689488445902643232785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31598343938378147430574853 5924689488445902643232785)
          ·
            refine ⟨4443517116334426982424589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924689488445902643232785 4443517116334426982424589)
            ·
              refine ⟨1666318918625410118409221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443517116334426982424589 1666318918625410118409221)
              ·
                refine ⟨312434797242264397201729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1666318918625410118409221 312434797242264397201729)
                ·
                  refine ⟨234326097931698297901297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312434797242264397201729 234326097931698297901297)
                  ·
                    rfl

theorem cell20_513392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_513392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513392 prefixEnd_513392 := by exact prefixLift 513392
  have htrace : WordTrace (prefixWord ++ tailWord_513392) baseStart_513392 baseEnd_513392 := by
    simpa [prefixWord, tailWord_513392, baseEnd_513392] using wordTrace_append hprefix tailTrace_513392
  have hstable : (prefixWord ++ tailWord_513392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513392).length < 2 ^ (prefixWord ++ tailWord_513392).sum := by decide
  have hdescent : baseEnd_513392 < baseStart_513392 := by decide
  rcases family_descends (prefixWord ++ tailWord_513392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513492 : List Nat := [2, 4, 1, 2, 4, 1, 6]
def baseStart_513492 : Nat := 118140960795 + 513492 * 2 ^ 59
def prefixEnd_513492 : Nat := 4983230072969 + 3 ^ 40 * 513492 * 2
def baseEnd_513492 : Nat := 26041304517393599396395

theorem tailTrace_513492 : CollatzResearch.WordTrace tailWord_513492 prefixEnd_513492 26041304517393599396395 := by
  unfold tailWord_513492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364295927856828148379365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12485727903809104197839153 9364295927856828148379365)
  ·
    refine ⟨1755805486473155277821131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9364295927856828148379365 1755805486473155277821131)
    ·
      refine ⟨2633708229709732916731697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755805486473155277821131 2633708229709732916731697)
      ·
        refine ⟨1975281172282299687548773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2633708229709732916731697 1975281172282299687548773)
        ·
          refine ⟨370365219802931191415395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1975281172282299687548773 370365219802931191415395)
          ·
            refine ⟨555547829704396787123093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370365219802931191415395 555547829704396787123093)
            ·
              refine ⟨26041304517393599396395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 555547829704396787123093 26041304517393599396395)
              ·
                rfl

theorem cell20_513492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 6].length) (baseStart_513492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513492 prefixEnd_513492 := by exact prefixLift 513492
  have htrace : WordTrace (prefixWord ++ tailWord_513492) baseStart_513492 baseEnd_513492 := by
    simpa [prefixWord, tailWord_513492, baseEnd_513492] using wordTrace_append hprefix tailTrace_513492
  have hstable : (prefixWord ++ tailWord_513492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513492).length < 2 ^ (prefixWord ++ tailWord_513492).sum := by decide
  have hdescent : baseEnd_513492 < baseStart_513492 := by decide
  rcases family_descends (prefixWord ++ tailWord_513492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513503 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_513503 : Nat := 118140960795 + 513503 * 2 ^ 59
def prefixEnd_513503 : Nat := 4983230072969 + 3 ^ 40 * 513503 * 2
def baseEnd_513503 : Nat := 234376761356275245200843

theorem tailTrace_513503 : CollatzResearch.WordTrace tailWord_513503 prefixEnd_513503 234376761356275245200843 := by
  unfold tailWord_513503
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728993058673805175409163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12485995372449203450272775 18728993058673805175409163)
  ·
    refine ⟨28093489588010707763113745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18728993058673805175409163 28093489588010707763113745)
    ·
      refine ⟨21070117191008030822335309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28093489588010707763113745 21070117191008030822335309)
      ·
        refine ⟨7901293946628011558375741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21070117191008030822335309 7901293946628011558375741)
        ·
          refine ⟨2962985229985504334390903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7901293946628011558375741 2962985229985504334390903)
          ·
            refine ⟨4444477844978256501586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962985229985504334390903 4444477844978256501586355)
            ·
              refine ⟨6666716767467384752379533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444477844978256501586355 6666716767467384752379533)
              ·
                refine ⟨2500018787800269282142325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6666716767467384752379533 2500018787800269282142325)
                ·
                  refine ⟨234376761356275245200843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500018787800269282142325 234376761356275245200843)
                  ·
                    rfl

theorem cell20_513503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_513503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513503 prefixEnd_513503 := by exact prefixLift 513503
  have htrace : WordTrace (prefixWord ++ tailWord_513503) baseStart_513503 baseEnd_513503 := by
    simpa [prefixWord, tailWord_513503, baseEnd_513503] using wordTrace_append hprefix tailTrace_513503
  have hstable : (prefixWord ++ tailWord_513503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513503).length < 2 ^ (prefixWord ++ tailWord_513503).sum := by decide
  have hdescent : baseEnd_513503 < baseStart_513503 := by decide
  rcases family_descends (prefixWord ++ tailWord_513503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513520 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_513520 : Nat := 118140960795 + 513520 * 2 ^ 59
def prefixEnd_513520 : Nat := 4983230072969 + 3 ^ 40 * 513520 * 2
def baseEnd_513520 : Nat := 234384520619498741634107

theorem tailTrace_513520 : CollatzResearch.WordTrace tailWord_513520 prefixEnd_513520 234384520619498741634107 := by
  unfold tailWord_513520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364806549806108539389007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12486408733074811385852009 9364806549806108539389007)
  ·
    refine ⟨14047209824709162809083511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364806549806108539389007 14047209824709162809083511)
    ·
      refine ⟨21070814737063744213625267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047209824709162809083511 21070814737063744213625267)
      ·
        refine ⟨31606222105595616320437901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21070814737063744213625267 31606222105595616320437901)
        ·
          refine ⟨11852333289598356120164213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31606222105595616320437901 11852333289598356120164213)
          ·
            refine ⟨1111156245899845886265395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11852333289598356120164213 1111156245899845886265395)
            ·
              refine ⟨1666734368849768829398093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111156245899845886265395 1666734368849768829398093)
              ·
                refine ⟨625025388318663311024285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1666734368849768829398093 625025388318663311024285)
                ·
                  refine ⟨234384520619498741634107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625025388318663311024285 234384520619498741634107)
                  ·
                    rfl

theorem cell20_513520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_513520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513520 prefixEnd_513520 := by exact prefixLift 513520
  have htrace : WordTrace (prefixWord ++ tailWord_513520) baseStart_513520 baseEnd_513520 := by
    simpa [prefixWord, tailWord_513520, baseEnd_513520] using wordTrace_append hprefix tailTrace_513520
  have hstable : (prefixWord ++ tailWord_513520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513520).length < 2 ^ (prefixWord ++ tailWord_513520).sum := by decide
  have hdescent : baseEnd_513520 < baseStart_513520 := by decide
  rcases family_descends (prefixWord ++ tailWord_513520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513555 : List Nat := [1, 1, 1, 2, 1, 14]
def baseStart_513555 : Nat := 118140960795 + 513555 * 2 ^ 59
def prefixEnd_513555 : Nat := 4983230072969 + 3 ^ 40 * 513555 * 2
def baseEnd_513555 : Nat := 8681499836044228721011

theorem tailTrace_513555 : CollatzResearch.WordTrace tailWord_513555 prefixEnd_513555 8681499836044228721011 := by
  unfold tailWord_513555
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730889654485418056302119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12487259769656945370868079 18730889654485418056302119)
  ·
    refine ⟨28096334481728127084453179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18730889654485418056302119 28096334481728127084453179)
    ·
      refine ⟨42144501722592190626679769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28096334481728127084453179 42144501722592190626679769)
      ·
        refine ⟨31608376291944142970009827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42144501722592190626679769 31608376291944142970009827)
        ·
          refine ⟨47412564437916214455014741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31608376291944142970009827 47412564437916214455014741)
          ·
            refine ⟨8681499836044228721011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 47412564437916214455014741 8681499836044228721011)
            ·
              rfl

theorem cell20_513555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 14].length) (baseStart_513555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513555 prefixEnd_513555 := by exact prefixLift 513555
  have htrace : WordTrace (prefixWord ++ tailWord_513555) baseStart_513555 baseEnd_513555 := by
    simpa [prefixWord, tailWord_513555, baseEnd_513555] using wordTrace_append hprefix tailTrace_513555
  have hstable : (prefixWord ++ tailWord_513555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513555).length < 2 ^ (prefixWord ++ tailWord_513555).sum := by decide
  have hdescent : baseEnd_513555 < baseStart_513555 := by decide
  rcases family_descends (prefixWord ++ tailWord_513555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513565 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_513565 : Nat := 118140960795 + 513565 * 2 ^ 59
def prefixEnd_513565 : Nat := 4983230072969 + 3 ^ 40 * 513565 * 2
def baseEnd_513565 : Nat := 234405059845678585133923

theorem tailTrace_513565 : CollatzResearch.WordTrace tailWord_513565 prefixEnd_513565 234405059845678585133923 := by
  unfold tailWord_513565
  simp only [CollatzResearch.WordTrace]
  refine ⟨18731254384449189764166149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12487502922966126509444099 18731254384449189764166149)
  ·
    refine ⟨3512110197084223080781153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18731254384449189764166149 3512110197084223080781153)
    ·
      refine ⟨2634082647813167310585865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3512110197084223080781153 2634082647813167310585865)
      ·
        refine ⟨1975561985859875482939399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2634082647813167310585865 1975561985859875482939399)
        ·
          refine ⟨2963342978789813224409099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975561985859875482939399 2963342978789813224409099)
          ·
            refine ⟨4445014468184719836613649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963342978789813224409099 4445014468184719836613649)
            ·
              refine ⟨3333760851138539877460237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445014468184719836613649 3333760851138539877460237)
              ·
                refine ⟨1250160319176952454047589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3333760851138539877460237 1250160319176952454047589)
                ·
                  refine ⟨234405059845678585133923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250160319176952454047589 234405059845678585133923)
                  ·
                    rfl

theorem cell20_513565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_513565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513565 prefixEnd_513565 := by exact prefixLift 513565
  have htrace : WordTrace (prefixWord ++ tailWord_513565) baseStart_513565 baseEnd_513565 := by
    simpa [prefixWord, tailWord_513565, baseEnd_513565] using wordTrace_append hprefix tailTrace_513565
  have hstable : (prefixWord ++ tailWord_513565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513565).length < 2 ^ (prefixWord ++ tailWord_513565).sum := by decide
  have hdescent : baseEnd_513565 < baseStart_513565 := by decide
  rcases family_descends (prefixWord ++ tailWord_513565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513582 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_513582 : Nat := 118140960795 + 513582 * 2 ^ 59
def prefixEnd_513582 : Nat := 4983230072969 + 3 ^ 40 * 513582 * 2
def baseEnd_513582 : Nat := 234412819108902081567187

theorem tailTrace_513582 : CollatzResearch.WordTrace tailWord_513582 prefixEnd_513582 234412819108902081567187 := by
  unfold tailWord_513582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341484303173450208441875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12487916283591734445023333 2341484303173450208441875)
  ·
    refine ⟨3512226454760175312662813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341484303173450208441875 3512226454760175312662813)
    ·
      refine ⟨1317084920535065742248555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3512226454760175312662813 1317084920535065742248555)
      ·
        refine ⟨1975627380802598613372833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317084920535065742248555 1975627380802598613372833)
        ·
          refine ⟨1481720535601948960029625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975627380802598613372833 1481720535601948960029625)
          ·
            refine ⟨1111290401701461720022219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481720535601948960029625 1111290401701461720022219)
            ·
              refine ⟨1666935602552192580033329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111290401701461720022219 1666935602552192580033329)
              ·
                refine ⟨1250201701914144435024997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666935602552192580033329 1250201701914144435024997)
                ·
                  refine ⟨234412819108902081567187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250201701914144435024997 234412819108902081567187)
                  ·
                    rfl

theorem cell20_513582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_513582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513582 prefixEnd_513582 := by exact prefixLift 513582
  have htrace : WordTrace (prefixWord ++ tailWord_513582) baseStart_513582 baseEnd_513582 := by
    simpa [prefixWord, tailWord_513582, baseEnd_513582] using wordTrace_append hprefix tailTrace_513582
  have hstable : (prefixWord ++ tailWord_513582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513582).length < 2 ^ (prefixWord ++ tailWord_513582).sum := by decide
  have hdescent : baseEnd_513582 < baseStart_513582 := by decide
  rcases family_descends (prefixWord ++ tailWord_513582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513589 : List Nat := [1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_513589 : Nat := 118140960795 + 513589 * 2 ^ 59
def prefixEnd_513589 : Nat := 4983230072969 + 3 ^ 40 * 513589 * 2
def baseEnd_513589 : Nat := 78138671366547056111275

theorem tailTrace_513589 : CollatzResearch.WordTrace tailWord_513589 prefixEnd_513589 78138671366547056111275 := by
  unfold tailWord_513589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732129736362241863039821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488086490908161242026547 18732129736362241863039821)
  ·
    refine ⟨7024548651135840698639933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18732129736362241863039821 7024548651135840698639933)
    ·
      refine ⟨2634205744175940261989975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7024548651135840698639933 2634205744175940261989975)
      ·
        refine ⟨3951308616263910392984963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634205744175940261989975 3951308616263910392984963)
        ·
          refine ⟨5926962924395865589477445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951308616263910392984963 5926962924395865589477445)
          ·
            refine ⟨1111305548324224798027021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5926962924395865589477445 1111305548324224798027021)
            ·
              refine ⟨416739580621584299260133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1111305548324224798027021 416739580621584299260133)
              ·
                refine ⟨78138671366547056111275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416739580621584299260133 78138671366547056111275)
                ·
                  rfl

theorem cell20_513589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_513589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513589 prefixEnd_513589 := by exact prefixLift 513589
  have htrace : WordTrace (prefixWord ++ tailWord_513589) baseStart_513589 baseEnd_513589 := by
    simpa [prefixWord, tailWord_513589, baseEnd_513589] using wordTrace_append hprefix tailTrace_513589
  have hstable : (prefixWord ++ tailWord_513589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513589).length < 2 ^ (prefixWord ++ tailWord_513589).sum := by decide
  have hdescent : baseEnd_513589 < baseStart_513589 := by decide
  rcases family_descends (prefixWord ++ tailWord_513589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513606 : List Nat := [6, 1, 1, 1, 3, 1, 7]
def baseStart_513606 : Nat := 118140960795 + 513606 * 2 ^ 59
def prefixEnd_513606 : Nat := 4983230072969 + 3 ^ 40 * 513606 * 2
def baseEnd_513606 : Nat := 26047085929207184974121

theorem tailTrace_513606 : CollatzResearch.WordTrace tailWord_513606 prefixEnd_513606 26047085929207184974121 := by
  unfold tailWord_513606
  simp only [CollatzResearch.WordTrace]
  refine ⟨585398430540645430200271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12488499851533769177605781 585398430540645430200271)
  ·
    refine ⟨878097645810968145300407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585398430540645430200271 878097645810968145300407)
    ·
      refine ⟨1317146468716452217950611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878097645810968145300407 1317146468716452217950611)
      ·
        refine ⟨1975719703074678326925917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317146468716452217950611 1975719703074678326925917)
        ·
          refine ⟨740894888653004372597219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1975719703074678326925917 740894888653004372597219)
          ·
            refine ⟨1111342332979506558895829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740894888653004372597219 1111342332979506558895829)
            ·
              refine ⟨26047085929207184974121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1111342332979506558895829 26047085929207184974121)
              ·
                rfl

theorem cell20_513606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_513606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513606 prefixEnd_513606 := by exact prefixLift 513606
  have htrace : WordTrace (prefixWord ++ tailWord_513606) baseStart_513606 baseEnd_513606 := by
    simpa [prefixWord, tailWord_513606, baseEnd_513606] using wordTrace_append hprefix tailTrace_513606
  have hstable : (prefixWord ++ tailWord_513606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513606).length < 2 ^ (prefixWord ++ tailWord_513606).sum := by decide
  have hdescent : baseEnd_513606 < baseStart_513606 := by decide
  rcases family_descends (prefixWord ++ tailWord_513606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513613 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_513613 : Nat := 118140960795 + 513613 * 2 ^ 59
def prefixEnd_513613 : Nat := 4983230072969 + 3 ^ 40 * 513613 * 2
def baseEnd_513613 : Nat := 234426968353603751533727

theorem tailTrace_513613 : CollatzResearch.WordTrace tailWord_513613 prefixEnd_513613 234426968353603751533727 := by
  unfold tailWord_513613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733005088275293961913493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488670058850195974608995 18733005088275293961913493)
  ·
    refine ⟨878109613512904404464695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18733005088275293961913493 878109613512904404464695)
    ·
      refine ⟨1317164420269356606697043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878109613512904404464695 1317164420269356606697043)
      ·
        refine ⟨1975746630404034910045565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317164420269356606697043 1975746630404034910045565)
        ·
          refine ⟨740904986401513091267087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1975746630404034910045565 740904986401513091267087)
          ·
            refine ⟨1111357479602269636900631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740904986401513091267087 1111357479602269636900631)
            ·
              refine ⟨1667036219403404455350947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111357479602269636900631 1667036219403404455350947)
              ·
                refine ⟨2500554329105106683026421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667036219403404455350947 2500554329105106683026421)
                ·
                  refine ⟨234426968353603751533727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500554329105106683026421 234426968353603751533727)
                  ·
                    rfl

theorem cell20_513613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_513613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513613 prefixEnd_513613 := by exact prefixLift 513613
  have htrace : WordTrace (prefixWord ++ tailWord_513613) baseStart_513613 baseEnd_513613 := by
    simpa [prefixWord, tailWord_513613, baseEnd_513613] using wordTrace_append hprefix tailTrace_513613
  have hstable : (prefixWord ++ tailWord_513613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513613).length < 2 ^ (prefixWord ++ tailWord_513613).sum := by decide
  have hdescent : baseEnd_513613 < baseStart_513613 := by decide
  rcases family_descends (prefixWord ++ tailWord_513613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513617 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_513617 : Nat := 118140960795 + 513617 * 2 ^ 59
def prefixEnd_513617 : Nat := 4983230072969 + 3 ^ 40 * 513617 * 2
def baseEnd_513617 : Nat := 234428794062597515400377

theorem tailTrace_513617 : CollatzResearch.WordTrace tailWord_513617 prefixEnd_513617 234428794062597515400377 := by
  unfold tailWord_513617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733150980260802645059105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488767320173868430039403 18733150980260802645059105)
  ·
    refine ⟨14049863235195601983794329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18733150980260802645059105 14049863235195601983794329)
    ·
      refine ⟨10537397426396701487845747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14049863235195601983794329 10537397426396701487845747)
      ·
        refine ⟨15806096139595052231768621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537397426396701487845747 15806096139595052231768621)
        ·
          refine ⟨5927286052348144586913233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15806096139595052231768621 5927286052348144586913233)
          ·
            refine ⟨4445464539261108440184925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5927286052348144586913233 4445464539261108440184925)
            ·
              refine ⟨1667049202222915665069347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4445464539261108440184925 1667049202222915665069347)
              ·
                refine ⟨2500573803334373497604021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667049202222915665069347 2500573803334373497604021)
                ·
                  refine ⟨234428794062597515400377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500573803334373497604021 234428794062597515400377)
                  ·
                    rfl

theorem cell20_513617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_513617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513617 prefixEnd_513617 := by exact prefixLift 513617
  have htrace : WordTrace (prefixWord ++ tailWord_513617) baseStart_513617 baseEnd_513617 := by
    simpa [prefixWord, tailWord_513617, baseEnd_513617] using wordTrace_append hprefix tailTrace_513617
  have hstable : (prefixWord ++ tailWord_513617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513617).length < 2 ^ (prefixWord ++ tailWord_513617).sum := by decide
  have hdescent : baseEnd_513617 < baseStart_513617 := by decide
  rcases family_descends (prefixWord ++ tailWord_513617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513620 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_513620 : Nat := 118140960795 + 513620 * 2 ^ 59
def prefixEnd_513620 : Nat := 4983230072969 + 3 ^ 40 * 513620 * 2
def baseEnd_513620 : Nat := 234430163344342838300365

theorem tailTrace_513620 : CollatzResearch.WordTrace tailWord_513620 prefixEnd_513620 234430163344342838300365 := by
  unfold tailWord_513620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366630199624967078709157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12488840266166622771612209 9366630199624967078709157)
  ·
    refine ⟨1756243162429681327257967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9366630199624967078709157 1756243162429681327257967)
    ·
      refine ⟨2634364743644521990886951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1756243162429681327257967 2634364743644521990886951)
      ·
        refine ⟨3951547115466782986330427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634364743644521990886951 3951547115466782986330427)
        ·
          refine ⟨5927320673200174479495641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951547115466782986330427 5927320673200174479495641)
          ·
            refine ⟨4445490504900130859621731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5927320673200174479495641 4445490504900130859621731)
            ·
              refine ⟨6668235757350196289432597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445490504900130859621731 6668235757350196289432597)
              ·
                refine ⟨312573551125790451067153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6668235757350196289432597 312573551125790451067153)
                ·
                  refine ⟨234430163344342838300365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312573551125790451067153 234430163344342838300365)
                  ·
                    rfl

theorem cell20_513620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_513620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513620 prefixEnd_513620 := by exact prefixLift 513620
  have htrace : WordTrace (prefixWord ++ tailWord_513620) baseStart_513620 baseEnd_513620 := by
    simpa [prefixWord, tailWord_513620, baseEnd_513620] using wordTrace_append hprefix tailTrace_513620
  have hstable : (prefixWord ++ tailWord_513620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513620).length < 2 ^ (prefixWord ++ tailWord_513620).sum := by decide
  have hdescent : baseEnd_513620 < baseStart_513620 := by decide
  rcases family_descends (prefixWord ++ tailWord_513620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513648 : List Nat := [2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_513648 : Nat := 118140960795 + 513648 * 2 ^ 59
def prefixEnd_513648 : Nat := 4983230072969 + 3 ^ 40 * 513648 * 2
def baseEnd_513648 : Nat := 78147647769099728455639

theorem tailTrace_513648 : CollatzResearch.WordTrace tailWord_513648 prefixEnd_513648 78147647769099728455639 := by
  unfold tailWord_513648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9367140821574247469718799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12489521095432329959625065 9367140821574247469718799)
  ·
    refine ⟨14050711232361371204578199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9367140821574247469718799 14050711232361371204578199)
    ·
      refine ⟨21076066848542056806867299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14050711232361371204578199 21076066848542056806867299)
      ·
        refine ⟨31614100272813085210300949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21076066848542056806867299 31614100272813085210300949)
        ·
          refine ⟨1481910950288113369232857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31614100272813085210300949 1481910950288113369232857)
          ·
            refine ⟨1111433212716085026924643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481910950288113369232857 1111433212716085026924643)
            ·
              refine ⟨1667149819074127540386965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111433212716085026924643 1667149819074127540386965)
              ·
                refine ⟨78147647769099728455639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1667149819074127540386965 78147647769099728455639)
                ·
                  rfl

theorem cell20_513648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_513648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513648 prefixEnd_513648 := by exact prefixLift 513648
  have htrace : WordTrace (prefixWord ++ tailWord_513648) baseStart_513648 baseEnd_513648 := by
    simpa [prefixWord, tailWord_513648, baseEnd_513648] using wordTrace_append hprefix tailTrace_513648
  have hstable : (prefixWord ++ tailWord_513648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513648).length < 2 ^ (prefixWord ++ tailWord_513648).sum := by decide
  have hdescent : baseEnd_513648 < baseStart_513648 := by decide
  rcases family_descends (prefixWord ++ tailWord_513648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513654 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_513654 : Nat := 118140960795 + 513654 * 2 ^ 59
def prefixEnd_513654 : Nat := 4983230072969 + 3 ^ 40 * 513654 * 2
def baseEnd_513654 : Nat := 234445681870789831166893

theorem tailTrace_513654 : CollatzResearch.WordTrace tailWord_513654 prefixEnd_513654 234445681870789831166893 := by
  unfold tailWord_513654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170906280070422372759751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12489666987417838642770677 1170906280070422372759751)
  ·
    refine ⟨1756359420105633559139627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1170906280070422372759751 1756359420105633559139627)
    ·
      refine ⟨2634539130158450338709441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1756359420105633559139627 2634539130158450338709441)
      ·
        refine ⟨1975904347618837754032081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2634539130158450338709441 1975904347618837754032081)
        ·
          refine ⟨1481928260714128315524061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975904347618837754032081 1481928260714128315524061)
          ·
            refine ⟨555723097767798118321523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1481928260714128315524061 555723097767798118321523)
            ·
              refine ⟨833584646651697177482285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555723097767798118321523 833584646651697177482285)
              ·
                refine ⟨312594242494386441555857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833584646651697177482285 312594242494386441555857)
                ·
                  refine ⟨234445681870789831166893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312594242494386441555857 234445681870789831166893)
                  ·
                    rfl

theorem cell20_513654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_513654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513654 prefixEnd_513654 := by exact prefixLift 513654
  have htrace : WordTrace (prefixWord ++ tailWord_513654) baseStart_513654 baseEnd_513654 := by
    simpa [prefixWord, tailWord_513654, baseEnd_513654] using wordTrace_append hprefix tailTrace_513654
  have hstable : (prefixWord ++ tailWord_513654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513654).length < 2 ^ (prefixWord ++ tailWord_513654).sum := by decide
  have hdescent : baseEnd_513654 < baseStart_513654 := by decide
  rcases family_descends (prefixWord ++ tailWord_513654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513810 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_513810 : Nat := 118140960795 + 513810 * 2 ^ 59
def prefixEnd_513810 : Nat := 4983230072969 + 3 ^ 40 * 513810 * 2
def baseEnd_513810 : Nat := 234516884521546621966255

theorem tailTrace_513810 : CollatzResearch.WordTrace tailWord_513810 prefixEnd_513810 234516884521546621966255 := by
  unfold tailWord_513810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685047567140399151708721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12493460179041064404556589 4685047567140399151708721)
  ·
    refine ⟨3513785675355299363781541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4685047567140399151708721 3513785675355299363781541)
    ·
      refine ⟨658834814129118630709039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3513785675355299363781541 658834814129118630709039)
      ·
        refine ⟨988252221193677946063559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658834814129118630709039 988252221193677946063559)
        ·
          refine ⟨1482378331790516919095339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988252221193677946063559 1482378331790516919095339)
          ·
            refine ⟨2223567497685775378643009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482378331790516919095339 2223567497685775378643009)
            ·
              refine ⟨1667675623264331533982257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223567497685775378643009 1667675623264331533982257)
              ·
                refine ⟨1250756717448248650486693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667675623264331533982257 1250756717448248650486693)
                ·
                  refine ⟨234516884521546621966255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250756717448248650486693 234516884521546621966255)
                  ·
                    rfl

theorem cell20_513810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_513810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513810 prefixEnd_513810 := by exact prefixLift 513810
  have htrace : WordTrace (prefixWord ++ tailWord_513810) baseStart_513810 baseEnd_513810 := by
    simpa [prefixWord, tailWord_513810, baseEnd_513810] using wordTrace_append hprefix tailTrace_513810
  have hstable : (prefixWord ++ tailWord_513810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513810).length < 2 ^ (prefixWord ++ tailWord_513810).sum := by decide
  have hdescent : baseEnd_513810 < baseStart_513810 := by decide
  rcases family_descends (prefixWord ++ tailWord_513810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513844 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_513844 : Nat := 118140960795 + 513844 * 2 ^ 59
def prefixEnd_513844 : Nat := 4983230072969 + 3 ^ 40 * 513844 * 2
def baseEnd_513844 : Nat := 234532403047993614832783

theorem tailTrace_513844 : CollatzResearch.WordTrace tailWord_513844 prefixEnd_513844 234532403047993614832783 := by
  unfold tailWord_513844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370715175219210206786293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12494286900292280275715057 9370715175219210206786293)
  ·
    refine ⟨878504547676800956886215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9370715175219210206786293 878504547676800956886215)
    ·
      refine ⟨1317756821515201435329323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878504547676800956886215 1317756821515201435329323)
      ·
        refine ⟨1976635232272802152993985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317756821515201435329323 1976635232272802152993985)
        ·
          refine ⟨1482476424204601614745489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976635232272802152993985 1482476424204601614745489)
          ·
            refine ⟨1111857318153451211059117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482476424204601614745489 1111857318153451211059117)
            ·
              refine ⟨416946494307544204147169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1111857318153451211059117 416946494307544204147169)
              ·
                refine ⟨312709870730658153110377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416946494307544204147169 312709870730658153110377)
                ·
                  refine ⟨234532403047993614832783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312709870730658153110377 234532403047993614832783)
                  ·
                    rfl

theorem cell20_513844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_513844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513844 prefixEnd_513844 := by exact prefixLift 513844
  have htrace : WordTrace (prefixWord ++ tailWord_513844) baseStart_513844 baseEnd_513844 := by
    simpa [prefixWord, tailWord_513844, baseEnd_513844] using wordTrace_append hprefix tailTrace_513844
  have hstable : (prefixWord ++ tailWord_513844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513844).length < 2 ^ (prefixWord ++ tailWord_513844).sum := by decide
  have hdescent : baseEnd_513844 < baseStart_513844 := by decide
  rcases family_descends (prefixWord ++ tailWord_513844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513859 : List Nat := [1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_513859 : Nat := 118140960795 + 513859 * 2 ^ 59
def prefixEnd_513859 : Nat := 4983230072969 + 3 ^ 40 * 513859 * 2
def baseEnd_513859 : Nat := 78179749818906743110907

theorem tailTrace_513859 : CollatzResearch.WordTrace tailWord_513859 prefixEnd_513859 78179749818906743110907 := by
  unfold tailWord_513859
  simp only [CollatzResearch.WordTrace]
  refine ⟨18741977445384077975368631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12494651630256051983579087 18741977445384077975368631)
  ·
    refine ⟨28112966168076116963052947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18741977445384077975368631 28112966168076116963052947)
    ·
      refine ⟨42169449252114175444579421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28112966168076116963052947 42169449252114175444579421)
      ·
        refine ⟨15813543469542815791717283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42169449252114175444579421 15813543469542815791717283)
        ·
          refine ⟨23720315204314223687575925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813543469542815791717283 23720315204314223687575925)
          ·
            refine ⟨2223779550404458470710243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23720315204314223687575925 2223779550404458470710243)
            ·
              refine ⟨3335669325606687706065365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223779550404458470710243 3335669325606687706065365)
              ·
                refine ⟨78179749818906743110907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3335669325606687706065365 78179749818906743110907)
                ·
                  rfl

theorem cell20_513859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_513859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513859 prefixEnd_513859 := by exact prefixLift 513859
  have htrace : WordTrace (prefixWord ++ tailWord_513859) baseStart_513859 baseEnd_513859 := by
    simpa [prefixWord, tailWord_513859, baseEnd_513859] using wordTrace_append hprefix tailTrace_513859
  have hstable : (prefixWord ++ tailWord_513859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513859).length < 2 ^ (prefixWord ++ tailWord_513859).sum := by decide
  have hdescent : baseEnd_513859 < baseStart_513859 := by decide
  rcases family_descends (prefixWord ++ tailWord_513859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513876 : List Nat := [2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_513876 : Nat := 118140960795 + 513876 * 2 ^ 59
def prefixEnd_513876 : Nat := 4983230072969 + 3 ^ 40 * 513876 * 2
def baseEnd_513876 : Nat := 78182336239981241921995

theorem tailTrace_513876 : CollatzResearch.WordTrace tailWord_513876 prefixEnd_513876 78182336239981241921995 := by
  unfold tailWord_513876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371298743161244939368741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12495064990881659919158321 9371298743161244939368741)
  ·
    refine ⟨1757118514342733426131639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9371298743161244939368741 1757118514342733426131639)
    ·
      refine ⟨2635677771514100139197459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757118514342733426131639 2635677771514100139197459)
      ·
        refine ⟨3953516657271150208796189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635677771514100139197459 3953516657271150208796189)
        ·
          refine ⟨1482568746476681328298571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3953516657271150208796189 1482568746476681328298571)
          ·
            refine ⟨2223853119715021992447857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482568746476681328298571 2223853119715021992447857)
            ·
              refine ⟨1667889839786266494335893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223853119715021992447857 1667889839786266494335893)
              ·
                refine ⟨78182336239981241921995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1667889839786266494335893 78182336239981241921995)
                ·
                  rfl

theorem cell20_513876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_513876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513876 prefixEnd_513876 := by exact prefixLift 513876
  have htrace : WordTrace (prefixWord ++ tailWord_513876) baseStart_513876 baseEnd_513876 := by
    simpa [prefixWord, tailWord_513876, baseEnd_513876] using wordTrace_append hprefix tailTrace_513876
  have hstable : (prefixWord ++ tailWord_513876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513876).length < 2 ^ (prefixWord ++ tailWord_513876).sum := by decide
  have hdescent : baseEnd_513876 < baseStart_513876 := by decide
  rcases family_descends (prefixWord ++ tailWord_513876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513900 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_513900 : Nat := 118140960795 + 513900 * 2 ^ 59
def prefixEnd_513900 : Nat := 4983230072969 + 3 ^ 40 * 513900 * 2
def baseEnd_513900 : Nat := 234557962973906308965887

theorem tailTrace_513900 : CollatzResearch.WordTrace tailWord_513900 prefixEnd_513900 234557962973906308965887 := by
  unfold tailWord_513900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371736419117770988805577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12495648558823694651740769 9371736419117770988805577)
  ·
    refine ⟨7028802314338328241604183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9371736419117770988805577 7028802314338328241604183)
    ·
      refine ⟨10543203471507492362406275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028802314338328241604183 10543203471507492362406275)
      ·
        refine ⟨15814805207261238543609413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10543203471507492362406275 15814805207261238543609413)
        ·
          refine ⟨2965275976361482226926765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15814805207261238543609413 2965275976361482226926765)
          ·
            refine ⟨1111978491135555835097537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2965275976361482226926765 1111978491135555835097537)
            ·
              refine ⟨833983868351666876323153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111978491135555835097537 833983868351666876323153)
              ·
                refine ⟨625487901263750157242365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833983868351666876323153 625487901263750157242365)
                ·
                  refine ⟨234557962973906308965887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625487901263750157242365 234557962973906308965887)
                  ·
                    rfl

theorem cell20_513900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_513900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513900 prefixEnd_513900 := by exact prefixLift 513900
  have htrace : WordTrace (prefixWord ++ tailWord_513900) baseStart_513900 baseEnd_513900 := by
    simpa [prefixWord, tailWord_513900, baseEnd_513900] using wordTrace_append hprefix tailTrace_513900
  have hstable : (prefixWord ++ tailWord_513900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513900).length < 2 ^ (prefixWord ++ tailWord_513900).sum := by decide
  have hdescent : baseEnd_513900 < baseStart_513900 := by decide
  rcases family_descends (prefixWord ++ tailWord_513900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513910 : List Nat := [5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_513910 : Nat := 118140960795 + 513910 * 2 ^ 59
def prefixEnd_513910 : Nat := 4983230072969 + 3 ^ 40 * 513910 * 2
def baseEnd_513910 : Nat := 78187509082130239544171

theorem tailTrace_513910 : CollatzResearch.WordTrace tailWord_513910 prefixEnd_513910 78187509082130239544171 := by
  unfold tailWord_513910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171489848012457105342199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12495891712132875790316789 1171489848012457105342199)
  ·
    refine ⟨1757234772018685658013299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171489848012457105342199 1757234772018685658013299)
    ·
      refine ⟨2635852158028028487019949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757234772018685658013299 2635852158028028487019949)
      ·
        refine ⟨988444559260510682632481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2635852158028028487019949 988444559260510682632481)
        ·
          refine ⟨741333419445383011974361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988444559260510682632481 741333419445383011974361)
          ·
            refine ⟨556000064584037258980771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741333419445383011974361 556000064584037258980771)
            ·
              refine ⟨834000096876055888471157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556000064584037258980771 834000096876055888471157)
              ·
                refine ⟨78187509082130239544171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834000096876055888471157 78187509082130239544171)
                ·
                  rfl

theorem cell20_513910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_513910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513910 prefixEnd_513910 := by exact prefixLift 513910
  have htrace : WordTrace (prefixWord ++ tailWord_513910) baseStart_513910 baseEnd_513910 := by
    simpa [prefixWord, tailWord_513910, baseEnd_513910] using wordTrace_append hprefix tailTrace_513910
  have hstable : (prefixWord ++ tailWord_513910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513910).length < 2 ^ (prefixWord ++ tailWord_513910).sum := by decide
  have hdescent : baseEnd_513910 < baseStart_513910 := by decide
  rcases family_descends (prefixWord ++ tailWord_513910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513945 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 2]
def baseStart_513945 : Nat := 118140960795 + 513945 * 2 ^ 59
def prefixEnd_513945 : Nat := 4983230072969 + 3 ^ 40 * 513945 * 2
def baseEnd_513945 : Nat := 234578502200086152465703

theorem tailTrace_513945 : CollatzResearch.WordTrace tailWord_513945 prefixEnd_513945 234578502200086152465703 := by
  unfold tailWord_513945
  simp only [CollatzResearch.WordTrace]
  refine ⟨18745114123072514662999289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12496742748715009775332859 18745114123072514662999289)
  ·
    refine ⟨14058835592304385997249467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18745114123072514662999289 14058835592304385997249467)
    ·
      refine ⟨21088253388456578995874201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14058835592304385997249467 21088253388456578995874201)
      ·
        refine ⟨15816190041342434246905651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21088253388456578995874201 15816190041342434246905651)
        ·
          refine ⟨23724285062013651370358477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15816190041342434246905651 23724285062013651370358477)
          ·
            refine ⟨8896606898255119263884429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23724285062013651370358477 8896606898255119263884429)
            ·
              refine ⟨3336227586845669723956661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8896606898255119263884429 3336227586845669723956661)
              ·
                refine ⟨312771336266781536620937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3336227586845669723956661 312771336266781536620937)
                ·
                  refine ⟨234578502200086152465703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312771336266781536620937 234578502200086152465703)
                  ·
                    rfl

theorem cell20_513945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_513945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513945 prefixEnd_513945 := by exact prefixLift 513945
  have htrace : WordTrace (prefixWord ++ tailWord_513945) baseStart_513945 baseEnd_513945 := by
    simpa [prefixWord, tailWord_513945, baseEnd_513945] using wordTrace_append hprefix tailTrace_513945
  have hstable : (prefixWord ++ tailWord_513945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513945).length < 2 ^ (prefixWord ++ tailWord_513945).sum := by decide
  have hdescent : baseEnd_513945 < baseStart_513945 := by decide
  rcases family_descends (prefixWord ++ tailWord_513945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513976 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_513976 : Nat := 118140960795 + 513976 * 2 ^ 59
def prefixEnd_513976 : Nat := 4983230072969 + 3 ^ 40 * 513976 * 2
def baseEnd_513976 : Nat := 234592651444787822432243

theorem tailTrace_513976 : CollatzResearch.WordTrace tailWord_513976 prefixEnd_513976 234592651444787822432243 := by
  unfold tailWord_513976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373122392980103478688891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12497496523973471304918521 9373122392980103478688891)
  ·
    refine ⟨14059683589470155218033337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9373122392980103478688891 14059683589470155218033337)
    ·
      refine ⟨10544762692102616413525003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14059683589470155218033337 10544762692102616413525003)
      ·
        refine ⟨15817144038153924620287505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10544762692102616413525003 15817144038153924620287505)
        ·
          refine ⟨11862858028615443465215629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15817144038153924620287505 11862858028615443465215629)
          ·
            refine ⟨4448571760730791299455861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11862858028615443465215629 4448571760730791299455861)
            ·
              refine ⟨417053602568511684323987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4448571760730791299455861 417053602568511684323987)
              ·
                refine ⟨625580403852767526485981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417053602568511684323987 625580403852767526485981)
                ·
                  refine ⟨234592651444787822432243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625580403852767526485981 234592651444787822432243)
                  ·
                    rfl

theorem cell20_513976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_513976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513976 prefixEnd_513976 := by exact prefixLift 513976
  have htrace : WordTrace (prefixWord ++ tailWord_513976) baseStart_513976 baseEnd_513976 := by
    simpa [prefixWord, tailWord_513976, baseEnd_513976] using wordTrace_append hprefix tailTrace_513976
  have hstable : (prefixWord ++ tailWord_513976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513976).length < 2 ^ (prefixWord ++ tailWord_513976).sum := by decide
  have hdescent : baseEnd_513976 < baseStart_513976 := by decide
  rcases family_descends (prefixWord ++ tailWord_513976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514049 : List Nat := [1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_514049 : Nat := 118140960795 + 514049 * 2 ^ 59
def prefixEnd_514049 : Nat := 4983230072969 + 3 ^ 40 * 514049 * 2
def baseEnd_514049 : Nat := 78208656877974670999537

theorem tailTrace_514049 : CollatzResearch.WordTrace tailWord_514049 prefixEnd_514049 78208656877974670999537 := by
  unfold tailWord_514049
  simp only [CollatzResearch.WordTrace]
  refine ⟨18748907314695740424785201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12499271543130493616523467 18748907314695740424785201)
  ·
    refine ⟨14061680486021805318588901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18748907314695740424785201 14061680486021805318588901)
    ·
      refine ⟨2636565091129088497235419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14061680486021805318588901 2636565091129088497235419)
      ·
        refine ⟨3954847636693632745853129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636565091129088497235419 3954847636693632745853129)
        ·
          refine ⟨2966135727520224559389847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3954847636693632745853129 2966135727520224559389847)
          ·
            refine ⟨4449203591280336839084771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966135727520224559389847 4449203591280336839084771)
            ·
              refine ⟨6673805386920505258627157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449203591280336839084771 6673805386920505258627157)
              ·
                refine ⟨78208656877974670999537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6673805386920505258627157 78208656877974670999537)
                ·
                  rfl

theorem cell20_514049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_514049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514049 prefixEnd_514049 := by exact prefixLift 514049
  have htrace : WordTrace (prefixWord ++ tailWord_514049) baseStart_514049 baseEnd_514049 := by
    simpa [prefixWord, tailWord_514049, baseEnd_514049] using wordTrace_append hprefix tailTrace_514049
  have hstable : (prefixWord ++ tailWord_514049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514049).length < 2 ^ (prefixWord ++ tailWord_514049).sum := by decide
  have hdescent : baseEnd_514049 < baseStart_514049 := by decide
  rcases family_descends (prefixWord ++ tailWord_514049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514059 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 2]
def baseStart_514059 : Nat := 118140960795 + 514059 * 2 ^ 59
def prefixEnd_514059 : Nat := 4983230072969 + 3 ^ 40 * 514059 * 2
def baseEnd_514059 : Nat := 234630534906408422665237

theorem tailTrace_514059 : CollatzResearch.WordTrace tailWord_514059 prefixEnd_514059 234630534906408422665237 := by
  unfold tailWord_514059
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749272044659512132649231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12499514696439674755099487 18749272044659512132649231)
  ·
    refine ⟨28123908066989268198973847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18749272044659512132649231 28123908066989268198973847)
    ·
      refine ⟨42185862100483902298460771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28123908066989268198973847 42185862100483902298460771)
      ·
        refine ⟨63278793150725853447691157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42185862100483902298460771 63278793150725853447691157)
        ·
          refine ⟨2966193428940274380360523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63278793150725853447691157 2966193428940274380360523)
          ·
            refine ⟨4449290143410411570540785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966193428940274380360523 4449290143410411570540785)
            ·
              refine ⟨3336967607557808677905589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449290143410411570540785 3336967607557808677905589)
              ·
                refine ⟨312840713208544563553649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3336967607557808677905589 312840713208544563553649)
                ·
                  refine ⟨234630534906408422665237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312840713208544563553649 234630534906408422665237)
                  ·
                    rfl

theorem cell20_514059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2].length) (baseStart_514059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514059 prefixEnd_514059 := by exact prefixLift 514059
  have htrace : WordTrace (prefixWord ++ tailWord_514059) baseStart_514059 baseEnd_514059 := by
    simpa [prefixWord, tailWord_514059, baseEnd_514059] using wordTrace_append hprefix tailTrace_514059
  have hstable : (prefixWord ++ tailWord_514059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514059).length < 2 ^ (prefixWord ++ tailWord_514059).sum := by decide
  have hdescent : baseEnd_514059 < baseStart_514059 := by decide
  rcases family_descends (prefixWord ++ tailWord_514059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514066 : List Nat := [3, 2, 5, 10]
def baseStart_514066 : Nat := 118140960795 + 514066 * 2 ^ 59
def prefixEnd_514066 : Nat := 4983230072969 + 3 ^ 40 * 514066 * 2
def baseEnd_514066 : Nat := 965570904926532960625

theorem tailTrace_514066 : CollatzResearch.WordTrace tailWord_514066 prefixEnd_514066 965570904926532960625 := by
  unfold tailWord_514066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687381838908538082038513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12499684903756101552102701 4687381838908538082038513)
  ·
    refine ⟨3515536379181403561528885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4687381838908538082038513 3515536379181403561528885)
    ·
      refine ⟨329581535548256583893333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3515536379181403561528885 329581535548256583893333)
      ·
        refine ⟨965570904926532960625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 329581535548256583893333 965570904926532960625)
        ·
          rfl

theorem cell20_514066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 10].length) (baseStart_514066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514066 prefixEnd_514066 := by exact prefixLift 514066
  have htrace : WordTrace (prefixWord ++ tailWord_514066) baseStart_514066 baseEnd_514066 := by
    simpa [prefixWord, tailWord_514066, baseEnd_514066] using wordTrace_append hprefix tailTrace_514066
  have hstable : (prefixWord ++ tailWord_514066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514066).length < 2 ^ (prefixWord ++ tailWord_514066).sum := by decide
  have hdescent : baseEnd_514066 < baseStart_514066 := by decide
  rcases family_descends (prefixWord ++ tailWord_514066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514068 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_514068 : Nat := 118140960795 + 514068 * 2 ^ 59
def prefixEnd_514068 : Nat := 4983230072969 + 3 ^ 40 * 514068 * 2
def baseEnd_514068 : Nat := 234634642751644391365201

theorem tailTrace_514068 : CollatzResearch.WordTrace tailWord_514068 prefixEnd_514068 234634642751644391365201 := by
  unfold tailWord_514068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374800150813453334863429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12499733534417937779817905 9374800150813453334863429)
  ·
    refine ⟨1757775028277522500286893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9374800150813453334863429 1757775028277522500286893)
    ·
      refine ⟨659165635604070937607585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1757775028277522500286893 659165635604070937607585)
      ·
        refine ⟨494374226703053203205689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659165635604070937607585 494374226703053203205689)
        ·
          refine ⟨370780670027289902404267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494374226703053203205689 370780670027289902404267)
          ·
            refine ⟨556171005040934853606401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370780670027289902404267 556171005040934853606401)
            ·
              refine ⟨417128253780701140204801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556171005040934853606401 417128253780701140204801)
              ·
                refine ⟨312846190335525855153601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417128253780701140204801 312846190335525855153601)
                ·
                  refine ⟨234634642751644391365201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312846190335525855153601 234634642751644391365201)
                  ·
                    rfl

theorem cell20_514068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_514068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514068 prefixEnd_514068 := by exact prefixLift 514068
  have htrace : WordTrace (prefixWord ++ tailWord_514068) baseStart_514068 baseEnd_514068 := by
    simpa [prefixWord, tailWord_514068, baseEnd_514068] using wordTrace_append hprefix tailTrace_514068
  have hstable : (prefixWord ++ tailWord_514068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514068).length < 2 ^ (prefixWord ++ tailWord_514068).sum := by decide
  have hdescent : baseEnd_514068 < baseStart_514068 := by decide
  rcases family_descends (prefixWord ++ tailWord_514068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514076 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_514076 : Nat := 118140960795 + 514076 * 2 ^ 59
def prefixEnd_514076 : Nat := 4983230072969 + 3 ^ 40 * 514076 * 2
def baseEnd_514076 : Nat := 234638294169631919098501

theorem tailTrace_514076 : CollatzResearch.WordTrace tailWord_514076 prefixEnd_514076 234638294169631919098501 := by
  unfold tailWord_514076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374946042798962018009041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12499928057065282690678721 9374946042798962018009041)
  ·
    refine ⟨7031209532099221513506781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9374946042798962018009041 7031209532099221513506781)
    ·
      refine ⟨2636703574537208067565043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7031209532099221513506781 2636703574537208067565043)
      ·
        refine ⟨3955055361805812101347565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636703574537208067565043 3955055361805812101347565)
        ·
          refine ⟨1483145760677179538005337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3955055361805812101347565 1483145760677179538005337)
          ·
            refine ⟨1112359320507884653504003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483145760677179538005337 1112359320507884653504003)
            ·
              refine ⟨1668538980761826980256005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112359320507884653504003 1668538980761826980256005)
              ·
                refine ⟨312851058892842558798001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1668538980761826980256005 312851058892842558798001)
                ·
                  refine ⟨234638294169631919098501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312851058892842558798001 234638294169631919098501)
                  ·
                    rfl

theorem cell20_514076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_514076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514076 prefixEnd_514076 := by exact prefixLift 514076
  have htrace : WordTrace (prefixWord ++ tailWord_514076) baseStart_514076 baseEnd_514076 := by
    simpa [prefixWord, tailWord_514076, baseEnd_514076] using wordTrace_append hprefix tailTrace_514076
  have hstable : (prefixWord ++ tailWord_514076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514076).length < 2 ^ (prefixWord ++ tailWord_514076).sum := by decide
  have hdescent : baseEnd_514076 < baseStart_514076 := by decide
  rcases family_descends (prefixWord ++ tailWord_514076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514090 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_514090 : Nat := 118140960795 + 514090 * 2 ^ 59
def prefixEnd_514090 : Nat := 4983230072969 + 3 ^ 40 * 514090 * 2
def baseEnd_514090 : Nat := 234644684151110092631777

theorem tailTrace_514090 : CollatzResearch.WordTrace tailWord_514090 prefixEnd_514090 234644684151110092631777 := by
  unfold tailWord_514090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687600676886801106756931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12500268471698136284685149 4687600676886801106756931)
  ·
    refine ⟨7031401015330201660135397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687600676886801106756931 7031401015330201660135397)
    ·
      refine ⟨1318387690374412811275387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7031401015330201660135397 1318387690374412811275387)
      ·
        refine ⟨1977581535561619216913081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318387690374412811275387 1977581535561619216913081)
        ·
          refine ⟨1483186151671214412684811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977581535561619216913081 1483186151671214412684811)
          ·
            refine ⟨2224779227506821619027217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483186151671214412684811 2224779227506821619027217)
            ·
              refine ⟨1668584420630116214270413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224779227506821619027217 1668584420630116214270413)
              ·
                refine ⟨625719157736293580351405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1668584420630116214270413 625719157736293580351405)
                ·
                  refine ⟨234644684151110092631777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625719157736293580351405 234644684151110092631777)
                  ·
                    rfl

theorem cell20_514090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_514090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514090 prefixEnd_514090 := by exact prefixLift 514090
  have htrace : WordTrace (prefixWord ++ tailWord_514090) baseStart_514090 baseEnd_514090 := by
    simpa [prefixWord, tailWord_514090, baseEnd_514090] using wordTrace_append hprefix tailTrace_514090
  have hstable : (prefixWord ++ tailWord_514090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514090).length < 2 ^ (prefixWord ++ tailWord_514090).sum := by decide
  have hdescent : baseEnd_514090 < baseStart_514090 := by decide
  rcases family_descends (prefixWord ++ tailWord_514090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514100 : List Nat := [2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_514100 : Nat := 118140960795 + 514100 * 2 ^ 59
def prefixEnd_514100 : Nat := 4983230072969 + 3 ^ 40 * 514100 * 2
def baseEnd_514100 : Nat := 78216416141198167432801

theorem tailTrace_514100 : CollatzResearch.WordTrace tailWord_514100 prefixEnd_514100 78216416141198167432801 := by
  unfold tailWord_514100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375383718755488067445877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12500511625007317423261169 9375383718755488067445877)
  ·
    refine ⟨878942223633327006323051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9375383718755488067445877 878942223633327006323051)
    ·
      refine ⟨1318413335449990509484577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878942223633327006323051 1318413335449990509484577)
      ·
        refine ⟨988810001587492882113433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318413335449990509484577 988810001587492882113433)
        ·
          refine ⟨741607501190619661585075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988810001587492882113433 741607501190619661585075)
          ·
            refine ⟨1112411251785929492377613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741607501190619661585075 1112411251785929492377613)
            ·
              refine ⟨417154219419723559641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112411251785929492377613 417154219419723559641605)
              ·
                refine ⟨78216416141198167432801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417154219419723559641605 78216416141198167432801)
                ·
                  rfl

theorem cell20_514100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_514100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514100 prefixEnd_514100 := by exact prefixLift 514100
  have htrace : WordTrace (prefixWord ++ tailWord_514100) baseStart_514100 baseEnd_514100 := by
    simpa [prefixWord, tailWord_514100, baseEnd_514100] using wordTrace_append hprefix tailTrace_514100
  have hstable : (prefixWord ++ tailWord_514100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514100).length < 2 ^ (prefixWord ++ tailWord_514100).sum := by decide
  have hdescent : baseEnd_514100 < baseStart_514100 := by decide
  rcases family_descends (prefixWord ++ tailWord_514100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514135 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 2]
def baseStart_514135 : Nat := 118140960795 + 514135 * 2 ^ 59
def prefixEnd_514135 : Nat := 4983230072969 + 3 ^ 40 * 514135 * 2
def baseEnd_514135 : Nat := 234665223377289936131593

theorem tailTrace_514135 : CollatzResearch.WordTrace tailWord_514135 prefixEnd_514135 234665223377289936131593 := by
  unfold tailWord_514135
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752043992384177112415859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12501362661589451408277239 18752043992384177112415859)
  ·
    refine ⟨28128065988576265668623789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18752043992384177112415859 28128065988576265668623789)
    ·
      refine ⟨10548024745716099625733921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28128065988576265668623789 10548024745716099625733921)
      ·
        refine ⟨7911018559287074719300441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548024745716099625733921 7911018559287074719300441)
        ·
          refine ⟨5933263919465306039475331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7911018559287074719300441 5933263919465306039475331)
          ·
            refine ⟨8899895879197959059212997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933263919465306039475331 8899895879197959059212997)
            ·
              refine ⟨1668730477349617323602437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8899895879197959059212997 1668730477349617323602437)
              ·
                refine ⟨312886964503053248175457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1668730477349617323602437 312886964503053248175457)
                ·
                  refine ⟨234665223377289936131593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312886964503053248175457 234665223377289936131593)
                  ·
                    rfl

theorem cell20_514135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2].length) (baseStart_514135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514135 prefixEnd_514135 := by exact prefixLift 514135
  have htrace : WordTrace (prefixWord ++ tailWord_514135) baseStart_514135 baseEnd_514135 := by
    simpa [prefixWord, tailWord_514135, baseEnd_514135] using wordTrace_append hprefix tailTrace_514135
  have hstable : (prefixWord ++ tailWord_514135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514135).length < 2 ^ (prefixWord ++ tailWord_514135).sum := by decide
  have hdescent : baseEnd_514135 < baseStart_514135 := by decide
  rcases family_descends (prefixWord ++ tailWord_514135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514156 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_514156 : Nat := 118140960795 + 514156 * 2 ^ 59
def prefixEnd_514156 : Nat := 4983230072969 + 3 ^ 40 * 514156 * 2
def baseEnd_514156 : Nat := 234674808349507196431507

theorem tailTrace_514156 : CollatzResearch.WordTrace tailWord_514156 prefixEnd_514156 234674808349507196431507 := by
  unfold tailWord_514156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376404962654048849465161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12501873283538731799286881 9376404962654048849465161)
  ·
    refine ⟨7032303721990536637098871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9376404962654048849465161 7032303721990536637098871)
    ·
      refine ⟨10548455582985804955648307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032303721990536637098871 10548455582985804955648307)
      ·
        refine ⟨15822683374478707433472461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548455582985804955648307 15822683374478707433472461)
        ·
          refine ⟨5933506265429515287552173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15822683374478707433472461 5933506265429515287552173)
          ·
            refine ⟨2225064849536068232832065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5933506265429515287552173 2225064849536068232832065)
            ·
              refine ⟨1668798637152051174624049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225064849536068232832065 1668798637152051174624049)
              ·
                refine ⟨1251598977864038380968037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668798637152051174624049 1251598977864038380968037)
                ·
                  refine ⟨234674808349507196431507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251598977864038380968037 234674808349507196431507)
                  ·
                    rfl

theorem cell20_514156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_514156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514156 prefixEnd_514156 := by exact prefixLift 514156
  have htrace : WordTrace (prefixWord ++ tailWord_514156) baseStart_514156 baseEnd_514156 := by
    simpa [prefixWord, tailWord_514156, baseEnd_514156] using wordTrace_append hprefix tailTrace_514156
  have hstable : (prefixWord ++ tailWord_514156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514156).length < 2 ^ (prefixWord ++ tailWord_514156).sum := by decide
  have hdescent : baseEnd_514156 < baseStart_514156 := by decide
  rcases family_descends (prefixWord ++ tailWord_514156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514190 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_514190 : Nat := 118140960795 + 514190 * 2 ^ 59
def prefixEnd_514190 : Nat := 4983230072969 + 3 ^ 40 * 514190 * 2
def baseEnd_514190 : Nat := 234690326875954189298035

theorem tailTrace_514190 : CollatzResearch.WordTrace tailWord_514190 prefixEnd_514190 234690326875954189298035 := by
  unfold tailWord_514190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344256250898115188208503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12502700004789947670445349 2344256250898115188208503)
  ·
    refine ⟨3516384376347172782312755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2344256250898115188208503 3516384376347172782312755)
    ·
      refine ⟨5274576564520759173469133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516384376347172782312755 5274576564520759173469133)
      ·
        refine ⟨1977966211695284690050925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5274576564520759173469133 1977966211695284690050925)
        ·
          refine ⟨741737329385731758769097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1977966211695284690050925 741737329385731758769097)
          ·
            refine ⟨556302997039298819076823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741737329385731758769097 556302997039298819076823)
            ·
              refine ⟨834454495558948228615235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556302997039298819076823 834454495558948228615235)
              ·
                refine ⟨1251681743338422342922853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834454495558948228615235 1251681743338422342922853)
                ·
                  refine ⟨234690326875954189298035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251681743338422342922853 234690326875954189298035)
                  ·
                    rfl

theorem cell20_514190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_514190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514190 prefixEnd_514190 := by exact prefixLift 514190
  have htrace : WordTrace (prefixWord ++ tailWord_514190) baseStart_514190 baseEnd_514190 := by
    simpa [prefixWord, tailWord_514190, baseEnd_514190] using wordTrace_append hprefix tailTrace_514190
  have hstable : (prefixWord ++ tailWord_514190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514190).length < 2 ^ (prefixWord ++ tailWord_514190).sum := by decide
  have hdescent : baseEnd_514190 < baseStart_514190 := by decide
  rcases family_descends (prefixWord ++ tailWord_514190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514200 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_514200 : Nat := 118140960795 + 514200 * 2 ^ 59
def prefixEnd_514200 : Nat := 4983230072969 + 3 ^ 40 * 514200 * 2
def baseEnd_514200 : Nat := 234694891148438598964661

theorem tailTrace_514200 : CollatzResearch.WordTrace tailWord_514200 prefixEnd_514200 234694891148438598964661 := by
  unfold tailWord_514200
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377207368574346606766027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12502943158099128809021369 9377207368574346606766027)
  ·
    refine ⟨14065811052861519910149041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377207368574346606766027 14065811052861519910149041)
    ·
      refine ⟨10549358289646139932611781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14065811052861519910149041 10549358289646139932611781)
      ·
        refine ⟨1978004679308651237364709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10549358289646139932611781 1978004679308651237364709)
        ·
          refine ⟨370875877370372107005883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1978004679308651237364709 370875877370372107005883)
          ·
            refine ⟨556313816055558160508825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370875877370372107005883 556313816055558160508825)
            ·
              refine ⟨417235362041668620381619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556313816055558160508825 417235362041668620381619)
              ·
                refine ⟨625853043062502930572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417235362041668620381619 625853043062502930572429)
                ·
                  refine ⟨234694891148438598964661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625853043062502930572429 234694891148438598964661)
                  ·
                    rfl

theorem cell20_514200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_514200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514200 prefixEnd_514200 := by exact prefixLift 514200
  have htrace : WordTrace (prefixWord ++ tailWord_514200) baseStart_514200 baseEnd_514200 := by
    simpa [prefixWord, tailWord_514200, baseEnd_514200] using wordTrace_append hprefix tailTrace_514200
  have hstable : (prefixWord ++ tailWord_514200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514200).length < 2 ^ (prefixWord ++ tailWord_514200).sum := by decide
  have hdescent : baseEnd_514200 < baseStart_514200 := by decide
  rcases family_descends (prefixWord ++ tailWord_514200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514241 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 2]
def baseStart_514241 : Nat := 118140960795 + 514241 * 2 ^ 59
def prefixEnd_514241 : Nat := 4983230072969 + 3 ^ 40 * 514241 * 2
def baseEnd_514241 : Nat := 234713604665624678597827

theorem tailTrace_514241 : CollatzResearch.WordTrace tailWord_514241 prefixEnd_514241 234713604665624678597827 := by
  unfold tailWord_514241
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755910130000157215774577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12503940086666771477183051 18755910130000157215774577)
  ·
    refine ⟨14066932597500117911830933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18755910130000157215774577 14066932597500117911830933)
    ·
      refine ⟨659387465507818027117075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14066932597500117911830933 659387465507818027117075)
      ·
        refine ⟨989081198261727040675613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659387465507818027117075 989081198261727040675613)
        ·
          refine ⟨370905449348147640253355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 989081198261727040675613 370905449348147640253355)
          ·
            refine ⟨556358174022221460380033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370905449348147640253355 556358174022221460380033)
            ·
              refine ⟨417268630516666095285025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556358174022221460380033 417268630516666095285025)
              ·
                refine ⟨312951472887499571463769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417268630516666095285025 312951472887499571463769)
                ·
                  refine ⟨234713604665624678597827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312951472887499571463769 234713604665624678597827)
                  ·
                    rfl

theorem cell20_514241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_514241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514241 prefixEnd_514241 := by exact prefixLift 514241
  have htrace : WordTrace (prefixWord ++ tailWord_514241) baseStart_514241 baseEnd_514241 := by
    simpa [prefixWord, tailWord_514241, baseEnd_514241] using wordTrace_append hprefix tailTrace_514241
  have hstable : (prefixWord ++ tailWord_514241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514241).length < 2 ^ (prefixWord ++ tailWord_514241).sum := by decide
  have hdescent : baseEnd_514241 < baseStart_514241 := by decide
  rcases family_descends (prefixWord ++ tailWord_514241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514252 : List Nat := [2, 2, 1, 6, 2, 1, 1, 5]
def baseStart_514252 : Nat := 118140960795 + 514252 * 2 ^ 59
def prefixEnd_514252 : Nat := 4983230072969 + 3 ^ 40 * 514252 * 2
def baseEnd_514252 : Nat := 78239541788452509743705

theorem tailTrace_514252 : CollatzResearch.WordTrace tailWord_514252 prefixEnd_514252 78239541788452509743705 := by
  unfold tailWord_514252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378155666480153047212505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12504207555306870729616673 9378155666480153047212505)
  ·
    refine ⟨7033616749860114785409379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9378155666480153047212505 7033616749860114785409379)
    ·
      refine ⟨10550425124790172178114069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033616749860114785409379 10550425124790172178114069)
      ·
        refine ⟨494551177724539320849097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10550425124790172178114069 494551177724539320849097)
        ·
          refine ⟨370913383293404490636823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494551177724539320849097 370913383293404490636823)
          ·
            refine ⟨556370074940106735955235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370913383293404490636823 556370074940106735955235)
            ·
              refine ⟨834555112410160103932853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556370074940106735955235 834555112410160103932853)
              ·
                refine ⟨78239541788452509743705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834555112410160103932853 78239541788452509743705)
                ·
                  rfl

theorem cell20_514252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_514252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514252 prefixEnd_514252 := by exact prefixLift 514252
  have htrace : WordTrace (prefixWord ++ tailWord_514252) baseStart_514252 baseEnd_514252 := by
    simpa [prefixWord, tailWord_514252, baseEnd_514252] using wordTrace_append hprefix tailTrace_514252
  have hstable : (prefixWord ++ tailWord_514252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514252).length < 2 ^ (prefixWord ++ tailWord_514252).sum := by decide
  have hdescent : baseEnd_514252 < baseStart_514252 := by decide
  rcases family_descends (prefixWord ++ tailWord_514252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514284 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_514284 : Nat := 118140960795 + 514284 * 2 ^ 59
def prefixEnd_514284 : Nat := 4983230072969 + 3 ^ 40 * 514284 * 2
def baseEnd_514284 : Nat := 234733231037307640164317

theorem tailTrace_514284 : CollatzResearch.WordTrace tailWord_514284 prefixEnd_514284 234733231037307640164317 := by
  unfold tailWord_514284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378739234422187779794953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12504985645896250373059937 9378739234422187779794953)
  ·
    refine ⟨7034054425816640834846215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9378739234422187779794953 7034054425816640834846215)
    ·
      refine ⟨10551081638724961252269323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034054425816640834846215 10551081638724961252269323)
      ·
        refine ⟨15826622458087441878403985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10551081638724961252269323 15826622458087441878403985)
        ·
          refine ⟨11869966843565581408802989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15826622458087441878403985 11869966843565581408802989)
          ·
            refine ⟨4451237566337093028301121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11869966843565581408802989 4451237566337093028301121)
            ·
              refine ⟨3338428174752819771225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451237566337093028301121 3338428174752819771225841)
              ·
                refine ⟨2503821131064614828419381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338428174752819771225841 2503821131064614828419381)
                ·
                  refine ⟨234733231037307640164317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2503821131064614828419381 234733231037307640164317)
                  ·
                    rfl

theorem cell20_514284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_514284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514284 prefixEnd_514284 := by exact prefixLift 514284
  have htrace : WordTrace (prefixWord ++ tailWord_514284) baseStart_514284 baseEnd_514284 := by
    simpa [prefixWord, tailWord_514284, baseEnd_514284] using wordTrace_append hprefix tailTrace_514284
  have hstable : (prefixWord ++ tailWord_514284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514284).length < 2 ^ (prefixWord ++ tailWord_514284).sum := by decide
  have hdescent : baseEnd_514284 < baseStart_514284 := by decide
  rcases family_descends (prefixWord ++ tailWord_514284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514287 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 2]
def baseStart_514287 : Nat := 118140960795 + 514287 * 2 ^ 59
def prefixEnd_514287 : Nat := 4983230072969 + 3 ^ 40 * 514287 * 2
def baseEnd_514287 : Nat := 234734600319052963064305

theorem tailTrace_514287 : CollatzResearch.WordTrace tailWord_514287 prefixEnd_514287 234734600319052963064305 := by
  unfold tailWord_514287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18757587887833507071949115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12505058591889004714632743 18757587887833507071949115)
  ·
    refine ⟨28136381831750260607923673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18757587887833507071949115 28136381831750260607923673)
    ·
      refine ⟨21102286373812695455942755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28136381831750260607923673 21102286373812695455942755)
      ·
        refine ⟨31653429560719043183914133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21102286373812695455942755 31653429560719043183914133)
        ·
          refine ⟨1483754510658705149245975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31653429560719043183914133 1483754510658705149245975)
          ·
            refine ⟨2225631765988057723868963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483754510658705149245975 2225631765988057723868963)
            ·
              refine ⟨3338447648982086585803445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225631765988057723868963 3338447648982086585803445)
              ·
                refine ⟨312979467092070617419073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3338447648982086585803445 312979467092070617419073)
                ·
                  refine ⟨234734600319052963064305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312979467092070617419073 234734600319052963064305)
                  ·
                    rfl

theorem cell20_514287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2].length) (baseStart_514287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514287 prefixEnd_514287 := by exact prefixLift 514287
  have htrace : WordTrace (prefixWord ++ tailWord_514287) baseStart_514287 baseEnd_514287 := by
    simpa [prefixWord, tailWord_514287, baseEnd_514287] using wordTrace_append hprefix tailTrace_514287
  have hstable : (prefixWord ++ tailWord_514287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514287).length < 2 ^ (prefixWord ++ tailWord_514287).sum := by decide
  have hdescent : baseEnd_514287 < baseStart_514287 := by decide
  rcases family_descends (prefixWord ++ tailWord_514287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514291 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_514291 : Nat := 118140960795 + 514291 * 2 ^ 59
def prefixEnd_514291 : Nat := 4983230072969 + 3 ^ 40 * 514291 * 2
def baseEnd_514291 : Nat := 234736426028046726930955

theorem tailTrace_514291 : CollatzResearch.WordTrace tailWord_514291 prefixEnd_514291 234736426028046726930955 := by
  unfold tailWord_514291
  simp only [CollatzResearch.WordTrace]
  refine ⟨18757733779819015755094727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12505155853212677170063151 18757733779819015755094727)
  ·
    refine ⟨28136600669728523632642091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18757733779819015755094727 28136600669728523632642091)
    ·
      refine ⟨42204901004592785448963137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28136600669728523632642091 42204901004592785448963137)
      ·
        refine ⟨31653675753444589086722353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42204901004592785448963137 31653675753444589086722353)
        ·
          refine ⟨23740256815083441815041765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31653675753444589086722353 23740256815083441815041765)
          ·
            refine ⟨4451298152828145340320331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23740256815083441815041765 4451298152828145340320331)
            ·
              refine ⟨6676947229242218010480497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451298152828145340320331 6676947229242218010480497)
              ·
                refine ⟨5007710421931663507860373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6676947229242218010480497 5007710421931663507860373)
                ·
                  refine ⟨234736426028046726930955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5007710421931663507860373 234736426028046726930955)
                  ·
                    rfl

theorem cell20_514291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_514291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514291 prefixEnd_514291 := by exact prefixLift 514291
  have htrace : WordTrace (prefixWord ++ tailWord_514291) baseStart_514291 baseEnd_514291 := by
    simpa [prefixWord, tailWord_514291, baseEnd_514291] using wordTrace_append hprefix tailTrace_514291
  have hstable : (prefixWord ++ tailWord_514291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514291).length < 2 ^ (prefixWord ++ tailWord_514291).sum := by decide
  have hdescent : baseEnd_514291 < baseStart_514291 := by decide
  rcases family_descends (prefixWord ++ tailWord_514291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514318 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_514318 : Nat := 118140960795 + 514318 * 2 ^ 59
def prefixEnd_514318 : Nat := 4983230072969 + 3 ^ 40 * 514318 * 2
def baseEnd_514318 : Nat := 234748749563754633030845

theorem tailTrace_514318 : CollatzResearch.WordTrace tailWord_514318 prefixEnd_514318 234748749563754633030845 := by
  unfold tailWord_514318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344839818840149920790951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12505812367147466244218405 2344839818840149920790951)
  ·
    refine ⟨3517259728260224881186427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2344839818840149920790951 3517259728260224881186427)
    ·
      refine ⟨5275889592390337321779641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517259728260224881186427 5275889592390337321779641)
      ·
        refine ⟨3956917194292752991334731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5275889592390337321779641 3956917194292752991334731)
        ·
          refine ⟨5935375791439129487002097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956917194292752991334731 5935375791439129487002097)
          ·
            refine ⟨4451531843579347115251573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935375791439129487002097 4451531843579347115251573)
            ·
              refine ⟨417331110335563792054835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4451531843579347115251573 417331110335563792054835)
              ·
                refine ⟨625996665503345688082253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417331110335563792054835 625996665503345688082253)
                ·
                  refine ⟨234748749563754633030845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625996665503345688082253 234748749563754633030845)
                  ·
                    rfl

theorem cell20_514318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_514318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514318 prefixEnd_514318 := by exact prefixLift 514318
  have htrace : WordTrace (prefixWord ++ tailWord_514318) baseStart_514318 baseEnd_514318 := by
    simpa [prefixWord, tailWord_514318, baseEnd_514318] using wordTrace_append hprefix tailTrace_514318
  have hstable : (prefixWord ++ tailWord_514318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514318).length < 2 ^ (prefixWord ++ tailWord_514318).sum := by decide
  have hdescent : baseEnd_514318 < baseStart_514318 := by decide
  rcases family_descends (prefixWord ++ tailWord_514318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514349 : List Nat := [1, 5, 3, 1, 2, 2, 6]
def baseStart_514349 : Nat := 118140960795 + 514349 * 2 ^ 59
def prefixEnd_514349 : Nat := 4983230072969 + 3 ^ 40 * 514349 * 2
def baseEnd_514349 : Nat := 26084766534272922555265

theorem tailTrace_514349 : CollatzResearch.WordTrace tailWord_514349 prefixEnd_514349 26084766534272922555265 := by
  unfold tailWord_514349
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759849213608891660706101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12506566142405927773804067 18759849213608891660706101)
  ·
    refine ⟨1758735863775833593191197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18759849213608891660706101 1758735863775833593191197)
    ·
      refine ⟨659525948915937597446699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1758735863775833593191197 659525948915937597446699)
      ·
        refine ⟨989288923373906396170049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659525948915937597446699 989288923373906396170049)
        ·
          refine ⟨741966692530429797127537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989288923373906396170049 741966692530429797127537)
          ·
            refine ⟨556475019397822347845653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741966692530429797127537 556475019397822347845653)
            ·
              refine ⟨26084766534272922555265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 556475019397822347845653 26084766534272922555265)
              ·
                rfl

theorem cell20_514349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_514349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514349 prefixEnd_514349 := by exact prefixLift 514349
  have htrace : WordTrace (prefixWord ++ tailWord_514349) baseStart_514349 baseEnd_514349 := by
    simpa [prefixWord, tailWord_514349, baseEnd_514349] using wordTrace_append hprefix tailTrace_514349
  have hstable : (prefixWord ++ tailWord_514349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514349).length < 2 ^ (prefixWord ++ tailWord_514349).sum := by decide
  have hdescent : baseEnd_514349 < baseStart_514349 := by decide
  rcases family_descends (prefixWord ++ tailWord_514349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514360 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_514360 : Nat := 118140960795 + 514360 * 2 ^ 59
def prefixEnd_514360 : Nat := 4983230072969 + 3 ^ 40 * 514360 * 2
def baseEnd_514360 : Nat := 234767919508189153630673

theorem tailTrace_514360 : CollatzResearch.WordTrace tailWord_514360 prefixEnd_514360 234767919508189153630673 := by
  unfold tailWord_514360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380125208284520269678267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12506833611046027026237689 9380125208284520269678267)
  ·
    refine ⟨14070187812426780404517401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9380125208284520269678267 14070187812426780404517401)
    ·
      refine ⟨10552640859320085303388051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14070187812426780404517401 10552640859320085303388051)
      ·
        refine ⟨15828961288980127955082077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10552640859320085303388051 15828961288980127955082077)
        ·
          refine ⟨5935860483367547983155779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15828961288980127955082077 5935860483367547983155779)
          ·
            refine ⟨8903790725051321974733669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935860483367547983155779 8903790725051321974733669)
            ·
              refine ⟨1669460760947122870262563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8903790725051321974733669 1669460760947122870262563)
              ·
                refine ⟨2504191141420684305393845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669460760947122870262563 2504191141420684305393845)
                ·
                  refine ⟨234767919508189153630673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2504191141420684305393845 234767919508189153630673)
                  ·
                    rfl

theorem cell20_514360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_514360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514360 prefixEnd_514360 := by exact prefixLift 514360
  have htrace : WordTrace (prefixWord ++ tailWord_514360) baseStart_514360 baseEnd_514360 := by
    simpa [prefixWord, tailWord_514360, baseEnd_514360] using wordTrace_append hprefix tailTrace_514360
  have hstable : (prefixWord ++ tailWord_514360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514360).length < 2 ^ (prefixWord ++ tailWord_514360).sum := by decide
  have hdescent : baseEnd_514360 < baseStart_514360 := by decide
  rcases family_descends (prefixWord ++ tailWord_514360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514412 : List Nat := [2, 2, 1, 1, 14]
def baseStart_514412 : Nat := 118140960795 + 514412 * 2 ^ 59
def prefixEnd_514412 : Nat := 4983230072969 + 3 ^ 40 * 514412 * 2
def baseEnd_514412 : Nat := 2898662391668001035767

theorem tailTrace_514412 : CollatzResearch.WordTrace tailWord_514412 prefixEnd_514412 2898662391668001035767 := by
  unfold tailWord_514412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381073506190326710124745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12508098008253768946832993 9381073506190326710124745)
  ·
    refine ⟨7035805129642745032593559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9381073506190326710124745 7035805129642745032593559)
    ·
      refine ⟨10553707694464117548890339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7035805129642745032593559 10553707694464117548890339)
      ·
        refine ⟨15830561541696176323335509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10553707694464117548890339 15830561541696176323335509)
        ·
          refine ⟨2898662391668001035767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15830561541696176323335509 2898662391668001035767)
          ·
            rfl

theorem cell20_514412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 14].length) (baseStart_514412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514412 prefixEnd_514412 := by exact prefixLift 514412
  have htrace : WordTrace (prefixWord ++ tailWord_514412) baseStart_514412 baseEnd_514412 := by
    simpa [prefixWord, tailWord_514412, baseEnd_514412] using wordTrace_append hprefix tailTrace_514412
  have hstable : (prefixWord ++ tailWord_514412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514412).length < 2 ^ (prefixWord ++ tailWord_514412).sum := by decide
  have hdescent : baseEnd_514412 < baseStart_514412 := by decide
  rcases family_descends (prefixWord ++ tailWord_514412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514418 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_514418 : Nat := 118140960795 + 514418 * 2 ^ 59
def prefixEnd_514418 : Nat := 4983230072969 + 3 ^ 40 * 514418 * 2
def baseEnd_514418 : Nat := 234794392288598729697103

theorem tailTrace_514418 : CollatzResearch.WordTrace tailWord_514418 prefixEnd_514418 234794392288598729697103 := by
  unfold tailWord_514418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690591462589729111241977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12508243900239277629978605 4690591462589729111241977)
  ·
    refine ⟨3517943596942296833431483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4690591462589729111241977 3517943596942296833431483)
    ·
      refine ⟨5276915395413445250147225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517943596942296833431483 5276915395413445250147225)
      ·
        refine ⟨3957686546560083937610419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5276915395413445250147225 3957686546560083937610419)
        ·
          refine ⟨5936529819840125906415629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957686546560083937610419 5936529819840125906415629)
          ·
            refine ⟨2226198682440047214905861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5936529819840125906415629 2226198682440047214905861)
            ·
              refine ⟨417412252957508852794849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2226198682440047214905861 417412252957508852794849)
              ·
                refine ⟨313059189718131639596137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417412252957508852794849 313059189718131639596137)
                ·
                  refine ⟨234794392288598729697103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313059189718131639596137 234794392288598729697103)
                  ·
                    rfl

theorem cell20_514418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_514418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514418 prefixEnd_514418 := by exact prefixLift 514418
  have htrace : WordTrace (prefixWord ++ tailWord_514418) baseStart_514418 baseEnd_514418 := by
    simpa [prefixWord, tailWord_514418, baseEnd_514418] using wordTrace_append hprefix tailTrace_514418
  have hstable : (prefixWord ++ tailWord_514418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514418).length < 2 ^ (prefixWord ++ tailWord_514418).sum := by decide
  have hdescent : baseEnd_514418 < baseStart_514418 := by decide
  rcases family_descends (prefixWord ++ tailWord_514418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514429 : List Nat := [1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_514429 : Nat := 118140960795 + 514429 * 2 ^ 59
def prefixEnd_514429 : Nat := 4983230072969 + 3 ^ 40 * 514429 * 2
def baseEnd_514429 : Nat := 78266470996110526776797

theorem tailTrace_514429 : CollatzResearch.WordTrace tailWord_514429 prefixEnd_514429 78266470996110526776797 := by
  unfold tailWord_514429
  simp only [CollatzResearch.WordTrace]
  refine ⟨18762767053319065323618341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12508511368879376882412227 18762767053319065323618341)
  ·
    refine ⟨3518018822497324748178439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18762767053319065323618341 3518018822497324748178439)
    ·
      refine ⟨5277028233745987122267659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518018822497324748178439 5277028233745987122267659)
      ·
        refine ⟨7915542350618980683401489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277028233745987122267659 7915542350618980683401489)
        ·
          refine ⟨5936656762964235512551117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7915542350618980683401489 5936656762964235512551117)
          ·
            refine ⟨2226246286111588317206669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5936656762964235512551117 2226246286111588317206669)
            ·
              refine ⟨834842357291845618952501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2226246286111588317206669 834842357291845618952501)
              ·
                refine ⟨78266470996110526776797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834842357291845618952501 78266470996110526776797)
                ·
                  rfl

theorem cell20_514429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_514429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514429 prefixEnd_514429 := by exact prefixLift 514429
  have htrace : WordTrace (prefixWord ++ tailWord_514429) baseStart_514429 baseEnd_514429 := by
    simpa [prefixWord, tailWord_514429, baseEnd_514429] using wordTrace_append hprefix tailTrace_514429
  have hstable : (prefixWord ++ tailWord_514429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514429).length < 2 ^ (prefixWord ++ tailWord_514429).sum := by decide
  have hdescent : baseEnd_514429 < baseStart_514429 := by decide
  rcases family_descends (prefixWord ++ tailWord_514429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514443 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_514443 : Nat := 118140960795 + 514443 * 2 ^ 59
def prefixEnd_514443 : Nat := 4983230072969 + 3 ^ 40 * 514443 * 2
def baseEnd_514443 : Nat := 234805802969809753863667

theorem tailTrace_514443 : CollatzResearch.WordTrace tailWord_514443 prefixEnd_514443 234805802969809753863667 := by
  unfold tailWord_514443
  simp only [CollatzResearch.WordTrace]
  refine ⟨18763277675268345714627983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12508851783512230476418655 18763277675268345714627983)
  ·
    refine ⟨28144916512902518571941975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18763277675268345714627983 28144916512902518571941975)
    ·
      refine ⟨42217374769353777857912963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28144916512902518571941975 42217374769353777857912963)
      ·
        refine ⟨63326062154030666786869445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42217374769353777857912963 63326062154030666786869445)
        ·
          refine ⟨11873636653880750022538021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63326062154030666786869445 11873636653880750022538021)
          ·
            refine ⟨2226306872602640629225879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11873636653880750022538021 2226306872602640629225879)
            ·
              refine ⟨3339460308903960943838819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226306872602640629225879 3339460308903960943838819)
              ·
                refine ⟨5009190463355941415758229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339460308903960943838819 5009190463355941415758229)
                ·
                  refine ⟨234805802969809753863667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5009190463355941415758229 234805802969809753863667)
                  ·
                    rfl

theorem cell20_514443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_514443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514443 prefixEnd_514443 := by exact prefixLift 514443
  have htrace : WordTrace (prefixWord ++ tailWord_514443) baseStart_514443 baseEnd_514443 := by
    simpa [prefixWord, tailWord_514443, baseEnd_514443] using wordTrace_append hprefix tailTrace_514443
  have hstable : (prefixWord ++ tailWord_514443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514443).length < 2 ^ (prefixWord ++ tailWord_514443).sum := by decide
  have hdescent : baseEnd_514443 < baseStart_514443 := by decide
  rcases family_descends (prefixWord ++ tailWord_514443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514456 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_514456 : Nat := 118140960795 + 514456 * 2 ^ 59
def prefixEnd_514456 : Nat := 4983230072969 + 3 ^ 40 * 514456 * 2
def baseEnd_514456 : Nat := 234811736524039486430281

theorem tailTrace_514456 : CollatzResearch.WordTrace tailWord_514456 prefixEnd_514456 234811736524039486430281 := by
  unfold tailWord_514456
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381875912110624467425611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12509167882814165956567481 9381875912110624467425611)
  ·
    refine ⟨14072813868165936701138417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9381875912110624467425611 14072813868165936701138417)
    ·
      refine ⟨10554610401124452525853813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14072813868165936701138417 10554610401124452525853813)
      ·
        refine ⟨989494725105417424298795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10554610401124452525853813 989494725105417424298795)
        ·
          refine ⟨1484242087658126136448193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989494725105417424298795 1484242087658126136448193)
          ·
            refine ⟨1113181565743594602336145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484242087658126136448193 1113181565743594602336145)
            ·
              refine ⟨834886174307695951752109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113181565743594602336145 834886174307695951752109)
              ·
                refine ⟨313082315365385981907041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 834886174307695951752109 313082315365385981907041)
                ·
                  refine ⟨234811736524039486430281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313082315365385981907041 234811736524039486430281)
                  ·
                    rfl

theorem cell20_514456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_514456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514456 prefixEnd_514456 := by exact prefixLift 514456
  have htrace : WordTrace (prefixWord ++ tailWord_514456) baseStart_514456 baseEnd_514456 := by
    simpa [prefixWord, tailWord_514456, baseEnd_514456] using wordTrace_append hprefix tailTrace_514456
  have hstable : (prefixWord ++ tailWord_514456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514456).length < 2 ^ (prefixWord ++ tailWord_514456).sum := by decide
  have hdescent : baseEnd_514456 < baseStart_514456 := by decide
  rcases family_descends (prefixWord ++ tailWord_514456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514488 : List Nat := [2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_514488 : Nat := 118140960795 + 514488 * 2 ^ 59
def prefixEnd_514488 : Nat := 4983230072969 + 3 ^ 40 * 514488 * 2
def baseEnd_514488 : Nat := 78275447398663199121161

theorem tailTrace_514488 : CollatzResearch.WordTrace tailWord_514488 prefixEnd_514488 78275447398663199121161 := by
  unfold tailWord_514488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382459480052659200008059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12509945973403545600010745 9382459480052659200008059)
  ·
    refine ⟨14073689220078988800012089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9382459480052659200008059 14073689220078988800012089)
    ·
      refine ⟨10555266915059241600009067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14073689220078988800012089 10555266915059241600009067)
      ·
        refine ⟨15832900372588862400013601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555266915059241600009067 15832900372588862400013601)
        ·
          refine ⟨11874675279441646800010201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15832900372588862400013601 11874675279441646800010201)
          ·
            refine ⟨8906006459581235100007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11874675279441646800010201 8906006459581235100007651)
            ·
              refine ⟨13359009689371852650011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906006459581235100007651 13359009689371852650011477)
              ·
                refine ⟨78275447398663199121161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13359009689371852650011477 78275447398663199121161)
                ·
                  rfl

theorem cell20_514488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_514488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514488 prefixEnd_514488 := by exact prefixLift 514488
  have htrace : WordTrace (prefixWord ++ tailWord_514488) baseStart_514488 baseEnd_514488 := by
    simpa [prefixWord, tailWord_514488, baseEnd_514488] using wordTrace_append hprefix tailTrace_514488
  have hstable : (prefixWord ++ tailWord_514488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514488).length < 2 ^ (prefixWord ++ tailWord_514488).sum := by decide
  have hdescent : baseEnd_514488 < baseStart_514488 := by decide
  rcases family_descends (prefixWord ++ tailWord_514488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514497 : List Nat := [1, 2, 7, 1, 1, 2, 2, 4]
def baseStart_514497 : Nat := 118140960795 + 514497 * 2 ^ 59
def prefixEnd_514497 : Nat := 4983230072969 + 3 ^ 40 * 514497 * 2
def baseEnd_514497 : Nat := 78276816680408522021149

theorem tailTrace_514497 : CollatzResearch.WordTrace tailWord_514497 prefixEnd_514497 78276816680408522021149 := by
  unfold tailWord_514497
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765247217072712937093745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12510164811381808624729163 18765247217072712937093745)
  ·
    refine ⟨14073935412804534702820309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18765247217072712937093745 14073935412804534702820309)
    ·
      refine ⟨329857861237606282097351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14073935412804534702820309 329857861237606282097351)
      ·
        refine ⟨494786791856409423146027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329857861237606282097351 494786791856409423146027)
        ·
          refine ⟨742180187784614134719041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494786791856409423146027 742180187784614134719041)
          ·
            refine ⟨556635140838460601039281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742180187784614134719041 556635140838460601039281)
            ·
              refine ⟨417476355628845450779461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556635140838460601039281 417476355628845450779461)
              ·
                refine ⟨78276816680408522021149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417476355628845450779461 78276816680408522021149)
                ·
                  rfl

theorem cell20_514497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_514497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514497 prefixEnd_514497 := by exact prefixLift 514497
  have htrace : WordTrace (prefixWord ++ tailWord_514497) baseStart_514497 baseEnd_514497 := by
    simpa [prefixWord, tailWord_514497, baseEnd_514497] using wordTrace_append hprefix tailTrace_514497
  have hstable : (prefixWord ++ tailWord_514497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514497).length < 2 ^ (prefixWord ++ tailWord_514497).sum := by decide
  have hdescent : baseEnd_514497 < baseStart_514497 := by decide
  rcases family_descends (prefixWord ++ tailWord_514497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514505 : List Nat := [1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_514505 : Nat := 118140960795 + 514505 * 2 ^ 59
def prefixEnd_514505 : Nat := 4983230072969 + 3 ^ 40 * 514505 * 2
def baseEnd_514505 : Nat := 78278033819737697932249

theorem tailTrace_514505 : CollatzResearch.WordTrace tailWord_514505 prefixEnd_514505 78278033819737697932249 := by
  unfold tailWord_514505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765539001043730303384969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12510359334029153535589979 18765539001043730303384969)
  ·
    refine ⟨14074154250782797727538727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18765539001043730303384969 14074154250782797727538727)
    ·
      refine ⟨21111231376174196591308091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074154250782797727538727 21111231376174196591308091)
      ·
        refine ⟨31666847064261294886962137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111231376174196591308091 31666847064261294886962137)
        ·
          refine ⟨23750135298195971165221603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31666847064261294886962137 23750135298195971165221603)
          ·
            refine ⟨35625202947293956747832405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23750135298195971165221603 35625202947293956747832405)
            ·
              refine ⟨417482847038601055638661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 35625202947293956747832405 417482847038601055638661)
              ·
                refine ⟨78278033819737697932249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417482847038601055638661 78278033819737697932249)
                ·
                  rfl

theorem cell20_514505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_514505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514505 prefixEnd_514505 := by exact prefixLift 514505
  have htrace : WordTrace (prefixWord ++ tailWord_514505) baseStart_514505 baseEnd_514505 := by
    simpa [prefixWord, tailWord_514505, baseEnd_514505] using wordTrace_append hprefix tailTrace_514505
  have hstable : (prefixWord ++ tailWord_514505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514505).length < 2 ^ (prefixWord ++ tailWord_514505).sum := by decide
  have hdescent : baseEnd_514505 < baseStart_514505 := by decide
  rcases family_descends (prefixWord ++ tailWord_514505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514536 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_514536 : Nat := 118140960795 + 514536 * 2 ^ 59
def prefixEnd_514536 : Nat := 4983230072969 + 3 ^ 40 * 514536 * 2
def baseEnd_514536 : Nat := 234848250703914763763287

theorem tailTrace_514536 : CollatzResearch.WordTrace tailWord_514536 prefixEnd_514536 234848250703914763763287 := by
  unfold tailWord_514536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383334831965711298881731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12511113109287615065175641 9383334831965711298881731)
  ·
    refine ⟨14075002247948566948322597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383334831965711298881731 14075002247948566948322597)
    ·
      refine ⟨2639062921490356302810487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14075002247948566948322597 2639062921490356302810487)
      ·
        refine ⟨3958594382235534454215731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639062921490356302810487 3958594382235534454215731)
        ·
          refine ⟨5937891573353301681323597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958594382235534454215731 5937891573353301681323597)
          ·
            refine ⟨2226709340007488130496349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5937891573353301681323597 2226709340007488130496349)
            ·
              refine ⟨835016002502808048936131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2226709340007488130496349 835016002502808048936131)
              ·
                refine ⟨1252524003754212073404197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835016002502808048936131 1252524003754212073404197)
                ·
                  refine ⟨234848250703914763763287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252524003754212073404197 234848250703914763763287)
                  ·
                    rfl

theorem cell20_514536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_514536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514536 prefixEnd_514536 := by exact prefixLift 514536
  have htrace : WordTrace (prefixWord ++ tailWord_514536) baseStart_514536 baseEnd_514536 := by
    simpa [prefixWord, tailWord_514536, baseEnd_514536] using wordTrace_append hprefix tailTrace_514536
  have hstable : (prefixWord ++ tailWord_514536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514536).length < 2 ^ (prefixWord ++ tailWord_514536).sum := by decide
  have hdescent : baseEnd_514536 < baseStart_514536 := by decide
  rcases family_descends (prefixWord ++ tailWord_514536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514546 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_514546 : Nat := 118140960795 + 514546 * 2 ^ 59
def prefixEnd_514546 : Nat := 4983230072969 + 3 ^ 40 * 514546 * 2
def baseEnd_514546 : Nat := 234852814976399173429913

theorem tailTrace_514546 : CollatzResearch.WordTrace tailWord_514546 prefixEnd_514546 234852814976399173429913 := by
  unfold tailWord_514546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691758598473798576406873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12511356262596796203751661 4691758598473798576406873)
  ·
    refine ⟨3518818948855348932305155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4691758598473798576406873 3518818948855348932305155)
    ·
      refine ⟨5278228423283023398457733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518818948855348932305155 5278228423283023398457733)
      ·
        refine ⟨989667829365566887210825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5278228423283023398457733 989667829365566887210825)
        ·
          refine ⟨742250872024175165408119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989667829365566887210825 742250872024175165408119)
          ·
            refine ⟨1113376308036262748112179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742250872024175165408119 1113376308036262748112179)
            ·
              refine ⟨1670064462054394122168269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113376308036262748112179 1670064462054394122168269)
              ·
                refine ⟨626274173270397795813101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1670064462054394122168269 626274173270397795813101)
                ·
                  refine ⟨234852814976399173429913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626274173270397795813101 234852814976399173429913)
                  ·
                    rfl

theorem cell20_514546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_514546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514546 prefixEnd_514546 := by exact prefixLift 514546
  have htrace : WordTrace (prefixWord ++ tailWord_514546) baseStart_514546 baseEnd_514546 := by
    simpa [prefixWord, tailWord_514546, baseEnd_514546] using wordTrace_append hprefix tailTrace_514546
  have hstable : (prefixWord ++ tailWord_514546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514546).length < 2 ^ (prefixWord ++ tailWord_514546).sum := by decide
  have hdescent : baseEnd_514546 < baseStart_514546 := by decide
  rcases family_descends (prefixWord ++ tailWord_514546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514557 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_514557 : Nat := 118140960795 + 514557 * 2 ^ 59
def prefixEnd_514557 : Nat := 4983230072969 + 3 ^ 40 * 514557 * 2
def baseEnd_514557 : Nat := 234857835676132024063201

theorem tailTrace_514557 : CollatzResearch.WordTrace tailWord_514557 prefixEnd_514557 234857835676132024063201 := by
  unfold tailWord_514557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18767435596855343184277925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12511623731236895456185283 18767435596855343184277925)
  ·
    refine ⟨3518894174410376847052111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18767435596855343184277925 3518894174410376847052111)
    ·
      refine ⟨5278341261615565270578167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518894174410376847052111 5278341261615565270578167)
      ·
        refine ⟨7917511892423347905867251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278341261615565270578167 7917511892423347905867251)
        ·
          refine ⟨11876267838635021858800877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917511892423347905867251 11876267838635021858800877)
          ·
            refine ⟨4453600439488133197050329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11876267838635021858800877 4453600439488133197050329)
            ·
              refine ⟨3340200329616099897787747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453600439488133197050329 3340200329616099897787747)
              ·
                refine ⟨5010300494424149846681621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340200329616099897787747 5010300494424149846681621)
                ·
                  refine ⟨234857835676132024063201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5010300494424149846681621 234857835676132024063201)
                  ·
                    rfl

theorem cell20_514557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_514557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514557 prefixEnd_514557 := by exact prefixLift 514557
  have htrace : WordTrace (prefixWord ++ tailWord_514557) baseStart_514557 baseEnd_514557 := by
    simpa [prefixWord, tailWord_514557, baseEnd_514557] using wordTrace_append hprefix tailTrace_514557
  have hstable : (prefixWord ++ tailWord_514557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514557).length < 2 ^ (prefixWord ++ tailWord_514557).sum := by decide
  have hdescent : baseEnd_514557 < baseStart_514557 := by decide
  rcases family_descends (prefixWord ++ tailWord_514557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514629 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 2]
def baseStart_514629 : Nat := 118140960795 + 514629 * 2 ^ 59
def prefixEnd_514629 : Nat := 4983230072969 + 3 ^ 40 * 514629 * 2
def baseEnd_514629 : Nat := 234890698438019773662907

theorem tailTrace_514629 : CollatzResearch.WordTrace tailWord_514629 prefixEnd_514629 234890698438019773662907 := by
  unfold tailWord_514629
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770061652594499480898941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12513374435062999653932627 18770061652594499480898941)
  ·
    refine ⟨7038773119722937305337103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18770061652594499480898941 7038773119722937305337103)
    ·
      refine ⟨10558159679584405958005655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038773119722937305337103 10558159679584405958005655)
      ·
        refine ⟨15837239519376608937008483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558159679584405958005655 15837239519376608937008483)
        ·
          refine ⟨23755859279064913405512725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837239519376608937008483 23755859279064913405512725)
          ·
            refine ⟨1113555903706167815883409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23755859279064913405512725 1113555903706167815883409)
            ·
              refine ⟨835166927779625861912557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113555903706167815883409 835166927779625861912557)
              ·
                refine ⟨313187597917359698217209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835166927779625861912557 313187597917359698217209)
                ·
                  refine ⟨234890698438019773662907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313187597917359698217209 234890698438019773662907)
                  ·
                    rfl

theorem cell20_514629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_514629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514629 prefixEnd_514629 := by exact prefixLift 514629
  have htrace : WordTrace (prefixWord ++ tailWord_514629) baseStart_514629 baseEnd_514629 := by
    simpa [prefixWord, tailWord_514629, baseEnd_514629] using wordTrace_append hprefix tailTrace_514629
  have hstable : (prefixWord ++ tailWord_514629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514629).length < 2 ^ (prefixWord ++ tailWord_514629).sum := by decide
  have hdescent : baseEnd_514629 < baseStart_514629 := by decide
  rcases family_descends (prefixWord ++ tailWord_514629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514671 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_514671 : Nat := 118140960795 + 514671 * 2 ^ 59
def prefixEnd_514671 : Nat := 4983230072969 + 3 ^ 40 * 514671 * 2
def baseEnd_514671 : Nat := 234909868382454294262735

theorem tailTrace_514671 : CollatzResearch.WordTrace tailWord_514671 prefixEnd_514671 234909868382454294262735 := by
  unfold tailWord_514671
  simp only [CollatzResearch.WordTrace]
  refine ⟨18771593518442340653927867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12514395678961560435951911 18771593518442340653927867)
  ·
    refine ⟨28157390277663510980891801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18771593518442340653927867 28157390277663510980891801)
    ·
      refine ⟨21118042708247633235668851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28157390277663510980891801 21118042708247633235668851)
      ·
        refine ⟨31677064062371449853503277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21118042708247633235668851 31677064062371449853503277)
        ·
          refine ⟨11878899023389293695063729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31677064062371449853503277 11878899023389293695063729)
          ·
            refine ⟨8909174267541970271297797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878899023389293695063729 8909174267541970271297797)
            ·
              refine ⟨1670470175164119425868337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8909174267541970271297797 1670470175164119425868337)
              ·
                refine ⟨1252852631373089569401253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670470175164119425868337 1252852631373089569401253)
                ·
                  refine ⟨234909868382454294262735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252852631373089569401253 234909868382454294262735)
                  ·
                    rfl

theorem cell20_514671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_514671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514671 prefixEnd_514671 := by exact prefixLift 514671
  have htrace : WordTrace (prefixWord ++ tailWord_514671) baseStart_514671 baseEnd_514671 := by
    simpa [prefixWord, tailWord_514671, baseEnd_514671] using wordTrace_append hprefix tailTrace_514671
  have hstable : (prefixWord ++ tailWord_514671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514671).length < 2 ^ (prefixWord ++ tailWord_514671).sum := by decide
  have hdescent : baseEnd_514671 < baseStart_514671 := by decide
  rcases family_descends (prefixWord ++ tailWord_514671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514702 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_514702 : Nat := 118140960795 + 514702 * 2 ^ 59
def prefixEnd_514702 : Nat := 4983230072969 + 3 ^ 40 * 514702 * 2
def baseEnd_514702 : Nat := 234924017627155964229275

theorem tailTrace_514702 : CollatzResearch.WordTrace tailWord_514702 prefixEnd_514702 234924017627155964229275 := by
  unfold tailWord_514702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346590522666254118538295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12515149454220021965537573 2346590522666254118538295)
  ·
    refine ⟨3519885783999381177807443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2346590522666254118538295 3519885783999381177807443)
    ·
      refine ⟨5279828675999071766711165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519885783999381177807443 5279828675999071766711165)
      ·
        refine ⟨1979935753499651912516687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5279828675999071766711165 1979935753499651912516687)
        ·
          refine ⟨2969903630249477868775031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979935753499651912516687 2969903630249477868775031)
          ·
            refine ⟨4454855445374216803162547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969903630249477868775031 4454855445374216803162547)
            ·
              refine ⟨6682283168061325204743821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454855445374216803162547 6682283168061325204743821)
              ·
                refine ⟨2505856188022996951778933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6682283168061325204743821 2505856188022996951778933)
                ·
                  refine ⟨234924017627155964229275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2505856188022996951778933 234924017627155964229275)
                  ·
                    rfl

theorem cell20_514702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_514702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514702 prefixEnd_514702 := by exact prefixLift 514702
  have htrace : WordTrace (prefixWord ++ tailWord_514702) baseStart_514702 baseEnd_514702 := by
    simpa [prefixWord, tailWord_514702, baseEnd_514702] using wordTrace_append hprefix tailTrace_514702
  have hstable : (prefixWord ++ tailWord_514702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514702).length < 2 ^ (prefixWord ++ tailWord_514702).sum := by decide
  have hdescent : baseEnd_514702 < baseStart_514702 := by decide
  rcases family_descends (prefixWord ++ tailWord_514702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514723 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_514723 : Nat := 118140960795 + 514723 * 2 ^ 59
def prefixEnd_514723 : Nat := 4983230072969 + 3 ^ 40 * 514723 * 2
def baseEnd_514723 : Nat := 234933602599373224529189

theorem tailTrace_514723 : CollatzResearch.WordTrace tailWord_514723 prefixEnd_514723 234933602599373224529189 := by
  unfold tailWord_514723
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773490114253953534820823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12515660076169302356547215 18773490114253953534820823)
  ·
    refine ⟨28160235171380930302231235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18773490114253953534820823 28160235171380930302231235)
    ·
      refine ⟨42240352757071395453346853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28160235171380930302231235 42240352757071395453346853)
      ·
        refine ⟨7920066141950886647502535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42240352757071395453346853 7920066141950886647502535)
        ·
          refine ⟨11880099212926329971253803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920066141950886647502535 11880099212926329971253803)
          ·
            refine ⟨17820148819389494956880705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11880099212926329971253803 17820148819389494956880705)
            ·
              refine ⟨13365111614542121217660529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17820148819389494956880705 13365111614542121217660529)
              ·
                refine ⟨10023833710906590913245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13365111614542121217660529 10023833710906590913245397)
                ·
                  refine ⟨234933602599373224529189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10023833710906590913245397 234933602599373224529189)
                  ·
                    rfl

theorem cell20_514723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_514723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514723 prefixEnd_514723 := by exact prefixLift 514723
  have htrace : WordTrace (prefixWord ++ tailWord_514723) baseStart_514723 baseEnd_514723 := by
    simpa [prefixWord, tailWord_514723, baseEnd_514723] using wordTrace_append hprefix tailTrace_514723
  have hstable : (prefixWord ++ tailWord_514723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514723).length < 2 ^ (prefixWord ++ tailWord_514723).sum := by decide
  have hdescent : baseEnd_514723 < baseStart_514723 := by decide
  rcases family_descends (prefixWord ++ tailWord_514723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514733 : List Nat := [1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_514733 : Nat := 118140960795 + 514733 * 2 ^ 59
def prefixEnd_514733 : Nat := 4983230072969 + 3 ^ 40 * 514733 * 2
def baseEnd_514733 : Nat := 78312722290619211398605

theorem tailTrace_514733 : CollatzResearch.WordTrace tailWord_514733 prefixEnd_514733 78312722290619211398605 := by
  unfold tailWord_514733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773854844217725242684853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12515903229478483495123235 18773854844217725242684853)
  ·
    refine ⟨1760048891645411741501705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18773854844217725242684853 1760048891645411741501705)
    ·
      refine ⟨1320036668734058806126279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760048891645411741501705 1320036668734058806126279)
      ·
        refine ⟨1980055003101088209189419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320036668734058806126279 1980055003101088209189419)
        ·
          refine ⟨2970082504651632313784129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980055003101088209189419 2970082504651632313784129)
          ·
            refine ⟨2227561878488724235338097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970082504651632313784129 2227561878488724235338097)
            ·
              refine ⟨1670671408866543176503573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227561878488724235338097 1670671408866543176503573)
              ·
                refine ⟨78312722290619211398605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1670671408866543176503573 78312722290619211398605)
                ·
                  rfl

theorem cell20_514733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_514733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514733 prefixEnd_514733 := by exact prefixLift 514733
  have htrace : WordTrace (prefixWord ++ tailWord_514733) baseStart_514733 baseEnd_514733 := by
    simpa [prefixWord, tailWord_514733, baseEnd_514733] using wordTrace_append hprefix tailTrace_514733
  have hstable : (prefixWord ++ tailWord_514733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514733).length < 2 ^ (prefixWord ++ tailWord_514733).sum := by decide
  have hdescent : baseEnd_514733 < baseStart_514733 := by decide
  rcases family_descends (prefixWord ++ tailWord_514733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514753 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_514753 : Nat := 118140960795 + 514753 * 2 ^ 59
def prefixEnd_514753 : Nat := 4983230072969 + 3 ^ 40 * 514753 * 2
def baseEnd_514753 : Nat := 234947295416826453529067

theorem tailTrace_514753 : CollatzResearch.WordTrace tailWord_514753 prefixEnd_514753 234947295416826453529067 := by
  unfold tailWord_514753
  simp only [CollatzResearch.WordTrace]
  refine ⟨18774584304145268658412913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12516389536096845772275275 18774584304145268658412913)
  ·
    refine ⟨14080938228108951493809685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18774584304145268658412913 14080938228108951493809685)
    ·
      refine ⟨660043979442607101272329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14080938228108951493809685 660043979442607101272329)
      ·
        refine ⟨495032984581955325954247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660043979442607101272329 495032984581955325954247)
        ·
          refine ⟨742549476872932988931371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495032984581955325954247 742549476872932988931371)
          ·
            refine ⟨1113824215309399483397057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742549476872932988931371 1113824215309399483397057)
            ·
              refine ⟨835368161482049612547793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113824215309399483397057 835368161482049612547793)
              ·
                refine ⟨626526121111537209410845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835368161482049612547793 626526121111537209410845)
                ·
                  refine ⟨234947295416826453529067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626526121111537209410845 234947295416826453529067)
                  ·
                    rfl

theorem cell20_514753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_514753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514753 prefixEnd_514753 := by exact prefixLift 514753
  have htrace : WordTrace (prefixWord ++ tailWord_514753) baseStart_514753 baseEnd_514753 := by
    simpa [prefixWord, tailWord_514753, baseEnd_514753] using wordTrace_append hprefix tailTrace_514753
  have hstable : (prefixWord ++ tailWord_514753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514753).length < 2 ^ (prefixWord ++ tailWord_514753).sum := by decide
  have hdescent : baseEnd_514753 < baseStart_514753 := by decide
  rcases family_descends (prefixWord ++ tailWord_514753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514760 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_514760 : Nat := 118140960795 + 514760 * 2 ^ 59
def prefixEnd_514760 : Nat := 4983230072969 + 3 ^ 40 * 514760 * 2
def baseEnd_514760 : Nat := 234950490407565540295705

theorem tailTrace_514760 : CollatzResearch.WordTrace tailWord_514760 prefixEnd_514760 234950490407565540295705 := by
  unfold tailWord_514760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387419807559954426958867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12516559743413272569278489 9387419807559954426958867)
  ·
    refine ⟨14081129711339931640438301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9387419807559954426958867 14081129711339931640438301)
    ·
      refine ⟨5280423641752474365164363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14081129711339931640438301 5280423641752474365164363)
      ·
        refine ⟨7920635462628711547746545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280423641752474365164363 7920635462628711547746545)
        ·
          refine ⟨5940476596971533660809909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920635462628711547746545 5940476596971533660809909)
          ·
            refine ⟨556919680966081280700929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5940476596971533660809909 556919680966081280700929)
            ·
              refine ⟨417689760724560960525697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556919680966081280700929 417689760724560960525697)
              ·
                refine ⟨313267320543420720394273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417689760724560960525697 313267320543420720394273)
                ·
                  refine ⟨234950490407565540295705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313267320543420720394273 234950490407565540295705)
                  ·
                    rfl

theorem cell20_514760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_514760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514760 prefixEnd_514760 := by exact prefixLift 514760
  have htrace : WordTrace (prefixWord ++ tailWord_514760) baseStart_514760 baseEnd_514760 := by
    simpa [prefixWord, tailWord_514760, baseEnd_514760] using wordTrace_append hprefix tailTrace_514760
  have hstable : (prefixWord ++ tailWord_514760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514760).length < 2 ^ (prefixWord ++ tailWord_514760).sum := by decide
  have hdescent : baseEnd_514760 < baseStart_514760 := by decide
  rcases family_descends (prefixWord ++ tailWord_514760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514778 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_514778 : Nat := 118140960795 + 514778 * 2 ^ 59
def prefixEnd_514778 : Nat := 4983230072969 + 3 ^ 40 * 514778 * 2
def baseEnd_514778 : Nat := 234958706098037477695631

theorem tailTrace_514778 : CollatzResearch.WordTrace tailWord_514778 prefixEnd_514778 234958706098037477695631 := by
  unfold tailWord_514778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693874032263674482018247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12516997419369798618715325 4693874032263674482018247)
  ·
    refine ⟨7040811048395511723027371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693874032263674482018247 7040811048395511723027371)
    ·
      refine ⟨10561216572593267584541057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040811048395511723027371 10561216572593267584541057)
      ·
        refine ⟨7920912429444950688405793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10561216572593267584541057 7920912429444950688405793)
        ·
          refine ⟨5940684322083713016304345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920912429444950688405793 5940684322083713016304345)
          ·
            refine ⟨4455513241562784762228259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940684322083713016304345 4455513241562784762228259)
            ·
              refine ⟨6683269862344177143342389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455513241562784762228259 6683269862344177143342389)
              ·
                refine ⟨626556549594766607188349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6683269862344177143342389 626556549594766607188349)
                ·
                  refine ⟨234958706098037477695631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626556549594766607188349 234958706098037477695631)
                  ·
                    rfl

theorem cell20_514778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_514778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514778 prefixEnd_514778 := by exact prefixLift 514778
  have htrace : WordTrace (prefixWord ++ tailWord_514778) baseStart_514778 baseEnd_514778 := by
    simpa [prefixWord, tailWord_514778, baseEnd_514778] using wordTrace_append hprefix tailTrace_514778
  have hstable : (prefixWord ++ tailWord_514778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514778).length < 2 ^ (prefixWord ++ tailWord_514778).sum := by decide
  have hdescent : baseEnd_514778 < baseStart_514778 := by decide
  rcases family_descends (prefixWord ++ tailWord_514778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514785 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_514785 : Nat := 118140960795 + 514785 * 2 ^ 59
def prefixEnd_514785 : Nat := 4983230072969 + 3 ^ 40 * 514785 * 2
def baseEnd_514785 : Nat := 234961901088776564462269

theorem tailTrace_514785 : CollatzResearch.WordTrace tailWord_514785 prefixEnd_514785 234961901088776564462269 := by
  unfold tailWord_514785
  simp only [CollatzResearch.WordTrace]
  refine ⟨18775751440029338123577809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517167626686225415718539 18775751440029338123577809)
  ·
    refine ⟨14081813580022003592683357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18775751440029338123577809 14081813580022003592683357)
    ·
      refine ⟨5280680092508251347256259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14081813580022003592683357 5280680092508251347256259)
      ·
        refine ⟨7921020138762377020884389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280680092508251347256259 7921020138762377020884389)
        ·
          refine ⟨1485191276017945691415823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7921020138762377020884389 1485191276017945691415823)
          ·
            refine ⟨2227786914026918537123735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485191276017945691415823 2227786914026918537123735)
            ·
              refine ⟨3341680371040377805685603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227786914026918537123735 3341680371040377805685603)
              ·
                refine ⟨5012520556560566708528405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341680371040377805685603 5012520556560566708528405)
                ·
                  refine ⟨234961901088776564462269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5012520556560566708528405 234961901088776564462269)
                  ·
                    rfl

theorem cell20_514785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_514785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514785 prefixEnd_514785 := by exact prefixLift 514785
  have htrace : WordTrace (prefixWord ++ tailWord_514785) baseStart_514785 baseEnd_514785 := by
    simpa [prefixWord, tailWord_514785, baseEnd_514785] using wordTrace_append hprefix tailTrace_514785
  have hstable : (prefixWord ++ tailWord_514785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514785).length < 2 ^ (prefixWord ++ tailWord_514785).sum := by decide
  have hdescent : baseEnd_514785 < baseStart_514785 := by decide
  rcases family_descends (prefixWord ++ tailWord_514785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514805 : List Nat := [1, 3, 6, 1, 1, 1, 7]
def baseStart_514805 : Nat := 118140960795 + 514805 * 2 ^ 59
def prefixEnd_514805 : Nat := 4983230072969 + 3 ^ 40 * 514805 * 2
def baseEnd_514805 : Nat := 26107892181527264866169

theorem tailTrace_514805 : CollatzResearch.WordTrace tailWord_514805 prefixEnd_514805 26107892181527264866169 := by
  unfold tailWord_514805
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776480899956881539305869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517653933304587692870579 18776480899956881539305869)
  ·
    refine ⟨7041180337483830577239701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18776480899956881539305869 7041180337483830577239701)
    ·
      refine ⟨330055328319554558308111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7041180337483830577239701 330055328319554558308111)
      ·
        refine ⟨495082992479331837462167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330055328319554558308111 495082992479331837462167)
        ·
          refine ⟨742624488718997756193251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495082992479331837462167 742624488718997756193251)
          ·
            refine ⟨1113936733078496634289877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742624488718997756193251 1113936733078496634289877)
            ·
              refine ⟨26107892181527264866169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1113936733078496634289877 26107892181527264866169)
              ·
                rfl

theorem cell20_514805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 7].length) (baseStart_514805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514805 prefixEnd_514805 := by exact prefixLift 514805
  have htrace : WordTrace (prefixWord ++ tailWord_514805) baseStart_514805 baseEnd_514805 := by
    simpa [prefixWord, tailWord_514805, baseEnd_514805] using wordTrace_append hprefix tailTrace_514805
  have hstable : (prefixWord ++ tailWord_514805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514805).length < 2 ^ (prefixWord ++ tailWord_514805).sum := by decide
  have hdescent : baseEnd_514805 < baseStart_514805 := by decide
  rcases family_descends (prefixWord ++ tailWord_514805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514830 : List Nat := [4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_514830 : Nat := 118140960795 + 514830 * 2 ^ 59
def prefixEnd_514830 : Nat := 4983230072969 + 3 ^ 40 * 514830 * 2
def baseEnd_514830 : Nat := 78327480104985469320695

theorem tailTrace_514830 : CollatzResearch.WordTrace tailWord_514830 prefixEnd_514830 78327480104985469320695 := by
  unfold tailWord_514830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347174090608288851120743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12518261816577540539310629 2347174090608288851120743)
  ·
    refine ⟨3520761135912433276681115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2347174090608288851120743 3520761135912433276681115)
    ·
      refine ⟨5281141703868649915021673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520761135912433276681115 5281141703868649915021673)
      ·
        refine ⟨3960856277901487436266255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5281141703868649915021673 3960856277901487436266255)
        ·
          refine ⟨5941284416852231154399383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960856277901487436266255 5941284416852231154399383)
          ·
            refine ⟨8911926625278346731599075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941284416852231154399383 8911926625278346731599075)
            ·
              refine ⟨13367889937917520097398613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911926625278346731599075 13367889937917520097398613)
              ·
                refine ⟨78327480104985469320695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13367889937917520097398613 78327480104985469320695)
                ·
                  rfl

theorem cell20_514830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_514830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514830 prefixEnd_514830 := by exact prefixLift 514830
  have htrace : WordTrace (prefixWord ++ tailWord_514830) baseStart_514830 baseEnd_514830 := by
    simpa [prefixWord, tailWord_514830, baseEnd_514830] using wordTrace_append hprefix tailTrace_514830
  have hstable : (prefixWord ++ tailWord_514830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514830).length < 2 ^ (prefixWord ++ tailWord_514830).sum := by decide
  have hdescent : baseEnd_514830 < baseStart_514830 := by decide
  rcases family_descends (prefixWord ++ tailWord_514830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514847 : List Nat := [1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_514847 : Nat := 118140960795 + 514847 * 2 ^ 59
def prefixEnd_514847 : Nat := 4983230072969 + 3 ^ 40 * 514847 * 2
def baseEnd_514847 : Nat := 78330066526059968131783

theorem tailTrace_514847 : CollatzResearch.WordTrace tailWord_514847 prefixEnd_514847 78330066526059968131783 := by
  unfold tailWord_514847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778012765804722712334795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12518675177203148474889863 18778012765804722712334795)
  ·
    refine ⟨28167019148707084068502193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18778012765804722712334795 28167019148707084068502193)
    ·
      refine ⟨21125264361530313051376645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28167019148707084068502193 21125264361530313051376645)
      ·
        refine ⟨3960987067786933697133121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21125264361530313051376645 3960987067786933697133121)
        ·
          refine ⟨2970740300840200272849841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3960987067786933697133121 2970740300840200272849841)
          ·
            refine ⟨2228055225630150204637381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970740300840200272849841 2228055225630150204637381)
            ·
              refine ⟨417760354805653163369509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2228055225630150204637381 417760354805653163369509)
              ·
                refine ⟨78330066526059968131783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417760354805653163369509 78330066526059968131783)
                ·
                  rfl

theorem cell20_514847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_514847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514847 prefixEnd_514847 := by exact prefixLift 514847
  have htrace : WordTrace (prefixWord ++ tailWord_514847) baseStart_514847 baseEnd_514847 := by
    simpa [prefixWord, tailWord_514847, baseEnd_514847] using wordTrace_append hprefix tailTrace_514847
  have hstable : (prefixWord ++ tailWord_514847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514847).length < 2 ^ (prefixWord ++ tailWord_514847).sum := by decide
  have hdescent : baseEnd_514847 < baseStart_514847 := by decide
  rcases family_descends (prefixWord ++ tailWord_514847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514874 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_514874 : Nat := 118140960795 + 514874 * 2 ^ 59
def prefixEnd_514874 : Nat := 4983230072969 + 3 ^ 40 * 514874 * 2
def baseEnd_514874 : Nat := 235002523113887810495239

theorem tailTrace_514874 : CollatzResearch.WordTrace tailWord_514874 prefixEnd_514874 235002523113887810495239 := by
  unfold tailWord_514874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694749384176726580891919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12519331691137937549045117 4694749384176726580891919)
  ·
    refine ⟨7042124076265089871337879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694749384176726580891919 7042124076265089871337879)
    ·
      refine ⟨10563186114397634807006819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7042124076265089871337879 10563186114397634807006819)
      ·
        refine ⟨15844779171596452210510229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10563186114397634807006819 15844779171596452210510229)
        ·
          refine ⟨742724023668583697367667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15844779171596452210510229 742724023668583697367667)
          ·
            refine ⟨1114086035502875546051501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742724023668583697367667 1114086035502875546051501)
            ·
              refine ⟨417782263313578329769313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114086035502875546051501 417782263313578329769313)
              ·
                refine ⟨313336697485183747326985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417782263313578329769313 313336697485183747326985)
                ·
                  refine ⟨235002523113887810495239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313336697485183747326985 235002523113887810495239)
                  ·
                    rfl

theorem cell20_514874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_514874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514874 prefixEnd_514874 := by exact prefixLift 514874
  have htrace : WordTrace (prefixWord ++ tailWord_514874) baseStart_514874 baseEnd_514874 := by
    simpa [prefixWord, tailWord_514874, baseEnd_514874] using wordTrace_append hprefix tailTrace_514874
  have hstable : (prefixWord ++ tailWord_514874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514874).length < 2 ^ (prefixWord ++ tailWord_514874).sum := by decide
  have hdescent : baseEnd_514874 < baseStart_514874 := by decide
  rcases family_descends (prefixWord ++ tailWord_514874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514884 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_514884 : Nat := 118140960795 + 514884 * 2 ^ 59
def prefixEnd_514884 : Nat := 4983230072969 + 3 ^ 40 * 514884 * 2
def baseEnd_514884 : Nat := 235007087386372220161865

theorem tailTrace_514884 : CollatzResearch.WordTrace tailWord_514884 prefixEnd_514884 235007087386372220161865 := by
  unfold tailWord_514884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9389681133335339015715853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12519574844447118687621137 9389681133335339015715853)
  ·
    refine ⟨3521130425000752130893445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9389681133335339015715853 3521130425000752130893445)
    ·
      refine ⟨660211954687641024542521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3521130425000752130893445 660211954687641024542521)
      ·
        refine ⟨495158966015730768406891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660211954687641024542521 495158966015730768406891)
        ·
          refine ⟨742738449023596152610337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495158966015730768406891 742738449023596152610337)
          ·
            refine ⟨557053836767697114457753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742738449023596152610337 557053836767697114457753)
            ·
              refine ⟨417790377575772835843315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557053836767697114457753 417790377575772835843315)
              ·
                refine ⟨626685566363659253764973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417790377575772835843315 626685566363659253764973)
                ·
                  refine ⟨235007087386372220161865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626685566363659253764973 235007087386372220161865)
                  ·
                    rfl

theorem cell20_514884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_514884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514884 prefixEnd_514884 := by exact prefixLift 514884
  have htrace : WordTrace (prefixWord ++ tailWord_514884) baseStart_514884 baseEnd_514884 := by
    simpa [prefixWord, tailWord_514884, baseEnd_514884] using wordTrace_append hprefix tailTrace_514884
  have hstable : (prefixWord ++ tailWord_514884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514884).length < 2 ^ (prefixWord ++ tailWord_514884).sum := by decide
  have hdescent : baseEnd_514884 < baseStart_514884 := by decide
  rcases family_descends (prefixWord ++ tailWord_514884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514906 : List Nat := [3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_514906 : Nat := 118140960795 + 514906 * 2 ^ 59
def prefixEnd_514906 : Nat := 4983230072969 + 3 ^ 40 * 514906 * 2
def baseEnd_514906 : Nat := 78339042928612640476147

theorem tailTrace_514906 : CollatzResearch.WordTrace tailWord_514906 prefixEnd_514906 78339042928612640476147 := by
  unfold tailWord_514906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695041168147743947183143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12520109781727317192488381 4695041168147743947183143)
  ·
    refine ⟨7042561752221615920774715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4695041168147743947183143 7042561752221615920774715)
    ·
      refine ⟨10563842628332423881162073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7042561752221615920774715 10563842628332423881162073)
      ·
        refine ⟨7922881971249317910871555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10563842628332423881162073 7922881971249317910871555)
        ·
          refine ⟨11884322956873976866307333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922881971249317910871555 11884322956873976866307333)
          ·
            refine ⟨2228310554413870662432625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11884322956873976866307333 2228310554413870662432625)
            ·
              refine ⟨1671232915810402996824469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228310554413870662432625 1671232915810402996824469)
              ·
                refine ⟨78339042928612640476147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1671232915810402996824469 78339042928612640476147)
                ·
                  rfl

theorem cell20_514906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_514906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514906 prefixEnd_514906 := by exact prefixLift 514906
  have htrace : WordTrace (prefixWord ++ tailWord_514906) baseStart_514906 baseEnd_514906 := by
    simpa [prefixWord, tailWord_514906, baseEnd_514906] using wordTrace_append hprefix tailTrace_514906
  have hstable : (prefixWord ++ tailWord_514906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514906).length < 2 ^ (prefixWord ++ tailWord_514906).sum := by decide
  have hdescent : baseEnd_514906 < baseStart_514906 := by decide
  rcases family_descends (prefixWord ++ tailWord_514906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514913 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_514913 : Nat := 118140960795 + 514913 * 2 ^ 59
def prefixEnd_514913 : Nat := 4983230072969 + 3 ^ 40 * 514913 * 2
def baseEnd_514913 : Nat := 235020323776577008195079

theorem tailTrace_514913 : CollatzResearch.WordTrace tailWord_514913 prefixEnd_514913 235020323776577008195079 := by
  unfold tailWord_514913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18780419983565615984237393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12520279989043743989491595 18780419983565615984237393)
  ·
    refine ⟨14085314987674211988178045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18780419983565615984237393 14085314987674211988178045)
    ·
      refine ⟨5281993120377829495566767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14085314987674211988178045 5281993120377829495566767)
      ·
        refine ⟨7922989680566744243350151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281993120377829495566767 7922989680566744243350151)
        ·
          refine ⟨11884484520850116365025227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922989680566744243350151 11884484520850116365025227)
          ·
            refine ⟨17826726781275174547537841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884484520850116365025227 17826726781275174547537841)
            ·
              refine ⟨13370045085956380910653381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17826726781275174547537841 13370045085956380910653381)
              ·
                refine ⟨2506883453616821420747509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13370045085956380910653381 2506883453616821420747509)
                ·
                  refine ⟨235020323776577008195079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2506883453616821420747509 235020323776577008195079)
                  ·
                    rfl

theorem cell20_514913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_514913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514913 prefixEnd_514913 := by exact prefixLift 514913
  have htrace : WordTrace (prefixWord ++ tailWord_514913) baseStart_514913 baseEnd_514913 := by
    simpa [prefixWord, tailWord_514913, baseEnd_514913] using wordTrace_append hprefix tailTrace_514913
  have hstable : (prefixWord ++ tailWord_514913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514913).length < 2 ^ (prefixWord ++ tailWord_514913).sum := by decide
  have hdescent : baseEnd_514913 < baseStart_514913 := by decide
  rcases family_descends (prefixWord ++ tailWord_514913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514926 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_514926 : Nat := 118140960795 + 514926 * 2 ^ 59
def prefixEnd_514926 : Nat := 4983230072969 + 3 ^ 40 * 514926 * 2
def baseEnd_514926 : Nat := 235026257330806740761693

theorem tailTrace_514926 : CollatzResearch.WordTrace tailWord_514926 prefixEnd_514926 235026257330806740761693 := by
  unfold tailWord_514926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347611766564814900557579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12520596088345679469640421 2347611766564814900557579)
  ·
    refine ⟨3521417649847222350836369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2347611766564814900557579 3521417649847222350836369)
    ·
      refine ⟨2641063237385416763127277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521417649847222350836369 2641063237385416763127277)
      ·
        refine ⟨990398714019531286172729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2641063237385416763127277 990398714019531286172729)
        ·
          refine ⟨742799035514648464629547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990398714019531286172729 742799035514648464629547)
          ·
            refine ⟨1114198553271972696944321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742799035514648464629547 1114198553271972696944321)
            ·
              refine ⟨835648914953979522708241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114198553271972696944321 835648914953979522708241)
              ·
                refine ⟨626736686215484642031181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835648914953979522708241 626736686215484642031181)
                ·
                  refine ⟨235026257330806740761693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626736686215484642031181 235026257330806740761693)
                  ·
                    rfl

theorem cell20_514926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_514926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514926 prefixEnd_514926 := by exact prefixLift 514926
  have htrace : WordTrace (prefixWord ++ tailWord_514926) baseStart_514926 baseEnd_514926 := by
    simpa [prefixWord, tailWord_514926, baseEnd_514926] using wordTrace_append hprefix tailTrace_514926
  have hstable : (prefixWord ++ tailWord_514926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514926).length < 2 ^ (prefixWord ++ tailWord_514926).sum := by decide
  have hdescent : baseEnd_514926 < baseStart_514926 := by decide
  rcases family_descends (prefixWord ++ tailWord_514926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514930 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_514930 : Nat := 118140960795 + 514930 * 2 ^ 59
def prefixEnd_514930 : Nat := 4983230072969 + 3 ^ 40 * 514930 * 2
def baseEnd_514930 : Nat := 235028083039800504628343

theorem tailTrace_514930 : CollatzResearch.WordTrace tailWord_514930 prefixEnd_514930 235028083039800504628343 := by
  unfold tailWord_514930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695260006126006971901561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12520693349669351925070829 4695260006126006971901561)
  ·
    refine ⟨3521445004594505228926171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4695260006126006971901561 3521445004594505228926171)
    ·
      refine ⟨5282167506891757843389257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3521445004594505228926171 5282167506891757843389257)
      ·
        refine ⟨3961625630168818382541943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5282167506891757843389257 3961625630168818382541943)
        ·
          refine ⟨5942438445253227573812915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961625630168818382541943 5942438445253227573812915)
          ·
            refine ⟨8913657667879841360719373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5942438445253227573812915 8913657667879841360719373)
            ·
              refine ⟨3342621625454940510269765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8913657667879841360719373 3342621625454940510269765)
              ·
                refine ⟨626741554772801345675581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3342621625454940510269765 626741554772801345675581)
                ·
                  refine ⟨235028083039800504628343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626741554772801345675581 235028083039800504628343)
                  ·
                    rfl

theorem cell20_514930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_514930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514930 prefixEnd_514930 := by exact prefixLift 514930
  have htrace : WordTrace (prefixWord ++ tailWord_514930) baseStart_514930 baseEnd_514930 := by
    simpa [prefixWord, tailWord_514930, baseEnd_514930] using wordTrace_append hprefix tailTrace_514930
  have hstable : (prefixWord ++ tailWord_514930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514930).length < 2 ^ (prefixWord ++ tailWord_514930).sum := by decide
  have hdescent : baseEnd_514930 < baseStart_514930 := by decide
  rcases family_descends (prefixWord ++ tailWord_514930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514933 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 2]
def baseStart_514933 : Nat := 118140960795 + 514933 * 2 ^ 59
def prefixEnd_514933 : Nat := 4983230072969 + 3 ^ 40 * 514933 * 2
def baseEnd_514933 : Nat := 235029452321545827528331

theorem tailTrace_514933 : CollatzResearch.WordTrace tailWord_514933 prefixEnd_514933 235029452321545827528331 := by
  unfold tailWord_514933
  simp only [CollatzResearch.WordTrace]
  refine ⟨18781149443493159399965453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12520766295662106266643635 18781149443493159399965453)
  ·
    refine ⟨7042931041309934774987045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18781149443493159399965453 7042931041309934774987045)
    ·
      refine ⟨1320549570245612770310071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7042931041309934774987045 1320549570245612770310071)
      ·
        refine ⟨1980824355368419155465107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320549570245612770310071 1980824355368419155465107)
        ·
          refine ⟨2971236533052628733197661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980824355368419155465107 2971236533052628733197661)
          ·
            refine ⟨1114213699894735774949123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2971236533052628733197661 1114213699894735774949123)
            ·
              refine ⟨1671320549842103662423685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114213699894735774949123 1671320549842103662423685)
              ·
                refine ⟨313372603095394436704441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1671320549842103662423685 313372603095394436704441)
                ·
                  refine ⟨235029452321545827528331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313372603095394436704441 235029452321545827528331)
                  ·
                    rfl

theorem cell20_514933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_514933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514933 prefixEnd_514933 := by exact prefixLift 514933
  have htrace : WordTrace (prefixWord ++ tailWord_514933) baseStart_514933 baseEnd_514933 := by
    simpa [prefixWord, tailWord_514933, baseEnd_514933] using wordTrace_append hprefix tailTrace_514933
  have hstable : (prefixWord ++ tailWord_514933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514933).length < 2 ^ (prefixWord ++ tailWord_514933).sum := by decide
  have hdescent : baseEnd_514933 < baseStart_514933 := by decide
  rcases family_descends (prefixWord ++ tailWord_514933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514954 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_514954 : Nat := 118140960795 + 514954 * 2 ^ 59
def prefixEnd_514954 : Nat := 4983230072969 + 3 ^ 40 * 514954 * 2
def baseEnd_514954 : Nat := 235039037293763087828245

theorem tailTrace_514954 : CollatzResearch.WordTrace tailWord_514954 prefixEnd_514954 235039037293763087828245 := by
  unfold tailWord_514954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695478844104269996619979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12521276917611386657653277 4695478844104269996619979)
  ·
    refine ⟨7043218266156404994929969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4695478844104269996619979 7043218266156404994929969)
    ·
      refine ⟨5282413699617303746197477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7043218266156404994929969 5282413699617303746197477)
      ·
        refine ⟨990452568678244452412027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5282413699617303746197477 990452568678244452412027)
        ·
          refine ⟨1485678853017366678618041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990452568678244452412027 1485678853017366678618041)
          ·
            refine ⟨1114259139763025008963531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485678853017366678618041 1114259139763025008963531)
            ·
              refine ⟨1671388709644537513445297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114259139763025008963531 1671388709644537513445297)
              ·
                refine ⟨1253541532233403135083973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671388709644537513445297 1253541532233403135083973)
                ·
                  refine ⟨235039037293763087828245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1253541532233403135083973 235039037293763087828245)
                  ·
                    rfl

theorem cell20_514954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_514954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_514954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_514954 prefixEnd_514954 := by exact prefixLift 514954
  have htrace : WordTrace (prefixWord ++ tailWord_514954) baseStart_514954 baseEnd_514954 := by
    simpa [prefixWord, tailWord_514954, baseEnd_514954] using wordTrace_append hprefix tailTrace_514954
  have hstable : (prefixWord ++ tailWord_514954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514954).length < 2 ^ (prefixWord ++ tailWord_514954).sum := by decide
  have hdescent : baseEnd_514954 < baseStart_514954 := by decide
  rcases family_descends (prefixWord ++ tailWord_514954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515012 : List Nat := [2, 3, 3, 3, 2, 1, 2, 4]
def baseStart_515012 : Nat := 118140960795 + 515012 * 2 ^ 59
def prefixEnd_515012 : Nat := 4983230072969 + 3 ^ 40 * 515012 * 2
def baseEnd_515012 : Nat := 78355170024724221298225

theorem tailTrace_515012 : CollatzResearch.WordTrace tailWord_515012 prefixEnd_515012 78355170024724221298225 := by
  unfold tailWord_515012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392015405103477946045645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12522687206804637261394193 9392015405103477946045645)
  ·
    refine ⟨3522005776913804229767117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9392015405103477946045645 3522005776913804229767117)
    ·
      refine ⟨1320752166342676586162669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3522005776913804229767117 1320752166342676586162669)
      ·
        refine ⟨495282062378503719811001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1320752166342676586162669 495282062378503719811001)
        ·
          refine ⟨371461546783877789858251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495282062378503719811001 371461546783877789858251)
          ·
            refine ⟨557192320175816684787377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371461546783877789858251 557192320175816684787377)
            ·
              refine ⟨417894240131862513590533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557192320175816684787377 417894240131862513590533)
              ·
                refine ⟨78355170024724221298225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417894240131862513590533 78355170024724221298225)
                ·
                  rfl

theorem cell20_515012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_515012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515012 prefixEnd_515012 := by exact prefixLift 515012
  have htrace : WordTrace (prefixWord ++ tailWord_515012) baseStart_515012 baseEnd_515012 := by
    simpa [prefixWord, tailWord_515012, baseEnd_515012] using wordTrace_append hprefix tailTrace_515012
  have hstable : (prefixWord ++ tailWord_515012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515012).length < 2 ^ (prefixWord ++ tailWord_515012).sum := by decide
  have hdescent : baseEnd_515012 < baseStart_515012 := by decide
  rcases family_descends (prefixWord ++ tailWord_515012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515016 : List Nat := [2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_515016 : Nat := 118140960795 + 515016 * 2 ^ 59
def prefixEnd_515016 : Nat := 4983230072969 + 3 ^ 40 * 515016 * 2
def baseEnd_515016 : Nat := 78355778594388809253775

theorem tailTrace_515016 : CollatzResearch.WordTrace tailWord_515016 prefixEnd_515016 78355778594388809253775 := by
  unfold tailWord_515016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392088351096232287618451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12522784468128309716824601 9392088351096232287618451)
  ·
    refine ⟨14088132526644348431427677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9392088351096232287618451 14088132526644348431427677)
    ·
      refine ⟨5283049697491630661785379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14088132526644348431427677 5283049697491630661785379)
      ·
        refine ⟨7924574546237445992678069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283049697491630661785379 7924574546237445992678069)
        ·
          refine ⟨742928863709760561813569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7924574546237445992678069 742928863709760561813569)
          ·
            refine ⟨557196647782320421360177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742928863709760561813569 557196647782320421360177)
            ·
              refine ⟨417897485836740316020133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557196647782320421360177 417897485836740316020133)
              ·
                refine ⟨78355778594388809253775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417897485836740316020133 78355778594388809253775)
                ·
                  rfl

theorem cell20_515016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_515016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515016 prefixEnd_515016 := by exact prefixLift 515016
  have htrace : WordTrace (prefixWord ++ tailWord_515016) baseStart_515016 baseEnd_515016 := by
    simpa [prefixWord, tailWord_515016, baseEnd_515016] using wordTrace_append hprefix tailTrace_515016
  have hstable : (prefixWord ++ tailWord_515016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515016).length < 2 ^ (prefixWord ++ tailWord_515016).sum := by decide
  have hdescent : baseEnd_515016 < baseStart_515016 := by decide
  rcases family_descends (prefixWord ++ tailWord_515016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515020 : List Nat := [2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_515020 : Nat := 118140960795 + 515020 * 2 ^ 59
def prefixEnd_515020 : Nat := 4983230072969 + 3 ^ 40 * 515020 * 2
def baseEnd_515020 : Nat := 78356387164053397209325

theorem tailTrace_515020 : CollatzResearch.WordTrace tailWord_515020 prefixEnd_515020 78356387164053397209325 := by
  unfold tailWord_515020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392161297088986629191257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12522881729451982172255009 9392161297088986629191257)
  ·
    refine ⟨7044120972816739971893443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9392161297088986629191257 7044120972816739971893443)
    ·
      refine ⟨10566181459225109957840165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044120972816739971893443 10566181459225109957840165)
      ·
        refine ⟨1981159023604708117095031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10566181459225109957840165 1981159023604708117095031)
        ·
          refine ⟨2971738535407062175642547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981159023604708117095031 2971738535407062175642547)
          ·
            refine ⟨4457607803110593263463821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971738535407062175642547 4457607803110593263463821)
            ·
              refine ⟨1671602926166472473798933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4457607803110593263463821 1671602926166472473798933)
              ·
                refine ⟨78356387164053397209325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1671602926166472473798933 78356387164053397209325)
                ·
                  rfl

theorem cell20_515020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_515020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515020 prefixEnd_515020 := by exact prefixLift 515020
  have htrace : WordTrace (prefixWord ++ tailWord_515020) baseStart_515020 baseEnd_515020 := by
    simpa [prefixWord, tailWord_515020, baseEnd_515020] using wordTrace_append hprefix tailTrace_515020
  have hstable : (prefixWord ++ tailWord_515020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515020).length < 2 ^ (prefixWord ++ tailWord_515020).sum := by decide
  have hdescent : baseEnd_515020 < baseStart_515020 := by decide
  rcases family_descends (prefixWord ++ tailWord_515020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515026 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_515026 : Nat := 118140960795 + 515026 * 2 ^ 59
def prefixEnd_515026 : Nat := 4983230072969 + 3 ^ 40 * 515026 * 2
def baseEnd_515026 : Nat := 235071900055650837427951

theorem tailTrace_515026 : CollatzResearch.WordTrace tailWord_515026 prefixEnd_515026 235071900055650837427951 := by
  unfold tailWord_515026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696135358039059070775233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12523027621437490855400621 4696135358039059070775233)
  ·
    refine ⟨3522101518529294303081425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4696135358039059070775233 3522101518529294303081425)
    ·
      refine ⟨2641576138896970727311069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3522101518529294303081425 2641576138896970727311069)
      ·
        refine ⟨990591052086364022741651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2641576138896970727311069 990591052086364022741651)
        ·
          refine ⟨1485886578129546034112477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990591052086364022741651 1485886578129546034112477)
          ·
            refine ⟨557207466798579762792179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1485886578129546034112477 557207466798579762792179)
            ·
              refine ⟨835811200197869644188269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557207466798579762792179 835811200197869644188269)
              ·
                refine ⟨313429200074201116570601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835811200197869644188269 313429200074201116570601)
                ·
                  refine ⟨235071900055650837427951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313429200074201116570601 235071900055650837427951)
                  ·
                    rfl

theorem cell20_515026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_515026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515026 prefixEnd_515026 := by exact prefixLift 515026
  have htrace : WordTrace (prefixWord ++ tailWord_515026) baseStart_515026 baseEnd_515026 := by
    simpa [prefixWord, tailWord_515026, baseEnd_515026] using wordTrace_append hprefix tailTrace_515026
  have hstable : (prefixWord ++ tailWord_515026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515026).length < 2 ^ (prefixWord ++ tailWord_515026).sum := by decide
  have hdescent : baseEnd_515026 < baseStart_515026 := by decide
  rcases family_descends (prefixWord ++ tailWord_515026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515037 : List Nat := [1, 4, 3, 1, 2, 3, 6]
def baseStart_515037 : Nat := 118140960795 + 515037 * 2 ^ 59
def prefixEnd_515037 : Nat := 4983230072969 + 3 ^ 40 * 515037 * 2
def baseEnd_515037 : Nat := 26119657861709298673471

theorem tailTrace_515037 : CollatzResearch.WordTrace tailWord_515037 prefixEnd_515037 26119657861709298673471 := by
  unfold tailWord_515037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784942635116385161751365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12523295090077590107834243 18784942635116385161751365)
  ·
    refine ⟨3522176744084322217828381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18784942635116385161751365 3522176744084322217828381)
    ·
      refine ⟨1320816279031620831685643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3522176744084322217828381 1320816279031620831685643)
      ·
        refine ⟨1981224418547431247528465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320816279031620831685643 1981224418547431247528465)
        ·
          refine ⟨1485918313910573435646349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1981224418547431247528465 1485918313910573435646349)
          ·
            refine ⟨557219367716465038367381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1485918313910573435646349 557219367716465038367381)
            ·
              refine ⟨26119657861709298673471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 557219367716465038367381 26119657861709298673471)
              ·
                rfl

theorem cell20_515037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_515037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515037 prefixEnd_515037 := by exact prefixLift 515037
  have htrace : WordTrace (prefixWord ++ tailWord_515037) baseStart_515037 baseEnd_515037 := by
    simpa [prefixWord, tailWord_515037, baseEnd_515037] using wordTrace_append hprefix tailTrace_515037
  have hstable : (prefixWord ++ tailWord_515037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515037).length < 2 ^ (prefixWord ++ tailWord_515037).sum := by decide
  have hdescent : baseEnd_515037 < baseStart_515037 := by decide
  rcases family_descends (prefixWord ++ tailWord_515037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515144 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_515144 : Nat := 118140960795 + 515144 * 2 ^ 59
def prefixEnd_515144 : Nat := 4983230072969 + 3 ^ 40 * 515144 * 2
def baseEnd_515144 : Nat := 235125758470966871494135

theorem tailTrace_515144 : CollatzResearch.WordTrace tailWord_515144 prefixEnd_515144 235125758470966871494135 := by
  unfold tailWord_515144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394422622864371217948243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12525896830485828290597657 9394422622864371217948243)
  ·
    refine ⟨14091633934296556826922365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9394422622864371217948243 14091633934296556826922365)
    ·
      refine ⟨5284362725361208810095887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14091633934296556826922365 5284362725361208810095887)
      ·
        refine ⟨7926544088041813215143831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284362725361208810095887 7926544088041813215143831)
        ·
          refine ⟨11889816132062719822715747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926544088041813215143831 11889816132062719822715747)
          ·
            refine ⟨17834724198094079734073621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889816132062719822715747 17834724198094079734073621)
            ·
              refine ⟨836002696785659987534701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17834724198094079734073621 836002696785659987534701)
              ·
                refine ⟨313501011294622495325513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836002696785659987534701 313501011294622495325513)
                ·
                  refine ⟨235125758470966871494135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313501011294622495325513 235125758470966871494135)
                  ·
                    rfl

theorem cell20_515144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_515144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515144 prefixEnd_515144 := by exact prefixLift 515144
  have htrace : WordTrace (prefixWord ++ tailWord_515144) baseStart_515144 baseEnd_515144 := by
    simpa [prefixWord, tailWord_515144, baseEnd_515144] using wordTrace_append hprefix tailTrace_515144
  have hstable : (prefixWord ++ tailWord_515144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515144).length < 2 ^ (prefixWord ++ tailWord_515144).sum := by decide
  have hdescent : baseEnd_515144 < baseStart_515144 := by decide
  rcases family_descends (prefixWord ++ tailWord_515144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515148 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_515148 : Nat := 118140960795 + 515148 * 2 ^ 59
def prefixEnd_515148 : Nat := 4983230072969 + 3 ^ 40 * 515148 * 2
def baseEnd_515148 : Nat := 235127584179960635360785

theorem tailTrace_515148 : CollatzResearch.WordTrace tailWord_515148 prefixEnd_515148 235127584179960635360785 := by
  unfold tailWord_515148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394495568857125559521049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12525994091809500746028065 9394495568857125559521049)
  ·
    refine ⟨7045871676642844169640787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9394495568857125559521049 7045871676642844169640787)
    ·
      refine ⟨10568807514964266254461181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045871676642844169640787 10568807514964266254461181)
      ·
        refine ⟨3963302818111599845422943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10568807514964266254461181 3963302818111599845422943)
        ·
          refine ⟨5944954227167399768134415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963302818111599845422943 5944954227167399768134415)
          ·
            refine ⟨8917431340751099652201623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944954227167399768134415 8917431340751099652201623)
            ·
              refine ⟨13376147011126649478302435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917431340751099652201623 13376147011126649478302435)
              ·
                refine ⟨20064220516689974217453653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13376147011126649478302435 20064220516689974217453653)
                ·
                  refine ⟨235127584179960635360785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20064220516689974217453653 235127584179960635360785)
                  ·
                    rfl

theorem cell20_515148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_515148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515148 prefixEnd_515148 := by exact prefixLift 515148
  have htrace : WordTrace (prefixWord ++ tailWord_515148) baseStart_515148 baseEnd_515148 := by
    simpa [prefixWord, tailWord_515148, baseEnd_515148] using wordTrace_append hprefix tailTrace_515148
  have hstable : (prefixWord ++ tailWord_515148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515148).length < 2 ^ (prefixWord ++ tailWord_515148).sum := by decide
  have hdescent : baseEnd_515148 < baseStart_515148 := by decide
  rcases family_descends (prefixWord ++ tailWord_515148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515175 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 3]
def baseStart_515175 : Nat := 118140960795 + 515175 * 2 ^ 59
def prefixEnd_515175 : Nat := 4983230072969 + 3 ^ 40 * 515175 * 2
def baseEnd_515175 : Nat := 235139907715668541460675

theorem tailTrace_515175 : CollatzResearch.WordTrace tailWord_515175 prefixEnd_515175 235139907715668541460675 := by
  unfold tailWord_515175
  simp only [CollatzResearch.WordTrace]
  refine ⟨18789975908616434730274979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12526650605744289820183319 18789975908616434730274979)
  ·
    refine ⟨28184963862924652095412469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18789975908616434730274979 28184963862924652095412469)
    ·
      refine ⟨2642340362149186133944919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28184963862924652095412469 2642340362149186133944919)
      ·
        refine ⟨3963510543223779200917379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642340362149186133944919 3963510543223779200917379)
        ·
          refine ⟨5945265814835668801376069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963510543223779200917379 5945265814835668801376069)
          ·
            refine ⟨1114737340281687900258013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5945265814835668801376069 1114737340281687900258013)
            ·
              refine ⟨418026502605632962596755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114737340281687900258013 418026502605632962596755)
              ·
                refine ⟨627039753908449443895133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418026502605632962596755 627039753908449443895133)
                ·
                  refine ⟨235139907715668541460675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627039753908449443895133 235139907715668541460675)
                  ·
                    rfl

theorem cell20_515175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_515175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515175 prefixEnd_515175 := by exact prefixLift 515175
  have htrace : WordTrace (prefixWord ++ tailWord_515175) baseStart_515175 baseEnd_515175 := by
    simpa [prefixWord, tailWord_515175, baseEnd_515175] using wordTrace_append hprefix tailTrace_515175
  have hstable : (prefixWord ++ tailWord_515175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515175).length < 2 ^ (prefixWord ++ tailWord_515175).sum := by decide
  have hdescent : baseEnd_515175 < baseStart_515175 := by decide
  rcases family_descends (prefixWord ++ tailWord_515175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515230 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_515230 : Nat := 118140960795 + 515230 * 2 ^ 59
def prefixEnd_515230 : Nat := 4983230072969 + 3 ^ 40 * 515230 * 2
def baseEnd_515230 : Nat := 235165011214332794627117

theorem tailTrace_515230 : CollatzResearch.WordTrace tailWord_515230 prefixEnd_515230 235165011214332794627117 := by
  unfold tailWord_515230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348997740427147390440893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12527987948944786082351429 2348997740427147390440893)
  ·
    refine ⟨880874152660180271415335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2348997740427147390440893 880874152660180271415335)
    ·
      refine ⟨1321311228990270407123003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880874152660180271415335 1321311228990270407123003)
      ·
        refine ⟨1981966843485405610684505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321311228990270407123003 1981966843485405610684505)
        ·
          refine ⟨1486475132614054208013379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1981966843485405610684505 1486475132614054208013379)
          ·
            refine ⟨2229712698921081312020069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486475132614054208013379 2229712698921081312020069)
            ·
              refine ⟨418071131047702746003763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2229712698921081312020069 418071131047702746003763)
              ·
                refine ⟨627106696571554119005645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418071131047702746003763 627106696571554119005645)
                ·
                  refine ⟨235165011214332794627117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627106696571554119005645 235165011214332794627117)
                  ·
                    rfl

theorem cell20_515230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_515230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515230 prefixEnd_515230 := by exact prefixLift 515230
  have htrace : WordTrace (prefixWord ++ tailWord_515230) baseStart_515230 baseEnd_515230 := by
    simpa [prefixWord, tailWord_515230, baseEnd_515230] using wordTrace_append hprefix tailTrace_515230
  have hstable : (prefixWord ++ tailWord_515230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515230).length < 2 ^ (prefixWord ++ tailWord_515230).sum := by decide
  have hdescent : baseEnd_515230 < baseStart_515230 := by decide
  rcases family_descends (prefixWord ++ tailWord_515230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515300 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_515300 : Nat := 118140960795 + 515300 * 2 ^ 59
def prefixEnd_515300 : Nat := 4983230072969 + 3 ^ 40 * 515300 * 2
def baseEnd_515300 : Nat := 235196961121723662293497

theorem tailTrace_515300 : CollatzResearch.WordTrace tailWord_515300 prefixEnd_515300 235196961121723662293497 := by
  unfold tailWord_515300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397267516581790539287677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12529690022109054052383569 9397267516581790539287677)
  ·
    refine ⟨3523975318718171452232879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9397267516581790539287677 3523975318718171452232879)
    ·
      refine ⟨5285962978077257178349319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523975318718171452232879 5285962978077257178349319)
      ·
        refine ⟨7928944467115885767523979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285962978077257178349319 7928944467115885767523979)
        ·
          refine ⟨11893416700673828651285969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928944467115885767523979 11893416700673828651285969)
          ·
            refine ⟨8920062525505371488464477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11893416700673828651285969 8920062525505371488464477)
            ·
              refine ⟨3345023447064514308174179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8920062525505371488464477 3345023447064514308174179)
              ·
                refine ⟨5017535170596771462261269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345023447064514308174179 5017535170596771462261269)
                ·
                  refine ⟨235196961121723662293497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5017535170596771462261269 235196961121723662293497)
                  ·
                    rfl

theorem cell20_515300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_515300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515300 prefixEnd_515300 := by exact prefixLift 515300
  have htrace : WordTrace (prefixWord ++ tailWord_515300) baseStart_515300 baseEnd_515300 := by
    simpa [prefixWord, tailWord_515300, baseEnd_515300] using wordTrace_append hprefix tailTrace_515300
  have hstable : (prefixWord ++ tailWord_515300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515300).length < 2 ^ (prefixWord ++ tailWord_515300).sum := by decide
  have hdescent : baseEnd_515300 < baseStart_515300 := by decide
  rcases family_descends (prefixWord ++ tailWord_515300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515324 : List Nat := [2, 2, 2, 1, 5, 1, 7]
def baseStart_515324 : Nat := 118140960795 + 515324 * 2 ^ 59
def prefixEnd_515324 : Nat := 4983230072969 + 3 ^ 40 * 515324 * 2
def baseEnd_515324 : Nat := 26134212819520693943711

theorem tailTrace_515324 : CollatzResearch.WordTrace tailWord_515324 prefixEnd_515324 26134212819520693943711 := by
  unfold tailWord_515324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397705192538316588724513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12530273590051088784966017 9397705192538316588724513)
  ·
    refine ⟨7048278894403737441543385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9397705192538316588724513 7048278894403737441543385)
    ·
      refine ⟨5286209170802803081157539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7048278894403737441543385 5286209170802803081157539)
      ·
        refine ⟨7929313756204204621736309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286209170802803081157539 7929313756204204621736309)
        ·
          refine ⟨743373164644144183287779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7929313756204204621736309 743373164644144183287779)
          ·
            refine ⟨1115059746966216274931669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743373164644144183287779 1115059746966216274931669)
            ·
              refine ⟨26134212819520693943711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1115059746966216274931669 26134212819520693943711)
              ·
                rfl

theorem cell20_515324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_515324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515324 prefixEnd_515324 := by exact prefixLift 515324
  have htrace : WordTrace (prefixWord ++ tailWord_515324) baseStart_515324 baseEnd_515324 := by
    simpa [prefixWord, tailWord_515324, baseEnd_515324] using wordTrace_append hprefix tailTrace_515324
  have hstable : (prefixWord ++ tailWord_515324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515324).length < 2 ^ (prefixWord ++ tailWord_515324).sum := by decide
  have hdescent : baseEnd_515324 < baseStart_515324 := by decide
  rcases family_descends (prefixWord ++ tailWord_515324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515331 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_515331 : Nat := 118140960795 + 515331 * 2 ^ 59
def prefixEnd_515331 : Nat := 4983230072969 + 3 ^ 40 * 515331 * 2
def baseEnd_515331 : Nat := 235211110366425332260037

theorem tailTrace_515331 : CollatzResearch.WordTrace tailWord_515331 prefixEnd_515331 235211110366425332260037 := by
  unfold tailWord_515331
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795665696051273372953847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12530443797367515581969231 18795665696051273372953847)
  ·
    refine ⟨28193498544076910059430771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18795665696051273372953847 28193498544076910059430771)
    ·
      refine ⟨42290247816115365089146157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28193498544076910059430771 42290247816115365089146157)
      ·
        refine ⟨15858842931043261908429809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42290247816115365089146157 15858842931043261908429809)
        ·
          refine ⟨11894132198282446431322357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15858842931043261908429809 11894132198282446431322357)
          ·
            refine ⟨1115074893588979352936471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11894132198282446431322357 1115074893588979352936471)
            ·
              refine ⟨1672612340383469029404707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115074893588979352936471 1672612340383469029404707)
              ·
                refine ⟨2508918510575203544107061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672612340383469029404707 2508918510575203544107061)
                ·
                  refine ⟨235211110366425332260037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2508918510575203544107061 235211110366425332260037)
                  ·
                    rfl

theorem cell20_515331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_515331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515331 prefixEnd_515331 := by exact prefixLift 515331
  have htrace : WordTrace (prefixWord ++ tailWord_515331) baseStart_515331 baseEnd_515331 := by
    simpa [prefixWord, tailWord_515331, baseEnd_515331] using wordTrace_append hprefix tailTrace_515331
  have hstable : (prefixWord ++ tailWord_515331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515331).length < 2 ^ (prefixWord ++ tailWord_515331).sum := by decide
  have hdescent : baseEnd_515331 < baseStart_515331 := by decide
  rcases family_descends (prefixWord ++ tailWord_515331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515345 : List Nat := [1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_515345 : Nat := 118140960795 + 515345 * 2 ^ 59
def prefixEnd_515345 : Nat := 4983230072969 + 3 ^ 40 * 515345 * 2
def baseEnd_515345 : Nat := 78405833449301168597771

theorem tailTrace_515345 : CollatzResearch.WordTrace tailWord_515345 prefixEnd_515345 78405833449301168597771 := by
  unfold tailWord_515345
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796176318000553763963489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12530784212000369175975659 18796176318000553763963489)
  ·
    refine ⟨14097132238500415322972617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18796176318000553763963489 14097132238500415322972617)
    ·
      refine ⟨10572849178875311492229463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14097132238500415322972617 10572849178875311492229463)
      ·
        refine ⟨15859273768312967238344195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572849178875311492229463 15859273768312967238344195)
        ·
          refine ⟨23788910652469450857516293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859273768312967238344195 23788910652469450857516293)
          ·
            refine ⟨4460420747338022035784305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23788910652469450857516293 4460420747338022035784305)
            ·
              refine ⟨3345315560503516526838229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460420747338022035784305 3345315560503516526838229)
              ·
                refine ⟨78405833449301168597771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3345315560503516526838229 78405833449301168597771)
                ·
                  rfl

theorem cell20_515345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_515345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515345 prefixEnd_515345 := by exact prefixLift 515345
  have htrace : WordTrace (prefixWord ++ tailWord_515345) baseStart_515345 baseEnd_515345 := by
    simpa [prefixWord, tailWord_515345, baseEnd_515345] using wordTrace_append hprefix tailTrace_515345
  have hstable : (prefixWord ++ tailWord_515345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515345).length < 2 ^ (prefixWord ++ tailWord_515345).sum := by decide
  have hdescent : baseEnd_515345 < baseStart_515345 := by decide
  rcases family_descends (prefixWord ++ tailWord_515345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515358 : List Nat := [4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_515358 : Nat := 118140960795 + 515358 * 2 ^ 59
def prefixEnd_515358 : Nat := 4983230072969 + 3 ^ 40 * 515358 * 2
def baseEnd_515358 : Nat := 78407811300711079453309

theorem tailTrace_515358 : CollatzResearch.WordTrace tailWord_515358 prefixEnd_515358 78407811300711079453309 := by
  unfold tailWord_515358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349581308369182123023341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12531100311302304656124485 2349581308369182123023341)
  ·
    refine ⟨881092990638443296133753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2349581308369182123023341 881092990638443296133753)
    ·
      refine ⟨660819742978832472100315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881092990638443296133753 660819742978832472100315)
      ·
        refine ⟨991229614468248708150473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660819742978832472100315 991229614468248708150473)
        ·
          refine ⟨743422210851186531112855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991229614468248708150473 743422210851186531112855)
          ·
            refine ⟨1115133316276779796669283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743422210851186531112855 1115133316276779796669283)
            ·
              refine ⟨1672699974415169695003925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115133316276779796669283 1672699974415169695003925)
              ·
                refine ⟨78407811300711079453309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1672699974415169695003925 78407811300711079453309)
                ·
                  rfl

theorem cell20_515358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_515358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515358 prefixEnd_515358 := by exact prefixLift 515358
  have htrace : WordTrace (prefixWord ++ tailWord_515358) baseStart_515358 baseEnd_515358 := by
    simpa [prefixWord, tailWord_515358, baseEnd_515358] using wordTrace_append hprefix tailTrace_515358
  have hstable : (prefixWord ++ tailWord_515358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515358).length < 2 ^ (prefixWord ++ tailWord_515358).sum := by decide
  have hdescent : baseEnd_515358 < baseStart_515358 := by decide
  rcases family_descends (prefixWord ++ tailWord_515358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515389 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_515389 : Nat := 118140960795 + 515389 * 2 ^ 59
def prefixEnd_515389 : Nat := 4983230072969 + 3 ^ 40 * 515389 * 2
def baseEnd_515389 : Nat := 235237583146834908326467

theorem tailTrace_515389 : CollatzResearch.WordTrace tailWord_515389 prefixEnd_515389 235237583146834908326467 := by
  unfold tailWord_515389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797781129841149278565221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12531854086560766185710147 18797781129841149278565221)
  ·
    refine ⟨3524583961845215489730979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18797781129841149278565221 3524583961845215489730979)
    ·
      refine ⟨5286875942767823234596469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524583961845215489730979 5286875942767823234596469)
      ·
        refine ⟨495644619634483428243419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5286875942767823234596469 495644619634483428243419)
        ·
          refine ⟨743466929451725142365129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495644619634483428243419 743466929451725142365129)
          ·
            refine ⟨557600197088793856773847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743466929451725142365129 557600197088793856773847)
            ·
              refine ⟨836400295633190785160771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557600197088793856773847 836400295633190785160771)
              ·
                refine ⟨1254600443449786177741157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836400295633190785160771 1254600443449786177741157)
                ·
                  refine ⟨235237583146834908326467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254600443449786177741157 235237583146834908326467)
                  ·
                    rfl

theorem cell20_515389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_515389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515389 prefixEnd_515389 := by exact prefixLift 515389
  have htrace : WordTrace (prefixWord ++ tailWord_515389) baseStart_515389 baseEnd_515389 := by
    simpa [prefixWord, tailWord_515389, baseEnd_515389] using wordTrace_append hprefix tailTrace_515389
  have hstable : (prefixWord ++ tailWord_515389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515389).length < 2 ^ (prefixWord ++ tailWord_515389).sum := by decide
  have hdescent : baseEnd_515389 < baseStart_515389 := by decide
  rcases family_descends (prefixWord ++ tailWord_515389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515438 : List Nat := [4, 1, 2, 4, 9]
def baseStart_515438 : Nat := 118140960795 + 515438 * 2 ^ 59
def prefixEnd_515438 : Nat := 4983230072969 + 3 ^ 40 * 515438 * 2
def baseEnd_515438 : Nat := 2904443803481586613493

theorem tailTrace_515438 : CollatzResearch.WordTrace tailWord_515438 prefixEnd_515438 2904443803481586613493 := by
  unfold tailWord_515438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349946038332953830887371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12533045537775753764732645 2349946038332953830887371)
  ·
    refine ⟨3524919057499430746331057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349946038332953830887371 3524919057499430746331057)
    ·
      refine ⟨2643689293124573059748293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3524919057499430746331057 2643689293124573059748293)
      ·
        refine ⟨495691742460857448702805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2643689293124573059748293 495691742460857448702805)
        ·
          refine ⟨2904443803481586613493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 495691742460857448702805 2904443803481586613493)
          ·
            rfl

theorem cell20_515438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 9].length) (baseStart_515438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515438 prefixEnd_515438 := by exact prefixLift 515438
  have htrace : WordTrace (prefixWord ++ tailWord_515438) baseStart_515438 baseEnd_515438 := by
    simpa [prefixWord, tailWord_515438, baseEnd_515438] using wordTrace_append hprefix tailTrace_515438
  have hstable : (prefixWord ++ tailWord_515438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515438).length < 2 ^ (prefixWord ++ tailWord_515438).sum := by decide
  have hdescent : baseEnd_515438 < baseStart_515438 := by decide
  rcases family_descends (prefixWord ++ tailWord_515438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515452 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_515452 : Nat := 118140960795 + 515452 * 2 ^ 59
def prefixEnd_515452 : Nat := 4983230072969 + 3 ^ 40 * 515452 * 2
def baseEnd_515452 : Nat := 235266338063486689226209

theorem tailTrace_515452 : CollatzResearch.WordTrace tailWord_515452 prefixEnd_515452 235266338063486689226209 := by
  unfold tailWord_515452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400039464306455519054305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12533385952408607358739073 9400039464306455519054305)
  ·
    refine ⟨7050029598229841639290729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9400039464306455519054305 7050029598229841639290729)
    ·
      refine ⟨5287522198672381229468047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7050029598229841639290729 5287522198672381229468047)
      ·
        refine ⟨7931283298008571844202071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287522198672381229468047 7931283298008571844202071)
        ·
          refine ⟨11896924947012857766303107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931283298008571844202071 11896924947012857766303107)
          ·
            refine ⟨17845387420519286649454661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896924947012857766303107 17845387420519286649454661)
            ·
              refine ⟨3346010141347366246772749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17845387420519286649454661 3346010141347366246772749)
              ·
                refine ⟨1254753803005262342539781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3346010141347366246772749 1254753803005262342539781)
                ·
                  refine ⟨235266338063486689226209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254753803005262342539781 235266338063486689226209)
                  ·
                    rfl

theorem cell20_515452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_515452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515452 prefixEnd_515452 := by exact prefixLift 515452
  have htrace : WordTrace (prefixWord ++ tailWord_515452) baseStart_515452 baseEnd_515452 := by
    simpa [prefixWord, tailWord_515452, baseEnd_515452] using wordTrace_append hprefix tailTrace_515452
  have hstable : (prefixWord ++ tailWord_515452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515452).length < 2 ^ (prefixWord ++ tailWord_515452).sum := by decide
  have hdescent : baseEnd_515452 < baseStart_515452 := by decide
  rcases family_descends (prefixWord ++ tailWord_515452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515496 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_515496 : Nat := 118140960795 + 515496 * 2 ^ 59
def prefixEnd_515496 : Nat := 4983230072969 + 3 ^ 40 * 515496 * 2
def baseEnd_515496 : Nat := 235286420862418091759363

theorem tailTrace_515496 : CollatzResearch.WordTrace tailWord_515496 prefixEnd_515496 235286420862418091759363 := by
  unfold tailWord_515496
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400841870226753276355171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12534455826969004368473561 9400841870226753276355171)
  ·
    refine ⟨14101262805340129914532757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9400841870226753276355171 14101262805340129914532757)
    ·
      refine ⟨660996694000318589743723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14101262805340129914532757 660996694000318589743723)
      ·
        refine ⟨991495041000477884615585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660996694000318589743723 991495041000477884615585)
        ·
          refine ⟨743621280750358413461689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991495041000477884615585 743621280750358413461689)
          ·
            refine ⟨557715960562768810096267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743621280750358413461689 557715960562768810096267)
            ·
              refine ⟨836573940844153215144401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557715960562768810096267 836573940844153215144401)
              ·
                refine ⟨627430455633114911358301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836573940844153215144401 627430455633114911358301)
                ·
                  refine ⟨235286420862418091759363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627430455633114911358301 235286420862418091759363)
                  ·
                    rfl

theorem cell20_515496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_515496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515496 prefixEnd_515496 := by exact prefixLift 515496
  have htrace : WordTrace (prefixWord ++ tailWord_515496) baseStart_515496 baseEnd_515496 := by
    simpa [prefixWord, tailWord_515496, baseEnd_515496] using wordTrace_append hprefix tailTrace_515496
  have hstable : (prefixWord ++ tailWord_515496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515496).length < 2 ^ (prefixWord ++ tailWord_515496).sum := by decide
  have hdescent : baseEnd_515496 < baseStart_515496 := by decide
  rcases family_descends (prefixWord ++ tailWord_515496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515528 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_515528 : Nat := 118140960795 + 515528 * 2 ^ 59
def prefixEnd_515528 : Nat := 4983230072969 + 3 ^ 40 * 515528 * 2
def baseEnd_515528 : Nat := 235301026534368202692565

theorem tailTrace_515528 : CollatzResearch.WordTrace tailWord_515528 prefixEnd_515528 235301026534368202692565 := by
  unfold tailWord_515528
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401425438168788008937619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12535233917558384011916825 9401425438168788008937619)
  ·
    refine ⟨14102138157253182013406429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401425438168788008937619 14102138157253182013406429)
    ·
      refine ⟨5288301808969943255027411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14102138157253182013406429 5288301808969943255027411)
      ·
        refine ⟨7932452713454914882541117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288301808969943255027411 7932452713454914882541117)
        ·
          refine ⟨2974669767545593080952919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7932452713454914882541117 2974669767545593080952919)
          ·
            refine ⟨4462004651318389621429379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974669767545593080952919 4462004651318389621429379)
            ·
              refine ⟨6693006976977584432144069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462004651318389621429379 6693006976977584432144069)
              ·
                refine ⟨1254938808183297081027013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6693006976977584432144069 1254938808183297081027013)
                ·
                  refine ⟨235301026534368202692565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254938808183297081027013 235301026534368202692565)
                  ·
                    rfl

theorem cell20_515528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_515528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515528 prefixEnd_515528 := by exact prefixLift 515528
  have htrace : WordTrace (prefixWord ++ tailWord_515528) baseStart_515528 baseEnd_515528 := by
    simpa [prefixWord, tailWord_515528, baseEnd_515528] using wordTrace_append hprefix tailTrace_515528
  have hstable : (prefixWord ++ tailWord_515528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515528).length < 2 ^ (prefixWord ++ tailWord_515528).sum := by decide
  have hdescent : baseEnd_515528 < baseStart_515528 := by decide
  rcases family_descends (prefixWord ++ tailWord_515528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515559 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_515559 : Nat := 118140960795 + 515559 * 2 ^ 59
def prefixEnd_515559 : Nat := 4983230072969 + 3 ^ 40 * 515559 * 2
def baseEnd_515559 : Nat := 235315175779069872659105

theorem tailTrace_515559 : CollatzResearch.WordTrace tailWord_515559 prefixEnd_515559 235315175779069872659105 := by
  unfold tailWord_515559
  simp only [CollatzResearch.WordTrace]
  refine ⟨18803981539225268312253731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12535987692816845541502487 18803981539225268312253731)
  ·
    refine ⟨28205972308837902468380597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18803981539225268312253731 28205972308837902468380597)
    ·
      refine ⟨2644309903953553356410681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28205972308837902468380597 2644309903953553356410681)
      ·
        refine ⟨1983232427965165017308011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2644309903953553356410681 1983232427965165017308011)
        ·
          refine ⟨2974848641947747525962017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983232427965165017308011 2974848641947747525962017)
          ·
            refine ⟨2231136481460810644471513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974848641947747525962017 2231136481460810644471513)
            ·
              refine ⟨1673352361095607983353635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231136481460810644471513 1673352361095607983353635)
              ·
                refine ⟨2510028541643411975030453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673352361095607983353635 2510028541643411975030453)
                ·
                  refine ⟨235315175779069872659105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510028541643411975030453 235315175779069872659105)
                  ·
                    rfl

theorem cell20_515559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_515559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515559 prefixEnd_515559 := by exact prefixLift 515559
  have htrace : WordTrace (prefixWord ++ tailWord_515559) baseStart_515559 baseEnd_515559 := by
    simpa [prefixWord, tailWord_515559, baseEnd_515559] using wordTrace_append hprefix tailTrace_515559
  have hstable : (prefixWord ++ tailWord_515559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515559).length < 2 ^ (prefixWord ++ tailWord_515559).sum := by decide
  have hdescent : baseEnd_515559 < baseStart_515559 := by decide
  rcases family_descends (prefixWord ++ tailWord_515559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515562 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_515562 : Nat := 118140960795 + 515562 * 2 ^ 59
def prefixEnd_515562 : Nat := 4983230072969 + 3 ^ 40 * 515562 * 2
def baseEnd_515562 : Nat := 235316545060815195559093

theorem tailTrace_515562 : CollatzResearch.WordTrace tailWord_515562 prefixEnd_515562 235316545060815195559093 := by
  unfold tailWord_515562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701022739553599956153235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12536060638809599883075293 4701022739553599956153235)
  ·
    refine ⟨7051534109330399934229853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4701022739553599956153235 7051534109330399934229853)
    ·
      refine ⟨2644325290998899975336195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7051534109330399934229853 2644325290998899975336195)
      ·
        refine ⟨3966487936498349963004293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644325290998899975336195 3966487936498349963004293)
        ·
          refine ⟨743716488093440618063305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3966487936498349963004293 743716488093440618063305)
          ·
            refine ⟨557787366070080463547479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743716488093440618063305 557787366070080463547479)
            ·
              refine ⟨836681049105120695321219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557787366070080463547479 836681049105120695321219)
              ·
                refine ⟨1255021573657681042981829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836681049105120695321219 1255021573657681042981829)
                ·
                  refine ⟨235316545060815195559093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255021573657681042981829 235316545060815195559093)
                  ·
                    rfl

theorem cell20_515562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_515562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515562 prefixEnd_515562 := by exact prefixLift 515562
  have htrace : WordTrace (prefixWord ++ tailWord_515562) baseStart_515562 baseEnd_515562 := by
    simpa [prefixWord, tailWord_515562, baseEnd_515562] using wordTrace_append hprefix tailTrace_515562
  have hstable : (prefixWord ++ tailWord_515562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515562).length < 2 ^ (prefixWord ++ tailWord_515562).sum := by decide
  have hdescent : baseEnd_515562 < baseStart_515562 := by decide
  rcases family_descends (prefixWord ++ tailWord_515562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515576 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_515576 : Nat := 118140960795 + 515576 * 2 ^ 59
def prefixEnd_515576 : Nat := 4983230072969 + 3 ^ 40 * 515576 * 2
def baseEnd_515576 : Nat := 235322935042293369092369

theorem tailTrace_515576 : CollatzResearch.WordTrace tailWord_515576 prefixEnd_515576 235322935042293369092369 := by
  unfold tailWord_515576
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402300790081840107811291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12536401053442453477081721 9402300790081840107811291)
  ·
    refine ⟨14103451185122760161716937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9402300790081840107811291 14103451185122760161716937)
    ·
      refine ⟨10577588388842070121287703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14103451185122760161716937 10577588388842070121287703)
      ·
        refine ⟨15866382583263105181931555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10577588388842070121287703 15866382583263105181931555)
        ·
          refine ⟨23799573874894657772897333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15866382583263105181931555 23799573874894657772897333)
          ·
            refine ⟨2231210050771374166209125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23799573874894657772897333 2231210050771374166209125)
            ·
              refine ⟨418351884519632656164211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2231210050771374166209125 418351884519632656164211)
              ·
                refine ⟨627527826779448984246317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418351884519632656164211 627527826779448984246317)
                ·
                  refine ⟨235322935042293369092369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627527826779448984246317 235322935042293369092369)
                  ·
                    rfl

theorem cell20_515576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_515576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515576 prefixEnd_515576 := by exact prefixLift 515576
  have htrace : WordTrace (prefixWord ++ tailWord_515576) baseStart_515576 baseEnd_515576 := by
    simpa [prefixWord, tailWord_515576, baseEnd_515576] using wordTrace_append hprefix tailTrace_515576
  have hstable : (prefixWord ++ tailWord_515576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515576).length < 2 ^ (prefixWord ++ tailWord_515576).sum := by decide
  have hdescent : baseEnd_515576 < baseStart_515576 := by decide
  rcases family_descends (prefixWord ++ tailWord_515576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515617 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 2]
def baseStart_515617 : Nat := 118140960795 + 515617 * 2 ^ 59
def prefixEnd_515617 : Nat := 4983230072969 + 3 ^ 40 * 515617 * 2
def baseEnd_515617 : Nat := 235341648559479448725535

theorem tailTrace_515617 : CollatzResearch.WordTrace tailWord_515617 prefixEnd_515617 235341648559479448725535 := by
  unfold tailWord_515617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806096973015144217865105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12537397982010096145243403 18806096973015144217865105)
  ·
    refine ⟨14104572729761358163398829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18806096973015144217865105 14104572729761358163398829)
    ·
      refine ⟨5289214773660509311274561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14104572729761358163398829 5289214773660509311274561)
      ·
        refine ⟨3966911080245381983455921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5289214773660509311274561 3966911080245381983455921)
        ·
          refine ⟨2975183310184036487591941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966911080245381983455921 2975183310184036487591941)
          ·
            refine ⟨557846870659506841423489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2975183310184036487591941 557846870659506841423489)
            ·
              refine ⟨418385152994630131067617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557846870659506841423489 418385152994630131067617)
              ·
                refine ⟨313788864745972598300713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418385152994630131067617 313788864745972598300713)
                ·
                  refine ⟨235341648559479448725535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313788864745972598300713 235341648559479448725535)
                  ·
                    rfl

theorem cell20_515617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_515617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515617 prefixEnd_515617 := by exact prefixLift 515617
  have htrace : WordTrace (prefixWord ++ tailWord_515617) baseStart_515617 baseEnd_515617 := by
    simpa [prefixWord, tailWord_515617, baseEnd_515617] using wordTrace_append hprefix tailTrace_515617
  have hstable : (prefixWord ++ tailWord_515617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515617).length < 2 ^ (prefixWord ++ tailWord_515617).sum := by decide
  have hdescent : baseEnd_515617 < baseStart_515617 := by decide
  rcases family_descends (prefixWord ++ tailWord_515617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515624 : List Nat := [2, 1, 5, 2, 3, 1, 1, 5]
def baseStart_515624 : Nat := 118140960795 + 515624 * 2 ^ 59
def prefixEnd_515624 : Nat := 4983230072969 + 3 ^ 40 * 515624 * 2
def baseEnd_515624 : Nat := 78448281183406178497391

theorem tailTrace_515624 : CollatzResearch.WordTrace tailWord_515624 prefixEnd_515624 78448281183406178497391 := by
  unfold tailWord_515624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403176141994892206684963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12537568189326522942246617 9403176141994892206684963)
  ·
    refine ⟨14104764212992338310027445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9403176141994892206684963 14104764212992338310027445)
    ·
      refine ⟨1322321644968031716565073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14104764212992338310027445 1322321644968031716565073)
      ·
        refine ⟨991741233726023787423805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322321644968031716565073 991741233726023787423805)
        ·
          refine ⟨371902962647258920283927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 991741233726023787423805 371902962647258920283927)
          ·
            refine ⟨557854443970888380425891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371902962647258920283927 557854443970888380425891)
            ·
              refine ⟨836781665956332570638837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557854443970888380425891 836781665956332570638837)
              ·
                refine ⟨78448281183406178497391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 836781665956332570638837 78448281183406178497391)
                ·
                  rfl

theorem cell20_515624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_515624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515624 prefixEnd_515624 := by exact prefixLift 515624
  have htrace : WordTrace (prefixWord ++ tailWord_515624) baseStart_515624 baseEnd_515624 := by
    simpa [prefixWord, tailWord_515624, baseEnd_515624] using wordTrace_append hprefix tailTrace_515624
  have hstable : (prefixWord ++ tailWord_515624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515624).length < 2 ^ (prefixWord ++ tailWord_515624).sum := by decide
  have hdescent : baseEnd_515624 < baseStart_515624 := by decide
  rcases family_descends (prefixWord ++ tailWord_515624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515635 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_515635 : Nat := 118140960795 + 515635 * 2 ^ 59
def prefixEnd_515635 : Nat := 4983230072969 + 3 ^ 40 * 515635 * 2
def baseEnd_515635 : Nat := 235349864249951386125461

theorem tailTrace_515635 : CollatzResearch.WordTrace tailWord_515635 prefixEnd_515635 235349864249951386125461 := by
  unfold tailWord_515635
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806753486949933292020359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12537835657966622194680239 18806753486949933292020359)
  ·
    refine ⟨28210130230424899938030539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18806753486949933292020359 28210130230424899938030539)
    ·
      refine ⟨42315195345637349907045809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28210130230424899938030539 42315195345637349907045809)
      ·
        refine ⟨31736396509228012430284357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42315195345637349907045809 31736396509228012430284357)
        ·
          refine ⟨5950574345480252330678317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31736396509228012430284357 5950574345480252330678317)
          ·
            refine ⟨2231465379555094624004369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5950574345480252330678317 2231465379555094624004369)
            ·
              refine ⟨1673599034666320968003277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231465379555094624004369 1673599034666320968003277)
              ·
                refine ⟨627599637999870363001229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673599034666320968003277 627599637999870363001229)
                ·
                  refine ⟨235349864249951386125461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627599637999870363001229 235349864249951386125461)
                  ·
                    rfl

theorem cell20_515635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_515635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515635 prefixEnd_515635 := by exact prefixLift 515635
  have htrace : WordTrace (prefixWord ++ tailWord_515635) baseStart_515635 baseEnd_515635 := by
    simpa [prefixWord, tailWord_515635, baseEnd_515635] using wordTrace_append hprefix tailTrace_515635
  have hstable : (prefixWord ++ tailWord_515635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515635).length < 2 ^ (prefixWord ++ tailWord_515635).sum := by decide
  have hdescent : baseEnd_515635 < baseStart_515635 := by decide
  rcases family_descends (prefixWord ++ tailWord_515635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515638 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_515638 : Nat := 118140960795 + 515638 * 2 ^ 59
def prefixEnd_515638 : Nat := 4983230072969 + 3 ^ 40 * 515638 * 2
def baseEnd_515638 : Nat := 235351233531696709025449

theorem tailTrace_515638 : CollatzResearch.WordTrace tailWord_515638 prefixEnd_515638 235351233531696709025449 := by
  unfold tailWord_515638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175428931621191550273723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12537908603959376536253045 1175428931621191550273723)
  ·
    refine ⟨1763143397431787325410585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175428931621191550273723 1763143397431787325410585)
    ·
      refine ⟨1322357548073840494057939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763143397431787325410585 1322357548073840494057939)
      ·
        refine ⟨1983536322110760741086909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322357548073840494057939 1983536322110760741086909)
        ·
          refine ⟨743826120791535277907591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1983536322110760741086909 743826120791535277907591)
          ·
            refine ⟨1115739181187302916861387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743826120791535277907591 1115739181187302916861387)
            ·
              refine ⟨1673608771780954375292081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115739181187302916861387 1673608771780954375292081)
              ·
                refine ⟨1255206578835715781469061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673608771780954375292081 1255206578835715781469061)
                ·
                  refine ⟨235351233531696709025449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255206578835715781469061 235351233531696709025449)
                  ·
                    rfl

theorem cell20_515638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_515638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515638 prefixEnd_515638 := by exact prefixLift 515638
  have htrace : WordTrace (prefixWord ++ tailWord_515638) baseStart_515638 baseEnd_515638 := by
    simpa [prefixWord, tailWord_515638, baseEnd_515638] using wordTrace_append hprefix tailTrace_515638
  have hstable : (prefixWord ++ tailWord_515638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515638).length < 2 ^ (prefixWord ++ tailWord_515638).sum := by decide
  have hdescent : baseEnd_515638 < baseStart_515638 := by decide
  rcases family_descends (prefixWord ++ tailWord_515638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515642 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_515642 : Nat := 118140960795 + 515642 * 2 ^ 59
def prefixEnd_515642 : Nat := 4983230072969 + 3 ^ 40 * 515642 * 2
def baseEnd_515642 : Nat := 235353059240690472892099

theorem tailTrace_515642 : CollatzResearch.WordTrace tailWord_515642 prefixEnd_515642 235353059240690472892099 := by
  unfold tailWord_515642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701752199481143371881295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12538005865283048991683453 4701752199481143371881295)
  ·
    refine ⟨7052628299221715057821943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4701752199481143371881295 7052628299221715057821943)
    ·
      refine ⟨10578942448832572586732915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052628299221715057821943 10578942448832572586732915)
      ·
        refine ⟨15868413673248858880099373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578942448832572586732915 15868413673248858880099373)
        ·
          refine ⟨5950655127468322080037265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15868413673248858880099373 5950655127468322080037265)
          ·
            refine ⟨4462991345601241560027949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5950655127468322080037265 4462991345601241560027949)
            ·
              refine ⟨1673621754600465585010481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4462991345601241560027949 1673621754600465585010481)
              ·
                refine ⟨1255216315950349188757861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673621754600465585010481 1255216315950349188757861)
                ·
                  refine ⟨235353059240690472892099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255216315950349188757861 235353059240690472892099)
                  ·
                    rfl

theorem cell20_515642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_515642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515642 prefixEnd_515642 := by exact prefixLift 515642
  have htrace : WordTrace (prefixWord ++ tailWord_515642) baseStart_515642 baseEnd_515642 := by
    simpa [prefixWord, tailWord_515642, baseEnd_515642] using wordTrace_append hprefix tailTrace_515642
  have hstable : (prefixWord ++ tailWord_515642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515642).length < 2 ^ (prefixWord ++ tailWord_515642).sum := by decide
  have hdescent : baseEnd_515642 < baseStart_515642 := by decide
  rcases family_descends (prefixWord ++ tailWord_515642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515645 : List Nat := [1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_515645 : Nat := 118140960795 + 515645 * 2 ^ 59
def prefixEnd_515645 : Nat := 4983230072969 + 3 ^ 40 * 515645 * 2
def baseEnd_515645 : Nat := 78451476174145265264029

theorem tailTrace_515645 : CollatzResearch.WordTrace tailWord_515645 prefixEnd_515645 78451476174145265264029 := by
  unfold tailWord_515645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18807118216913704999884389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12538078811275803333256259 18807118216913704999884389)
  ·
    refine ⟨3526334665671319687478323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18807118216913704999884389 3526334665671319687478323)
    ·
      refine ⟨5289501998506979531217485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3526334665671319687478323 5289501998506979531217485)
      ·
        refine ⟨1983563249440117324206557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5289501998506979531217485 1983563249440117324206557)
        ·
          refine ⟨743836218540043996577459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1983563249440117324206557 743836218540043996577459)
          ·
            refine ⟨1115754327810065994866189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743836218540043996577459 1115754327810065994866189)
            ·
              refine ⟨418407872928774748074821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115754327810065994866189 418407872928774748074821)
              ·
                refine ⟨78451476174145265264029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418407872928774748074821 78451476174145265264029)
                ·
                  rfl

theorem cell20_515645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_515645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515645 prefixEnd_515645 := by exact prefixLift 515645
  have htrace : WordTrace (prefixWord ++ tailWord_515645) baseStart_515645 baseEnd_515645 := by
    simpa [prefixWord, tailWord_515645, baseEnd_515645] using wordTrace_append hprefix tailTrace_515645
  have hstable : (prefixWord ++ tailWord_515645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515645).length < 2 ^ (prefixWord ++ tailWord_515645).sum := by decide
  have hdescent : baseEnd_515645 < baseStart_515645 := by decide
  rcases family_descends (prefixWord ++ tailWord_515645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515663 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_515663 : Nat := 118140960795 + 515663 * 2 ^ 59
def prefixEnd_515663 : Nat := 4983230072969 + 3 ^ 40 * 515663 * 2
def baseEnd_515663 : Nat := 235362644212907733192013

theorem tailTrace_515663 : CollatzResearch.WordTrace tailWord_515663 prefixEnd_515663 235362644212907733192013 := by
  unfold tailWord_515663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18807774730848494074039643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12538516487232329382693095 18807774730848494074039643)
  ·
    refine ⟨28211662096272741111059465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18807774730848494074039643 28211662096272741111059465)
    ·
      refine ⟨21158746572204555833294599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28211662096272741111059465 21158746572204555833294599)
      ·
        refine ⟨31738119858306833749941899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21158746572204555833294599 31738119858306833749941899)
        ·
          refine ⟨47607179787460250624912849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31738119858306833749941899 47607179787460250624912849)
          ·
            refine ⟨35705384840595187968684637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47607179787460250624912849 35705384840595187968684637)
            ·
              refine ⟨13389519315223195488256739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35705384840595187968684637 13389519315223195488256739)
              ·
                refine ⟨20084278972834793232385109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389519315223195488256739 20084278972834793232385109)
                ·
                  refine ⟨235362644212907733192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20084278972834793232385109 235362644212907733192013)
                  ·
                    rfl

theorem cell20_515663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_515663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515663 prefixEnd_515663 := by exact prefixLift 515663
  have htrace : WordTrace (prefixWord ++ tailWord_515663) baseStart_515663 baseEnd_515663 := by
    simpa [prefixWord, tailWord_515663, baseEnd_515663] using wordTrace_append hprefix tailTrace_515663
  have hstable : (prefixWord ++ tailWord_515663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515663).length < 2 ^ (prefixWord ++ tailWord_515663).sum := by decide
  have hdescent : baseEnd_515663 < baseStart_515663 := by decide
  rcases family_descends (prefixWord ++ tailWord_515663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515676 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_515676 : Nat := 118140960795 + 515676 * 2 ^ 59
def prefixEnd_515676 : Nat := 4983230072969 + 3 ^ 40 * 515676 * 2
def baseEnd_515676 : Nat := 235368577767137465758627

theorem tailTrace_515676 : CollatzResearch.WordTrace tailWord_515676 prefixEnd_515676 235368577767137465758627 := by
  unfold tailWord_515676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404124439900698647131441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12538832586534264862841921 9404124439900698647131441)
  ·
    refine ⟨7053093329925523985348581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9404124439900698647131441 7053093329925523985348581)
    ·
      refine ⟨1322454999361035747252859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7053093329925523985348581 1322454999361035747252859)
      ·
        refine ⟨1983682499041553620879289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322454999361035747252859 1983682499041553620879289)
        ·
          refine ⟨1487761874281165215659467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983682499041553620879289 1487761874281165215659467)
          ·
            refine ⟨2231642811421747823489201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487761874281165215659467 2231642811421747823489201)
            ·
              refine ⟨1673732108566310867616901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231642811421747823489201 1673732108566310867616901)
              ·
                refine ⟨313824770356183287678169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1673732108566310867616901 313824770356183287678169)
                ·
                  refine ⟨235368577767137465758627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313824770356183287678169 235368577767137465758627)
                  ·
                    rfl

theorem cell20_515676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_515676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515676 prefixEnd_515676 := by exact prefixLift 515676
  have htrace : WordTrace (prefixWord ++ tailWord_515676) baseStart_515676 baseEnd_515676 := by
    simpa [prefixWord, tailWord_515676, baseEnd_515676] using wordTrace_append hprefix tailTrace_515676
  have hstable : (prefixWord ++ tailWord_515676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515676).length < 2 ^ (prefixWord ++ tailWord_515676).sum := by decide
  have hdescent : baseEnd_515676 < baseStart_515676 := by decide
  rcases family_descends (prefixWord ++ tailWord_515676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515735 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_515735 : Nat := 118140960795 + 515735 * 2 ^ 59
def prefixEnd_515735 : Nat := 4983230072969 + 3 ^ 40 * 515735 * 2
def baseEnd_515735 : Nat := 235395506974795482791719

theorem tailTrace_515735 : CollatzResearch.WordTrace tailWord_515735 prefixEnd_515735 235395506974795482791719 := by
  unfold tailWord_515735
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810400786587650370660659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12540267191058433580440439 18810400786587650370660659)
  ·
    refine ⟨28215601179881475555990989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18810400786587650370660659 28215601179881475555990989)
    ·
      refine ⟨10580850442455553333496621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28215601179881475555990989 10580850442455553333496621)
      ·
        refine ⟨3967818915920832500061233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10580850442455553333496621 3967818915920832500061233)
        ·
          refine ⟨2975864186940624375045925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3967818915920832500061233 2975864186940624375045925)
          ·
            refine ⟨557974535051367070321111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2975864186940624375045925 557974535051367070321111)
            ·
              refine ⟨836961802577050605481667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557974535051367070321111 836961802577050605481667)
              ·
                refine ⟨1255442703865575908222501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836961802577050605481667 1255442703865575908222501)
                ·
                  refine ⟨235395506974795482791719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255442703865575908222501 235395506974795482791719)
                  ·
                    rfl

theorem cell20_515735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_515735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515735 prefixEnd_515735 := by exact prefixLift 515735
  have htrace : WordTrace (prefixWord ++ tailWord_515735) baseStart_515735 baseEnd_515735 := by
    simpa [prefixWord, tailWord_515735, baseEnd_515735] using wordTrace_append hprefix tailTrace_515735
  have hstable : (prefixWord ++ tailWord_515735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515735).length < 2 ^ (prefixWord ++ tailWord_515735).sum := by decide
  have hdescent : baseEnd_515735 < baseStart_515735 := by decide
  rcases family_descends (prefixWord ++ tailWord_515735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515742 : List Nat := [4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_515742 : Nat := 118140960795 + 515742 * 2 ^ 59
def prefixEnd_515742 : Nat := 4983230072969 + 3 ^ 40 * 515742 * 2
def baseEnd_515742 : Nat := 78466233988511523186119

theorem tailTrace_515742 : CollatzResearch.WordTrace tailWord_515742 prefixEnd_515742 78466233988511523186119 := by
  unfold tailWord_515742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351332012195286320770685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12540437398374860377443653 2351332012195286320770685)
  ·
    refine ⟨881749504573232370289007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2351332012195286320770685 881749504573232370289007)
    ·
      refine ⟨1322624256859848555433511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881749504573232370289007 1322624256859848555433511)
      ·
        refine ⟨1983936385289772833150267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322624256859848555433511 1983936385289772833150267)
        ·
          refine ⟨2975904577934659249725401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983936385289772833150267 2975904577934659249725401)
          ·
            refine ⟨2231928433450994437294051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975904577934659249725401 2231928433450994437294051)
            ·
              refine ⟨3347892650176491655941077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231928433450994437294051 3347892650176491655941077)
              ·
                refine ⟨78466233988511523186119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3347892650176491655941077 78466233988511523186119)
                ·
                  rfl

theorem cell20_515742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_515742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515742 prefixEnd_515742 := by exact prefixLift 515742
  have htrace : WordTrace (prefixWord ++ tailWord_515742) baseStart_515742 baseEnd_515742 := by
    simpa [prefixWord, tailWord_515742, baseEnd_515742] using wordTrace_append hprefix tailTrace_515742
  have hstable : (prefixWord ++ tailWord_515742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515742).length < 2 ^ (prefixWord ++ tailWord_515742).sum := by decide
  have hdescent : baseEnd_515742 < baseStart_515742 := by decide
  rcases family_descends (prefixWord ++ tailWord_515742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515745 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 3]
def baseStart_515745 : Nat := 118140960795 + 515745 * 2 ^ 59
def prefixEnd_515745 : Nat := 4983230072969 + 3 ^ 40 * 515745 * 2
def baseEnd_515745 : Nat := 235400071247279892458345

theorem tailTrace_515745 : CollatzResearch.WordTrace tailWord_515745 prefixEnd_515745 235400071247279892458345 := by
  unfold tailWord_515745
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810765516551422078524689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12540510344367614719016459 18810765516551422078524689)
  ·
    refine ⟨14108074137413566558893517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18810765516551422078524689 14108074137413566558893517)
    ·
      refine ⟨5290527801530087459585069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14108074137413566558893517 5290527801530087459585069)
      ·
        refine ⟨1983947925573782797344401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5290527801530087459585069 1983947925573782797344401)
        ·
          refine ⟨1487960944180337098008301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983947925573782797344401 1487960944180337098008301)
          ·
            refine ⟨557985354067626411753113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1487960944180337098008301 557985354067626411753113)
            ·
              refine ⟨418489015550719808814835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557985354067626411753113 418489015550719808814835)
              ·
                refine ⟨627733523326079713222253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418489015550719808814835 627733523326079713222253)
                ·
                  refine ⟨235400071247279892458345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627733523326079713222253 235400071247279892458345)
                  ·
                    rfl

theorem cell20_515745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_515745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515745 prefixEnd_515745 := by exact prefixLift 515745
  have htrace : WordTrace (prefixWord ++ tailWord_515745) baseStart_515745 baseEnd_515745 := by
    simpa [prefixWord, tailWord_515745, baseEnd_515745] using wordTrace_append hprefix tailTrace_515745
  have hstable : (prefixWord ++ tailWord_515745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515745).length < 2 ^ (prefixWord ++ tailWord_515745).sum := by decide
  have hdescent : baseEnd_515745 < baseStart_515745 := by decide
  rcases family_descends (prefixWord ++ tailWord_515745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515773 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 2]
def baseStart_515773 : Nat := 118140960795 + 515773 * 2 ^ 59
def prefixEnd_515773 : Nat := 4983230072969 + 3 ^ 40 * 515773 * 2
def baseEnd_515773 : Nat := 235412851210236239524897

theorem tailTrace_515773 : CollatzResearch.WordTrace tailWord_515773 prefixEnd_515773 235412851210236239524897 := by
  unfold tailWord_515773
  simp only [CollatzResearch.WordTrace]
  refine ⟨18811786760449982860543973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12541191173633321907029315 18811786760449982860543973)
  ·
    refine ⟨3527210017584371786351995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18811786760449982860543973 3527210017584371786351995)
    ·
      refine ⟨5290815026376557679527993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527210017584371786351995 5290815026376557679527993)
      ·
        refine ⟨3968111269782418259645995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5290815026376557679527993 3968111269782418259645995)
        ·
          refine ⟨5952166904673627389468993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968111269782418259645995 5952166904673627389468993)
          ·
            refine ⟨4464125178505220542101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5952166904673627389468993 4464125178505220542101745)
            ·
              refine ⟨3348093883878915406576309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464125178505220542101745 3348093883878915406576309)
              ·
                refine ⟨313883801613648319366529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3348093883878915406576309 313883801613648319366529)
                ·
                  refine ⟨235412851210236239524897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313883801613648319366529 235412851210236239524897)
                  ·
                    rfl

theorem cell20_515773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_515773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515773 prefixEnd_515773 := by exact prefixLift 515773
  have htrace : WordTrace (prefixWord ++ tailWord_515773) baseStart_515773 baseEnd_515773 := by
    simpa [prefixWord, tailWord_515773, baseEnd_515773] using wordTrace_append hprefix tailTrace_515773
  have hstable : (prefixWord ++ tailWord_515773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515773).length < 2 ^ (prefixWord ++ tailWord_515773).sum := by decide
  have hdescent : baseEnd_515773 < baseStart_515773 := by decide
  rcases family_descends (prefixWord ++ tailWord_515773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515786 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_515786 : Nat := 118140960795 + 515786 * 2 ^ 59
def prefixEnd_515786 : Nat := 4983230072969 + 3 ^ 40 * 515786 * 2
def baseEnd_515786 : Nat := 235418784764465972091511

theorem tailTrace_515786 : CollatzResearch.WordTrace tailWord_515786 prefixEnd_515786 235418784764465972091511 := by
  unfold tailWord_515786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703065227350721520191803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12541507272935257387178141 4703065227350721520191803)
  ·
    refine ⟨7054597841026082280287705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4703065227350721520191803 7054597841026082280287705)
    ·
      refine ⟨5290948380769561710215779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7054597841026082280287705 5290948380769561710215779)
      ·
        refine ⟨7936422571154342565323669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290948380769561710215779 7936422571154342565323669)
        ·
          refine ⟨372019808022859807749547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7936422571154342565323669 372019808022859807749547)
          ·
            refine ⟨558029712034289711624321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372019808022859807749547 558029712034289711624321)
            ·
              refine ⟨418522284025717283718241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558029712034289711624321 418522284025717283718241)
              ·
                refine ⟨313891713019287962788681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418522284025717283718241 313891713019287962788681)
                ·
                  refine ⟨235418784764465972091511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313891713019287962788681 235418784764465972091511)
                  ·
                    rfl

theorem cell20_515786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_515786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515786 prefixEnd_515786 := by exact prefixLift 515786
  have htrace : WordTrace (prefixWord ++ tailWord_515786) baseStart_515786 baseEnd_515786 := by
    simpa [prefixWord, tailWord_515786, baseEnd_515786] using wordTrace_append hprefix tailTrace_515786
  have hstable : (prefixWord ++ tailWord_515786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515786).length < 2 ^ (prefixWord ++ tailWord_515786).sum := by decide
  have hdescent : baseEnd_515786 < baseStart_515786 := by decide
  rcases family_descends (prefixWord ++ tailWord_515786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515801 : List Nat := [1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_515801 : Nat := 118140960795 + 515801 * 2 ^ 59
def prefixEnd_515801 : Nat := 4983230072969 + 3 ^ 40 * 515801 * 2
def baseEnd_515801 : Nat := 78475210391064195530483

theorem tailTrace_515801 : CollatzResearch.WordTrace tailWord_515801 prefixEnd_515801 78475210391064195530483 := by
  unfold tailWord_515801
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812808004348543642563257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12541872002899029095042171 18812808004348543642563257)
  ·
    refine ⟨14109606003261407731922443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812808004348543642563257 14109606003261407731922443)
    ·
      refine ⟨21164409004892111597883665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14109606003261407731922443 21164409004892111597883665)
      ·
        refine ⟨15873306753669083698412749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21164409004892111597883665 15873306753669083698412749)
        ·
          refine ⟨5952490032625906386904781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15873306753669083698412749 5952490032625906386904781)
          ·
            refine ⟨2232183762234714895089293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5952490032625906386904781 2232183762234714895089293)
            ·
              refine ⟨837068910838018085658485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232183762234714895089293 837068910838018085658485)
              ·
                refine ⟨78475210391064195530483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 837068910838018085658485 78475210391064195530483)
                ·
                  rfl

theorem cell20_515801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_515801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515801 prefixEnd_515801 := by exact prefixLift 515801
  have htrace : WordTrace (prefixWord ++ tailWord_515801) baseStart_515801 baseEnd_515801 := by
    simpa [prefixWord, tailWord_515801, baseEnd_515801] using wordTrace_append hprefix tailTrace_515801
  have hstable : (prefixWord ++ tailWord_515801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515801).length < 2 ^ (prefixWord ++ tailWord_515801).sum := by decide
  have hdescent : baseEnd_515801 < baseStart_515801 := by decide
  rcases family_descends (prefixWord ++ tailWord_515801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515811 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_515811 : Nat := 118140960795 + 515811 * 2 ^ 59
def prefixEnd_515811 : Nat := 4983230072969 + 3 ^ 40 * 515811 * 2
def baseEnd_515811 : Nat := 235430195445676996258075

theorem tailTrace_515811 : CollatzResearch.WordTrace tailWord_515811 prefixEnd_515811 235430195445676996258075 := by
  unfold tailWord_515811
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813172734312315350427287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542115156208210233618191 18813172734312315350427287)
  ·
    refine ⟨28219759101468473025640931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813172734312315350427287 28219759101468473025640931)
    ·
      refine ⟨42329638652202709538461397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28219759101468473025640931 42329638652202709538461397)
      ·
        refine ⟨992100905911001004807689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42329638652202709538461397 992100905911001004807689)
        ·
          refine ⟨744075679433250753605767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992100905911001004807689 744075679433250753605767)
          ·
            refine ⟨1116113519149876130408651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744075679433250753605767 1116113519149876130408651)
            ·
              refine ⟨1674170278724814195612977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116113519149876130408651 1674170278724814195612977)
              ·
                refine ⟨1255627709043610646709733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674170278724814195612977 1255627709043610646709733)
                ·
                  refine ⟨235430195445676996258075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255627709043610646709733 235430195445676996258075)
                  ·
                    rfl

theorem cell20_515811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_515811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515811 prefixEnd_515811 := by exact prefixLift 515811
  have htrace : WordTrace (prefixWord ++ tailWord_515811) baseStart_515811 baseEnd_515811 := by
    simpa [prefixWord, tailWord_515811, baseEnd_515811] using wordTrace_append hprefix tailTrace_515811
  have hstable : (prefixWord ++ tailWord_515811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515811).length < 2 ^ (prefixWord ++ tailWord_515811).sum := by decide
  have hdescent : baseEnd_515811 < baseStart_515811 := by decide
  rcases family_descends (prefixWord ++ tailWord_515811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515838 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_515838 : Nat := 118140960795 + 515838 * 2 ^ 59
def prefixEnd_515838 : Nat := 4983230072969 + 3 ^ 40 * 515838 * 2
def baseEnd_515838 : Nat := 235442518981384902357965

theorem tailTrace_515838 : CollatzResearch.WordTrace tailWord_515838 prefixEnd_515838 235442518981384902357965 := by
  unfold tailWord_515838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351769688151812370207521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12542771670142999307773445 2351769688151812370207521)
  ·
    refine ⟨1763827266113859277655641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351769688151812370207521 1763827266113859277655641)
    ·
      refine ⟨1322870449585394458241731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763827266113859277655641 1322870449585394458241731)
      ·
        refine ⟨1984305674378091687362597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322870449585394458241731 1984305674378091687362597)
        ·
          refine ⟨372057313945892191380487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1984305674378091687362597 372057313945892191380487)
          ·
            refine ⟨558085970918838287070731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372057313945892191380487 558085970918838287070731)
            ·
              refine ⟨837128956378257430606097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558085970918838287070731 837128956378257430606097)
              ·
                refine ⟨627846717283693072954573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837128956378257430606097 627846717283693072954573)
                ·
                  refine ⟨235442518981384902357965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627846717283693072954573 235442518981384902357965)
                  ·
                    rfl

theorem cell20_515838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_515838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515838 prefixEnd_515838 := by exact prefixLift 515838
  have htrace : WordTrace (prefixWord ++ tailWord_515838) baseStart_515838 baseEnd_515838 := by
    simpa [prefixWord, tailWord_515838, baseEnd_515838] using wordTrace_append hprefix tailTrace_515838
  have hstable : (prefixWord ++ tailWord_515838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515838).length < 2 ^ (prefixWord ++ tailWord_515838).sum := by decide
  have hdescent : baseEnd_515838 < baseStart_515838 := by decide
  rcases family_descends (prefixWord ++ tailWord_515838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515877 : List Nat := [1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_515877 : Nat := 118140960795 + 515877 * 2 ^ 59
def prefixEnd_515877 : Nat := 4983230072969 + 3 ^ 40 * 515877 * 2
def baseEnd_515877 : Nat := 78486773214691366685935

theorem tailTrace_515877 : CollatzResearch.WordTrace tailWord_515877 prefixEnd_515877 78486773214691366685935 := by
  unfold tailWord_515877
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815579952073208622329885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12543719968048805748219923 18815579952073208622329885)
  ·
    refine ⟨7055842482027453233373707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18815579952073208622329885 7055842482027453233373707)
    ·
      refine ⟨10583763723041179850060561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7055842482027453233373707 10583763723041179850060561)
      ·
        refine ⟨7937822792280884887545421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10583763723041179850060561 7937822792280884887545421)
        ·
          refine ⟨2976683547105331832829533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7937822792280884887545421 2976683547105331832829533)
          ·
            refine ⟨1116256330164499437311075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2976683547105331832829533 1116256330164499437311075)
            ·
              refine ⟨1674384495246749155966613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116256330164499437311075 1674384495246749155966613)
              ·
                refine ⟨78486773214691366685935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1674384495246749155966613 78486773214691366685935)
                ·
                  rfl

theorem cell20_515877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_515877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515877 prefixEnd_515877 := by exact prefixLift 515877
  have htrace : WordTrace (prefixWord ++ tailWord_515877) baseStart_515877 baseEnd_515877 := by
    simpa [prefixWord, tailWord_515877, baseEnd_515877] using wordTrace_append hprefix tailTrace_515877
  have hstable : (prefixWord ++ tailWord_515877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515877).length < 2 ^ (prefixWord ++ tailWord_515877).sum := by decide
  have hdescent : baseEnd_515877 < baseStart_515877 := by decide
  rcases family_descends (prefixWord ++ tailWord_515877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515884 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_515884 : Nat := 118140960795 + 515884 * 2 ^ 59
def prefixEnd_515884 : Nat := 4983230072969 + 3 ^ 40 * 515884 * 2
def baseEnd_515884 : Nat := 235463514634813186824443

theorem tailTrace_515884 : CollatzResearch.WordTrace tailWord_515884 prefixEnd_515884 235463514634813186824443 := by
  unfold tailWord_515884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407917631523924408917353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12543890175365232545223137 9407917631523924408917353)
  ·
    refine ⟨7055938223642943306688015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9407917631523924408917353 7055938223642943306688015)
    ·
      refine ⟨10583907335464414960032023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7055938223642943306688015 10583907335464414960032023)
      ·
        refine ⟨15875861003196622440048035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10583907335464414960032023 15875861003196622440048035)
        ·
          refine ⟨23813791504794933660072053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15875861003196622440048035 23813791504794933660072053)
          ·
            refine ⟨2232542953574525030631755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23813791504794933660072053 2232542953574525030631755)
            ·
              refine ⟨3348814430361787545947633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232542953574525030631755 3348814430361787545947633)
              ·
                refine ⟨2511610822771340659460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348814430361787545947633 2511610822771340659460725)
                ·
                  refine ⟨235463514634813186824443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2511610822771340659460725 235463514634813186824443)
                  ·
                    rfl

theorem cell20_515884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_515884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515884 prefixEnd_515884 := by exact prefixLift 515884
  have htrace : WordTrace (prefixWord ++ tailWord_515884) baseStart_515884 baseEnd_515884 := by
    simpa [prefixWord, tailWord_515884, baseEnd_515884] using wordTrace_append hprefix tailTrace_515884
  have hstable : (prefixWord ++ tailWord_515884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515884).length < 2 ^ (prefixWord ++ tailWord_515884).sum := by decide
  have hdescent : baseEnd_515884 < baseStart_515884 := by decide
  rcases family_descends (prefixWord ++ tailWord_515884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515894 : List Nat := [5, 1, 2, 2, 1, 1, 8]
def baseStart_515894 : Nat := 118140960795 + 515894 * 2 ^ 59
def prefixEnd_515894 : Nat := 4983230072969 + 3 ^ 40 * 515894 * 2
def baseEnd_515894 : Nat := 26163119878588621832341

theorem tailTrace_515894 : CollatzResearch.WordTrace tailWord_515894 prefixEnd_515894 26163119878588621832341 := by
  unfold tailWord_515894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176012499563226282856171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12544133328674413683799157 1176012499563226282856171)
  ·
    refine ⟨1764018749344839424284257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1176012499563226282856171 1764018749344839424284257)
    ·
      refine ⟨1323014062008629568213193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764018749344839424284257 1323014062008629568213193)
      ·
        refine ⟨992260546506472176159895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323014062008629568213193 992260546506472176159895)
        ·
          refine ⟨1488390819759708264239843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992260546506472176159895 1488390819759708264239843)
          ·
            refine ⟨2232586229639562396359765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488390819759708264239843 2232586229639562396359765)
            ·
              refine ⟨26163119878588621832341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2232586229639562396359765 26163119878588621832341)
              ·
                rfl

theorem cell20_515894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_515894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515894 prefixEnd_515894 := by exact prefixLift 515894
  have htrace : WordTrace (prefixWord ++ tailWord_515894) baseStart_515894 baseEnd_515894 := by
    simpa [prefixWord, tailWord_515894, baseEnd_515894] using wordTrace_append hprefix tailTrace_515894
  have hstable : (prefixWord ++ tailWord_515894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515894).length < 2 ^ (prefixWord ++ tailWord_515894).sum := by decide
  have hdescent : baseEnd_515894 < baseStart_515894 := by decide
  rcases family_descends (prefixWord ++ tailWord_515894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515901 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_515901 : Nat := 118140960795 + 515901 * 2 ^ 59
def prefixEnd_515901 : Nat := 4983230072969 + 3 ^ 40 * 515901 * 2
def baseEnd_515901 : Nat := 235471273898036683257707

theorem tailTrace_515901 : CollatzResearch.WordTrace tailWord_515901 prefixEnd_515901 235471273898036683257707 := by
  unfold tailWord_515901
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816455303986260721203557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12544303535990840480802371 18816455303986260721203557)
  ·
    refine ⟨3528085369497423885225667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18816455303986260721203557 3528085369497423885225667)
    ·
      refine ⟨5292128054246135827838501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528085369497423885225667 5292128054246135827838501)
      ·
        refine ⟨992274010171150467719719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5292128054246135827838501 992274010171150467719719)
        ·
          refine ⟨1488411015256725701579579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992274010171150467719719 1488411015256725701579579)
          ·
            refine ⟨2232616522885088552369369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488411015256725701579579 2232616522885088552369369)
            ·
              refine ⟨1674462392163816414277027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232616522885088552369369 1674462392163816414277027)
              ·
                refine ⟨2511693588245724621415541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674462392163816414277027 2511693588245724621415541)
                ·
                  refine ⟨235471273898036683257707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2511693588245724621415541 235471273898036683257707)
                  ·
                    rfl

theorem cell20_515901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_515901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515901 prefixEnd_515901 := by exact prefixLift 515901
  have htrace : WordTrace (prefixWord ++ tailWord_515901) baseStart_515901 baseEnd_515901 := by
    simpa [prefixWord, tailWord_515901, baseEnd_515901] using wordTrace_append hprefix tailTrace_515901
  have hstable : (prefixWord ++ tailWord_515901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515901).length < 2 ^ (prefixWord ++ tailWord_515901).sum := by decide
  have hdescent : baseEnd_515901 < baseStart_515901 := by decide
  rcases family_descends (prefixWord ++ tailWord_515901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515929 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_515929 : Nat := 118140960795 + 515929 * 2 ^ 59
def prefixEnd_515929 : Nat := 4983230072969 + 3 ^ 40 * 515929 * 2
def baseEnd_515929 : Nat := 235484053860993030324259

theorem tailTrace_515929 : CollatzResearch.WordTrace tailWord_515929 prefixEnd_515929 235484053860993030324259 := by
  unfold tailWord_515929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817476547884821503222841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12544984365256547668815227 18817476547884821503222841)
  ·
    refine ⟨14113107410913616127417131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18817476547884821503222841 14113107410913616127417131)
    ·
      refine ⟨21169661116370424191125697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14113107410913616127417131 21169661116370424191125697)
      ·
        refine ⟨15877245837277818143344273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21169661116370424191125697 15877245837277818143344273)
        ·
          refine ⟨11907934377958363607508205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15877245837277818143344273 11907934377958363607508205)
          ·
            refine ⟨4465475391734386352815577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11907934377958363607508205 4465475391734386352815577)
            ·
              refine ⟨3349106543800789764611683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465475391734386352815577 3349106543800789764611683)
              ·
                refine ⟨5023659815701184646917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349106543800789764611683 5023659815701184646917525)
                ·
                  refine ⟨235484053860993030324259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5023659815701184646917525 235484053860993030324259)
                  ·
                    rfl

theorem cell20_515929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_515929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515929 prefixEnd_515929 := by exact prefixLift 515929
  have htrace : WordTrace (prefixWord ++ tailWord_515929) baseStart_515929 baseEnd_515929 := by
    simpa [prefixWord, tailWord_515929, baseEnd_515929] using wordTrace_append hprefix tailTrace_515929
  have hstable : (prefixWord ++ tailWord_515929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515929).length < 2 ^ (prefixWord ++ tailWord_515929).sum := by decide
  have hdescent : baseEnd_515929 < baseStart_515929 := by decide
  rcases family_descends (prefixWord ++ tailWord_515929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515967 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_515967 : Nat := 118140960795 + 515967 * 2 ^ 59
def prefixEnd_515967 : Nat := 4983230072969 + 3 ^ 40 * 515967 * 2
def baseEnd_515967 : Nat := 235501398096433787057437

theorem tailTrace_515967 : CollatzResearch.WordTrace tailWord_515967 prefixEnd_515967 235501398096433787057437 := by
  unfold tailWord_515967
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818862521747153993106155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12545908347831435995404103 18818862521747153993106155)
  ·
    refine ⟨28228293782620730989659233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18818862521747153993106155 28228293782620730989659233)
    ·
      refine ⟨21171220336965548242244425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28228293782620730989659233 21171220336965548242244425)
      ·
        refine ⟨15878415252724161181683319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21171220336965548242244425 15878415252724161181683319)
        ·
          refine ⟨23817622879086241772524979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15878415252724161181683319 23817622879086241772524979)
          ·
            refine ⟨35726434318629362658787469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23817622879086241772524979 35726434318629362658787469)
            ·
              refine ⟨13397412869486010997045301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35726434318629362658787469 13397412869486010997045301)
              ·
                refine ⟨1256007456514313530972997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13397412869486010997045301 1256007456514313530972997)
                ·
                  refine ⟨235501398096433787057437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256007456514313530972997 235501398096433787057437)
                  ·
                    rfl

theorem cell20_515967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_515967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_515967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_515967 prefixEnd_515967 := by exact prefixLift 515967
  have htrace : WordTrace (prefixWord ++ tailWord_515967) baseStart_515967 baseEnd_515967 := by
    simpa [prefixWord, tailWord_515967, baseEnd_515967] using wordTrace_append hprefix tailTrace_515967
  have hstable : (prefixWord ++ tailWord_515967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515967).length < 2 ^ (prefixWord ++ tailWord_515967).sum := by decide
  have hdescent : baseEnd_515967 < baseStart_515967 := by decide
  rcases family_descends (prefixWord ++ tailWord_515967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516043 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_516043 : Nat := 118140960795 + 516043 * 2 ^ 59
def prefixEnd_516043 : Nat := 4983230072969 + 3 ^ 40 * 516043 * 2
def baseEnd_516043 : Nat := 235536086567315300523793

theorem tailTrace_516043 : CollatzResearch.WordTrace tailWord_516043 prefixEnd_516043 235536086567315300523793 := by
  unfold tailWord_516043
  simp only [CollatzResearch.WordTrace]
  refine ⟨18821634469471818972872783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12547756312981212648581855 18821634469471818972872783)
  ·
    refine ⟨28232451704207728459309175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18821634469471818972872783 28232451704207728459309175)
    ·
      refine ⟨42348677556311592688963763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28232451704207728459309175 42348677556311592688963763)
      ·
        refine ⟨63523016334467389033445645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42348677556311592688963763 63523016334467389033445645)
        ·
          refine ⟨23821131125425270887542117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63523016334467389033445645 23821131125425270887542117)
          ·
            refine ⟨4466462086017238291414147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23821131125425270887542117 4466462086017238291414147)
            ·
              refine ⟨6699693129025857437121221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466462086017238291414147 6699693129025857437121221)
              ·
                refine ⟨1256192461692348269460229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6699693129025857437121221 1256192461692348269460229)
                ·
                  refine ⟨235536086567315300523793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256192461692348269460229 235536086567315300523793)
                  ·
                    rfl

theorem cell20_516043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_516043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516043 prefixEnd_516043 := by exact prefixLift 516043
  have htrace : WordTrace (prefixWord ++ tailWord_516043) baseStart_516043 baseEnd_516043 := by
    simpa [prefixWord, tailWord_516043, baseEnd_516043] using wordTrace_append hprefix tailTrace_516043
  have hstable : (prefixWord ++ tailWord_516043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516043).length < 2 ^ (prefixWord ++ tailWord_516043).sum := by decide
  have hdescent : baseEnd_516043 < baseStart_516043 := by decide
  rcases family_descends (prefixWord ++ tailWord_516043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516067 : List Nat := [1, 1, 1, 6, 1, 4, 6]
def baseStart_516067 : Nat := 118140960795 + 516067 * 2 ^ 59
def prefixEnd_516067 : Nat := 4983230072969 + 3 ^ 40 * 516067 * 2
def baseEnd_516067 : Nat := 26171893424586431524855

theorem tailTrace_516067 : CollatzResearch.WordTrace tailWord_516067 prefixEnd_516067 26171893424586431524855 := by
  unfold tailWord_516067
  simp only [CollatzResearch.WordTrace]
  refine ⟨18822509821384871071746455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12548339880923247381164303 18822509821384871071746455)
  ·
    refine ⟨28233764732077306607619683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18822509821384871071746455 28233764732077306607619683)
    ·
      refine ⟨42350647098115959911429525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28233764732077306607619683 42350647098115959911429525)
      ·
        refine ⟨1985186582724185620848259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42350647098115959911429525 1985186582724185620848259)
        ·
          refine ⟨2977779874086278431272389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985186582724185620848259 2977779874086278431272389)
          ·
            refine ⟨558333726391177205863573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2977779874086278431272389 558333726391177205863573)
            ·
              refine ⟨26171893424586431524855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 558333726391177205863573 26171893424586431524855)
              ·
                rfl

theorem cell20_516067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_516067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516067 prefixEnd_516067 := by exact prefixLift 516067
  have htrace : WordTrace (prefixWord ++ tailWord_516067) baseStart_516067 baseEnd_516067 := by
    simpa [prefixWord, tailWord_516067, baseEnd_516067] using wordTrace_append hprefix tailTrace_516067
  have hstable : (prefixWord ++ tailWord_516067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516067).length < 2 ^ (prefixWord ++ tailWord_516067).sum := by decide
  have hdescent : baseEnd_516067 < baseStart_516067 := by decide
  rcases family_descends (prefixWord ++ tailWord_516067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516074 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_516074 : Nat := 118140960795 + 516074 * 2 ^ 59
def prefixEnd_516074 : Nat := 4983230072969 + 3 ^ 40 * 516074 * 2
def baseEnd_516074 : Nat := 235550235812016970490333

theorem tailTrace_516074 : CollatzResearch.WordTrace tailWord_516074 prefixEnd_516074 235550235812016970490333 := by
  unfold tailWord_516074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705691283089877816812819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12548510088239674178167517 4705691283089877816812819)
  ·
    refine ⟨7058536924634816725219229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4705691283089877816812819 7058536924634816725219229)
    ·
      refine ⟨2646951346738056271957211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7058536924634816725219229 2646951346738056271957211)
      ·
        refine ⟨3970427020107084407935817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646951346738056271957211 3970427020107084407935817)
        ·
          refine ⟨2977820265080313305951863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3970427020107084407935817 2977820265080313305951863)
          ·
            refine ⟨4466730397620469958927795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977820265080313305951863 4466730397620469958927795)
            ·
              refine ⟨6700095596430704938391693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466730397620469958927795 6700095596430704938391693)
              ·
                refine ⟨2512535848661514351896885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6700095596430704938391693 2512535848661514351896885)
                ·
                  refine ⟨235550235812016970490333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2512535848661514351896885 235550235812016970490333)
                  ·
                    rfl

theorem cell20_516074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_516074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516074 prefixEnd_516074 := by exact prefixLift 516074
  have htrace : WordTrace (prefixWord ++ tailWord_516074) baseStart_516074 baseEnd_516074 := by
    simpa [prefixWord, tailWord_516074, baseEnd_516074] using wordTrace_append hprefix tailTrace_516074
  have hstable : (prefixWord ++ tailWord_516074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516074).length < 2 ^ (prefixWord ++ tailWord_516074).sum := by decide
  have hdescent : baseEnd_516074 < baseStart_516074 := by decide
  rcases family_descends (prefixWord ++ tailWord_516074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516088 : List Nat := [2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_516088 : Nat := 118140960795 + 516088 * 2 ^ 59
def prefixEnd_516088 : Nat := 4983230072969 + 3 ^ 40 * 516088 * 2
def baseEnd_516088 : Nat := 78518875264498381341203

theorem tailTrace_516088 : CollatzResearch.WordTrace tailWord_516088 prefixEnd_516088 78518875264498381341203 := by
  unfold tailWord_516088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9411637877154395829130459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12548850502872527772173945 9411637877154395829130459)
  ·
    refine ⟨14117456815731593743695689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9411637877154395829130459 14117456815731593743695689)
    ·
      refine ⟨10588092611798695307771767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14117456815731593743695689 10588092611798695307771767)
      ·
        refine ⟨15882138917698042961657651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588092611798695307771767 15882138917698042961657651)
        ·
          refine ⟨23823208376547064442486477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15882138917698042961657651 23823208376547064442486477)
          ·
            refine ⟨8933703141205149165932429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23823208376547064442486477 8933703141205149165932429)
            ·
              refine ⟨3350138677951930937224661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8933703141205149165932429 3350138677951930937224661)
              ·
                refine ⟨78518875264498381341203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3350138677951930937224661 78518875264498381341203)
                ·
                  rfl

theorem cell20_516088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_516088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516088 prefixEnd_516088 := by exact prefixLift 516088
  have htrace : WordTrace (prefixWord ++ tailWord_516088) baseStart_516088 baseEnd_516088 := by
    simpa [prefixWord, tailWord_516088, baseEnd_516088] using wordTrace_append hprefix tailTrace_516088
  have hstable : (prefixWord ++ tailWord_516088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516088).length < 2 ^ (prefixWord ++ tailWord_516088).sum := by decide
  have hdescent : baseEnd_516088 < baseStart_516088 := by decide
  rcases family_descends (prefixWord ++ tailWord_516088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516091 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 3]
def baseStart_516091 : Nat := 118140960795 + 516091 * 2 ^ 59
def prefixEnd_516091 : Nat := 4983230072969 + 3 ^ 40 * 516091 * 2
def baseEnd_516091 : Nat := 235557995075240466923597

theorem tailTrace_516091 : CollatzResearch.WordTrace tailWord_516091 prefixEnd_516091 235557995075240466923597 := by
  unfold tailWord_516091
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823385173297923170620127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12548923448865282113746751 18823385173297923170620127)
  ·
    refine ⟨28235077759946884755930191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18823385173297923170620127 28235077759946884755930191)
    ·
      refine ⟨42352616639920327133895287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28235077759946884755930191 42352616639920327133895287)
      ·
        refine ⟨63528924959880490700842931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42352616639920327133895287 63528924959880490700842931)
        ·
          refine ⟨95293387439820736051264397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63528924959880490700842931 95293387439820736051264397)
          ·
            refine ⟨35735020289932776019224149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95293387439820736051264397 35735020289932776019224149)
            ·
              refine ⟨418769769022649718975283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 35735020289932776019224149 418769769022649718975283)
              ·
                refine ⟨628154653533974578462925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418769769022649718975283 628154653533974578462925)
                ·
                  refine ⟨235557995075240466923597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628154653533974578462925 235557995075240466923597)
                  ·
                    rfl

theorem cell20_516091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_516091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516091 prefixEnd_516091 := by exact prefixLift 516091
  have htrace : WordTrace (prefixWord ++ tailWord_516091) baseStart_516091 baseEnd_516091 := by
    simpa [prefixWord, tailWord_516091, baseEnd_516091] using wordTrace_append hprefix tailTrace_516091
  have hstable : (prefixWord ++ tailWord_516091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516091).length < 2 ^ (prefixWord ++ tailWord_516091).sum := by decide
  have hdescent : baseEnd_516091 < baseStart_516091 := by decide
  rcases family_descends (prefixWord ++ tailWord_516091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516132 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_516132 : Nat := 118140960795 + 516132 * 2 ^ 59
def prefixEnd_516132 : Nat := 4983230072969 + 3 ^ 40 * 516132 * 2
def baseEnd_516132 : Nat := 235576708592426546556763

theorem tailTrace_516132 : CollatzResearch.WordTrace tailWord_516132 prefixEnd_516132 235576708592426546556763 := by
  unfold tailWord_516132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412440283074693586431325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12549920377432924781908433 9412440283074693586431325)
  ·
    refine ⟨3529665106153010094911747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9412440283074693586431325 3529665106153010094911747)
    ·
      refine ⟨5294497659229515142367621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3529665106153010094911747 5294497659229515142367621)
      ·
        refine ⟨992718311105534089193929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5294497659229515142367621 992718311105534089193929)
        ·
          refine ⟨744538733329150566895447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992718311105534089193929 744538733329150566895447)
          ·
            refine ⟨1116808099993725850343171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744538733329150566895447 1116808099993725850343171)
            ·
              refine ⟨1675212149990588775514757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116808099993725850343171 1675212149990588775514757)
              ·
                refine ⟨314102278123235395409017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1675212149990588775514757 314102278123235395409017)
                ·
                  refine ⟨235576708592426546556763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314102278123235395409017 235576708592426546556763)
                  ·
                    rfl

theorem cell20_516132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_516132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516132 prefixEnd_516132 := by exact prefixLift 516132
  have htrace : WordTrace (prefixWord ++ tailWord_516132) baseStart_516132 baseEnd_516132 := by
    simpa [prefixWord, tailWord_516132, baseEnd_516132] using wordTrace_append hprefix tailTrace_516132
  have hstable : (prefixWord ++ tailWord_516132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516132).length < 2 ^ (prefixWord ++ tailWord_516132).sum := by decide
  have hdescent : baseEnd_516132 < baseStart_516132 := by decide
  rcases family_descends (prefixWord ++ tailWord_516132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516171 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_516171 : Nat := 118140960795 + 516171 * 2 ^ 59
def prefixEnd_516171 : Nat := 4983230072969 + 3 ^ 40 * 516171 * 2
def baseEnd_516171 : Nat := 235594509255115744256603

theorem tailTrace_516171 : CollatzResearch.WordTrace tailWord_516171 prefixEnd_516171 235594509255115744256603 := by
  unfold tailWord_516171
  simp only [CollatzResearch.WordTrace]
  refine ⟨18826303013008096833532367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12550868675338731222354911 18826303013008096833532367)
  ·
    refine ⟨28239454519512145250298551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18826303013008096833532367 28239454519512145250298551)
    ·
      refine ⟨42359181779268217875447827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28239454519512145250298551 42359181779268217875447827)
      ·
        refine ⟨63538772668902326813171741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42359181779268217875447827 63538772668902326813171741)
        ·
          refine ⟨23827039750838372554939403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63538772668902326813171741 23827039750838372554939403)
          ·
            refine ⟨35740559626257558832409105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23827039750838372554939403 35740559626257558832409105)
            ·
              refine ⟨26805419719693169124306829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35740559626257558832409105 26805419719693169124306829)
              ·
                refine ⟨10052032394884938421615061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26805419719693169124306829 10052032394884938421615061)
                ·
                  refine ⟨235594509255115744256603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10052032394884938421615061 235594509255115744256603)
                  ·
                    rfl

theorem cell20_516171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_516171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516171 prefixEnd_516171 := by exact prefixLift 516171
  have htrace : WordTrace (prefixWord ++ tailWord_516171) baseStart_516171 baseEnd_516171 := by
    simpa [prefixWord, tailWord_516171, baseEnd_516171] using wordTrace_append hprefix tailTrace_516171
  have hstable : (prefixWord ++ tailWord_516171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516171).length < 2 ^ (prefixWord ++ tailWord_516171).sum := by decide
  have hdescent : baseEnd_516171 < baseStart_516171 := by decide
  rcases family_descends (prefixWord ++ tailWord_516171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516195 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_516195 : Nat := 118140960795 + 516195 * 2 ^ 59
def prefixEnd_516195 : Nat := 4983230072969 + 3 ^ 40 * 516195 * 2
def baseEnd_516195 : Nat := 235605463509078327456505

theorem tailTrace_516195 : CollatzResearch.WordTrace tailWord_516195 prefixEnd_516195 235605463509078327456505 := by
  unfold tailWord_516195
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827178364921148932406039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12551452243280765954937359 18827178364921148932406039)
  ·
    refine ⟨28240767547381723398609059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18827178364921148932406039 28240767547381723398609059)
    ·
      refine ⟨42361151321072585097913589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28240767547381723398609059 42361151321072585097913589)
      ·
        refine ⟨3971357936350554852929399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42361151321072585097913589 3971357936350554852929399)
        ·
          refine ⟨5957036904525832279394099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971357936350554852929399 5957036904525832279394099)
          ·
            refine ⟨8935555356788748419091149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957036904525832279394099 8935555356788748419091149)
            ·
              refine ⟨3350833258795780657159181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8935555356788748419091149 3350833258795780657159181)
              ·
                refine ⟨1256562472048417746434693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350833258795780657159181 1256562472048417746434693)
                ·
                  refine ⟨235605463509078327456505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256562472048417746434693 235605463509078327456505)
                  ·
                    rfl

theorem cell20_516195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_516195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516195 prefixEnd_516195 := by exact prefixLift 516195
  have htrace : WordTrace (prefixWord ++ tailWord_516195) baseStart_516195 baseEnd_516195 := by
    simpa [prefixWord, tailWord_516195, baseEnd_516195] using wordTrace_append hprefix tailTrace_516195
  have hstable : (prefixWord ++ tailWord_516195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516195).length < 2 ^ (prefixWord ++ tailWord_516195).sum := by decide
  have hdescent : baseEnd_516195 < baseStart_516195 := by decide
  rcases family_descends (prefixWord ++ tailWord_516195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516225 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 2]
def baseStart_516225 : Nat := 118140960795 + 516225 * 2 ^ 59
def prefixEnd_516225 : Nat := 4983230072969 + 3 ^ 40 * 516225 * 2
def baseEnd_516225 : Nat := 235619156326531556456383

theorem tailTrace_516225 : CollatzResearch.WordTrace tailWord_516225 prefixEnd_516225 235619156326531556456383 := by
  unfold tailWord_516225
  simp only [CollatzResearch.WordTrace]
  refine ⟨18828272554812464055998129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12552181703208309370665419 18828272554812464055998129)
  ·
    refine ⟨14121204416109348041998597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18828272554812464055998129 14121204416109348041998597)
    ·
      refine ⟨2647725828020502757874737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14121204416109348041998597 2647725828020502757874737)
      ·
        refine ⟨1985794371015377068406053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647725828020502757874737 1985794371015377068406053)
        ·
          refine ⟨372336444565383200326135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1985794371015377068406053 372336444565383200326135)
          ·
            refine ⟨558504666848074800489203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372336444565383200326135 558504666848074800489203)
            ·
              refine ⟨837757000272112200733805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558504666848074800489203 837757000272112200733805)
              ·
                refine ⟨314158875102042075275177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837757000272112200733805 314158875102042075275177)
                ·
                  refine ⟨235619156326531556456383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314158875102042075275177 235619156326531556456383)
                  ·
                    rfl

theorem cell20_516225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_516225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516225 prefixEnd_516225 := by exact prefixLift 516225
  have htrace : WordTrace (prefixWord ++ tailWord_516225) baseStart_516225 baseEnd_516225 := by
    simpa [prefixWord, tailWord_516225, baseEnd_516225] using wordTrace_append hprefix tailTrace_516225
  have hstable : (prefixWord ++ tailWord_516225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516225).length < 2 ^ (prefixWord ++ tailWord_516225).sum := by decide
  have hdescent : baseEnd_516225 < baseStart_516225 := by decide
  rcases family_descends (prefixWord ++ tailWord_516225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516229 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 2]
def baseStart_516229 : Nat := 118140960795 + 516229 * 2 ^ 59
def prefixEnd_516229 : Nat := 4983230072969 + 3 ^ 40 * 516229 * 2
def baseEnd_516229 : Nat := 235620982035525320323033

theorem tailTrace_516229 : CollatzResearch.WordTrace tailWord_516229 prefixEnd_516229 235620982035525320323033 := by
  unfold tailWord_516229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18828418446797972739143741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12552278964531981826095827 18828418446797972739143741)
  ·
    refine ⟨7060656917549239777178903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18828418446797972739143741 7060656917549239777178903)
    ·
      refine ⟨10590985376323859665768355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060656917549239777178903 10590985376323859665768355)
      ·
        refine ⟨15886478064485789498652533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590985376323859665768355 15886478064485789498652533)
        ·
          refine ⟨1489357318545542765498675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15886478064485789498652533 1489357318545542765498675)
          ·
            refine ⟨2234035977818314148248013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489357318545542765498675 2234035977818314148248013)
            ·
              refine ⟨837763491681867805593005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234035977818314148248013 837763491681867805593005)
              ·
                refine ⟨314161309380700427097377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837763491681867805593005 314161309380700427097377)
                ·
                  refine ⟨235620982035525320323033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314161309380700427097377 235620982035525320323033)
                  ·
                    rfl

theorem cell20_516229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_516229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516229 prefixEnd_516229 := by exact prefixLift 516229
  have htrace : WordTrace (prefixWord ++ tailWord_516229) baseStart_516229 baseEnd_516229 := by
    simpa [prefixWord, tailWord_516229, baseEnd_516229] using wordTrace_append hprefix tailTrace_516229
  have hstable : (prefixWord ++ tailWord_516229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516229).length < 2 ^ (prefixWord ++ tailWord_516229).sum := by decide
  have hdescent : baseEnd_516229 < baseStart_516229 := by decide
  rcases family_descends (prefixWord ++ tailWord_516229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516257 : List Nat := [1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_516257 : Nat := 118140960795 + 516257 * 2 ^ 59
def prefixEnd_516257 : Nat := 4983230072969 + 3 ^ 40 * 516257 * 2
def baseEnd_516257 : Nat := 78544587332827222463195

theorem tailTrace_516257 : CollatzResearch.WordTrace tailWord_516257 prefixEnd_516257 78544587332827222463195 := by
  unfold tailWord_516257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18829439690696533521163025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12552959793797689014108683 18829439690696533521163025)
  ·
    refine ⟨14122079768022400140872269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18829439690696533521163025 14122079768022400140872269)
    ·
      refine ⟨5295779913008400052827101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14122079768022400140872269 5295779913008400052827101)
      ·
        refine ⟨1985917467378150019810163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5295779913008400052827101 1985917467378150019810163)
        ·
          refine ⟨2978876201067225029715245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985917467378150019810163 2978876201067225029715245)
          ·
            refine ⟨1117078575400209386143217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2978876201067225029715245 1117078575400209386143217)
            ·
              refine ⟨837808931550157039607413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117078575400209386143217 837808931550157039607413)
              ·
                refine ⟨78544587332827222463195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 837808931550157039607413 78544587332827222463195)
                ·
                  rfl

theorem cell20_516257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_516257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516257 prefixEnd_516257 := by exact prefixLift 516257
  have htrace : WordTrace (prefixWord ++ tailWord_516257) baseStart_516257 baseEnd_516257 := by
    simpa [prefixWord, tailWord_516257, baseEnd_516257] using wordTrace_append hprefix tailTrace_516257
  have hstable : (prefixWord ++ tailWord_516257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516257).length < 2 ^ (prefixWord ++ tailWord_516257).sum := by decide
  have hdescent : baseEnd_516257 < baseStart_516257 := by decide
  rcases family_descends (prefixWord ++ tailWord_516257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516305 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 2]
def baseStart_516305 : Nat := 118140960795 + 516305 * 2 ^ 59
def prefixEnd_516305 : Nat := 4983230072969 + 3 ^ 40 * 516305 * 2
def baseEnd_516305 : Nat := 235655670506406833789389

theorem tailTrace_516305 : CollatzResearch.WordTrace tailWord_516305 prefixEnd_516305 235655670506406833789389 := by
  unfold tailWord_516305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831190394522637718910369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12554126929681758479273579 18831190394522637718910369)
  ·
    refine ⟨14123392795891978289182777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18831190394522637718910369 14123392795891978289182777)
    ·
      refine ⟨10592544596918983716887083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14123392795891978289182777 10592544596918983716887083)
      ·
        refine ⟨15888816895378475575330625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592544596918983716887083 15888816895378475575330625)
        ·
          refine ⟨11916612671533856681497969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15888816895378475575330625 11916612671533856681497969)
          ·
            refine ⟨8937459503650392511123477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916612671533856681497969 8937459503650392511123477)
            ·
              refine ⟨418943414233612148958913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8937459503650392511123477 418943414233612148958913)
              ·
                refine ⟨314207560675209111719185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418943414233612148958913 314207560675209111719185)
                ·
                  refine ⟨235655670506406833789389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314207560675209111719185 235655670506406833789389)
                  ·
                    rfl

theorem cell20_516305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_516305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516305 prefixEnd_516305 := by exact prefixLift 516305
  have htrace : WordTrace (prefixWord ++ tailWord_516305) baseStart_516305 baseEnd_516305 := by
    simpa [prefixWord, tailWord_516305, baseEnd_516305] using wordTrace_append hprefix tailTrace_516305
  have hstable : (prefixWord ++ tailWord_516305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516305).length < 2 ^ (prefixWord ++ tailWord_516305).sum := by decide
  have hdescent : baseEnd_516305 < baseStart_516305 := by decide
  rcases family_descends (prefixWord ++ tailWord_516305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516364 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_516364 : Nat := 118140960795 + 516364 * 2 ^ 59
def prefixEnd_516364 : Nat := 4983230072969 + 3 ^ 40 * 516364 * 2
def baseEnd_516364 : Nat := 235682599714064850822481

theorem tailTrace_516364 : CollatzResearch.WordTrace tailWord_516364 prefixEnd_516364 235682599714064850822481 := by
  unfold tailWord_516364
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416671150654445397654073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12555561534205927196872097 9416671150654445397654073)
  ·
    refine ⟨7062503362990834048240555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9416671150654445397654073 7062503362990834048240555)
    ·
      refine ⟨10593755044486251072360833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7062503362990834048240555 10593755044486251072360833)
      ·
        refine ⟨7945316283364688304270625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10593755044486251072360833 7945316283364688304270625)
        ·
          refine ⟨5958987212523516228202969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7945316283364688304270625 5958987212523516228202969)
          ·
            refine ⟨4469240409392637171152227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5958987212523516228202969 4469240409392637171152227)
            ·
              refine ⟨6703860614088955756728341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469240409392637171152227 6703860614088955756728341)
              ·
                refine ⟨314243466285419801096641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6703860614088955756728341 314243466285419801096641)
                ·
                  refine ⟨235682599714064850822481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314243466285419801096641 235682599714064850822481)
                  ·
                    rfl

theorem cell20_516364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_516364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516364 prefixEnd_516364 := by exact prefixLift 516364
  have htrace : WordTrace (prefixWord ++ tailWord_516364) baseStart_516364 baseEnd_516364 := by
    simpa [prefixWord, tailWord_516364, baseEnd_516364] using wordTrace_append hprefix tailTrace_516364
  have hstable : (prefixWord ++ tailWord_516364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516364).length < 2 ^ (prefixWord ++ tailWord_516364).sum := by decide
  have hdescent : baseEnd_516364 < baseStart_516364 := by decide
  rcases family_descends (prefixWord ++ tailWord_516364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516385 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_516385 : Nat := 118140960795 + 516385 * 2 ^ 59
def prefixEnd_516385 : Nat := 4983230072969 + 3 ^ 40 * 516385 * 2
def baseEnd_516385 : Nat := 235692184686282111122395

theorem tailTrace_516385 : CollatzResearch.WordTrace tailWord_516385 prefixEnd_516385 235692184686282111122395 := by
  unfold tailWord_516385
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834108234232811381822609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12556072156155207587881739 18834108234232811381822609)
  ·
    refine ⟨14125581175674608536366957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18834108234232811381822609 14125581175674608536366957)
    ·
      refine ⟨5297092940877978201137609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14125581175674608536366957 5297092940877978201137609)
      ·
        refine ⟨3972819705658483650853207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5297092940877978201137609 3972819705658483650853207)
        ·
          refine ⟨5959229558487725476279811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972819705658483650853207 5959229558487725476279811)
          ·
            refine ⟨8938844337731588214419717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959229558487725476279811 8938844337731588214419717)
            ·
              refine ⟨1676033313324672790203697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8938844337731588214419717 1676033313324672790203697)
              ·
                refine ⟨1257024984993504592652773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676033313324672790203697 1257024984993504592652773)
                ·
                  refine ⟨235692184686282111122395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257024984993504592652773 235692184686282111122395)
                  ·
                    rfl

theorem cell20_516385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_516385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516385 prefixEnd_516385 := by exact prefixLift 516385
  have htrace : WordTrace (prefixWord ++ tailWord_516385) baseStart_516385 baseEnd_516385 := by
    simpa [prefixWord, tailWord_516385, baseEnd_516385] using wordTrace_append hprefix tailTrace_516385
  have hstable : (prefixWord ++ tailWord_516385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516385).length < 2 ^ (prefixWord ++ tailWord_516385).sum := by decide
  have hdescent : baseEnd_516385 < baseStart_516385 := by decide
  rcases family_descends (prefixWord ++ tailWord_516385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516388 : List Nat := [2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_516388 : Nat := 118140960795 + 516388 * 2 ^ 59
def prefixEnd_516388 : Nat := 4983230072969 + 3 ^ 40 * 516388 * 2
def baseEnd_516388 : Nat := 78564517989342478007461

theorem tailTrace_516388 : CollatzResearch.WordTrace tailWord_516388 prefixEnd_516388 78564517989342478007461 := by
  unfold tailWord_516388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417108826610971447090909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12556145102147961929454545 9417108826610971447090909)
  ·
    refine ⟨3531415809979114292659091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9417108826610971447090909 3531415809979114292659091)
    ·
      refine ⟨5297123714968671438988637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531415809979114292659091 5297123714968671438988637)
      ·
        refine ⟨1986421393113251789620739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5297123714968671438988637 1986421393113251789620739)
        ·
          refine ⟨2979632089669877684431109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986421393113251789620739 2979632089669877684431109)
          ·
            refine ⟨558681016813102065830833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2979632089669877684431109 558681016813102065830833)
            ·
              refine ⟨419010762609826549373125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558681016813102065830833 419010762609826549373125)
              ·
                refine ⟨78564517989342478007461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419010762609826549373125 78564517989342478007461)
                ·
                  rfl

theorem cell20_516388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_516388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516388 prefixEnd_516388 := by exact prefixLift 516388
  have htrace : WordTrace (prefixWord ++ tailWord_516388) baseStart_516388 baseEnd_516388 := by
    simpa [prefixWord, tailWord_516388, baseEnd_516388] using wordTrace_append hprefix tailTrace_516388
  have hstable : (prefixWord ++ tailWord_516388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516388).length < 2 ^ (prefixWord ++ tailWord_516388).sum := by decide
  have hdescent : baseEnd_516388 < baseStart_516388 := by decide
  rcases family_descends (prefixWord ++ tailWord_516388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516399 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_516399 : Nat := 118140960795 + 516399 * 2 ^ 59
def prefixEnd_516399 : Nat := 4983230072969 + 3 ^ 40 * 516399 * 2
def baseEnd_516399 : Nat := 235698574667760284655671

theorem tailTrace_516399 : CollatzResearch.WordTrace tailWord_516399 prefixEnd_516399 235698574667760284655671 := by
  unfold tailWord_516399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834618856182091772832251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12556412570788061181888167 18834618856182091772832251)
  ·
    refine ⟨28251928284273137659248377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18834618856182091772832251 28251928284273137659248377)
    ·
      refine ⟨21188946213204853244436283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28251928284273137659248377 21188946213204853244436283)
      ·
        refine ⟨31783419319807279866654425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21188946213204853244436283 31783419319807279866654425)
        ·
          refine ⟨23837564489855459899990819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31783419319807279866654425 23837564489855459899990819)
          ·
            refine ⟨35756346734783189849986229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23837564489855459899990819 35756346734783189849986229)
            ·
              refine ⟨3352157506385924048436209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35756346734783189849986229 3352157506385924048436209)
              ·
                refine ⟨2514118129789443036327157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352157506385924048436209 2514118129789443036327157)
                ·
                  refine ⟨235698574667760284655671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514118129789443036327157 235698574667760284655671)
                  ·
                    rfl

theorem cell20_516399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_516399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516399 prefixEnd_516399 := by exact prefixLift 516399
  have htrace : WordTrace (prefixWord ++ tailWord_516399) baseStart_516399 baseEnd_516399 := by
    simpa [prefixWord, tailWord_516399, baseEnd_516399] using wordTrace_append hprefix tailTrace_516399
  have hstable : (prefixWord ++ tailWord_516399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516399).length < 2 ^ (prefixWord ++ tailWord_516399).sum := by decide
  have hdescent : baseEnd_516399 < baseStart_516399 := by decide
  rcases family_descends (prefixWord ++ tailWord_516399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516409 : List Nat := [1, 2, 1, 6, 1, 3, 6]
def baseStart_516409 : Nat := 118140960795 + 516409 * 2 ^ 59
def prefixEnd_516409 : Nat := 4983230072969 + 3 ^ 40 * 516409 * 2
def baseEnd_516409 : Nat := 26189237660027188258033

theorem tailTrace_516409 : CollatzResearch.WordTrace tailWord_516409 prefixEnd_516409 26189237660027188258033 := by
  unfold tailWord_516409
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834983586145863480696281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12556655724097242320464187 18834983586145863480696281)
  ·
    refine ⟨14126237689609397610522211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18834983586145863480696281 14126237689609397610522211)
    ·
      refine ⟨21189356534414096415783317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14126237689609397610522211 21189356534414096415783317)
      ·
        refine ⟨993251087550660769489843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21189356534414096415783317 993251087550660769489843)
        ·
          refine ⟨1489876631325991154234765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993251087550660769489843 1489876631325991154234765)
          ·
            refine ⟨558703736747246682838037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1489876631325991154234765 558703736747246682838037)
            ·
              refine ⟨26189237660027188258033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 558703736747246682838037 26189237660027188258033)
              ·
                rfl

theorem cell20_516409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_516409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516409 prefixEnd_516409 := by exact prefixLift 516409
  have htrace : WordTrace (prefixWord ++ tailWord_516409) baseStart_516409 baseEnd_516409 := by
    simpa [prefixWord, tailWord_516409, baseEnd_516409] using wordTrace_append hprefix tailTrace_516409
  have hstable : (prefixWord ++ tailWord_516409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516409).length < 2 ^ (prefixWord ++ tailWord_516409).sum := by decide
  have hdescent : baseEnd_516409 < baseStart_516409 := by decide
  rcases family_descends (prefixWord ++ tailWord_516409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516433 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 3]
def baseStart_516433 : Nat := 118140960795 + 516433 * 2 ^ 59
def prefixEnd_516433 : Nat := 4983230072969 + 3 ^ 40 * 516433 * 2
def baseEnd_516433 : Nat := 235714093194207277522199

theorem tailTrace_516433 : CollatzResearch.WordTrace tailWord_516433 prefixEnd_516433 235714093194207277522199 := by
  unfold tailWord_516433
  simp only [CollatzResearch.WordTrace]
  refine ⟨18835858938058915579569953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12557239292039277053046635 18835858938058915579569953)
  ·
    refine ⟨14126894203544186684677465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18835858938058915579569953 14126894203544186684677465)
    ·
      refine ⟨10595170652658140013508099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14126894203544186684677465 10595170652658140013508099)
      ·
        refine ⟨15892755978987210020262149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10595170652658140013508099 15892755978987210020262149)
        ·
          refine ⟨2979891746060101878799153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15892755978987210020262149 2979891746060101878799153)
          ·
            refine ⟨2234918809545076409099365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979891746060101878799153 2234918809545076409099365)
            ·
              refine ⟨419047276789701826706131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2234918809545076409099365 419047276789701826706131)
              ·
                refine ⟨628570915184552740059197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419047276789701826706131 628570915184552740059197)
                ·
                  refine ⟨235714093194207277522199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628570915184552740059197 235714093194207277522199)
                  ·
                    rfl

theorem cell20_516433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_516433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516433 prefixEnd_516433 := by exact prefixLift 516433
  have htrace : WordTrace (prefixWord ++ tailWord_516433) baseStart_516433 baseEnd_516433 := by
    simpa [prefixWord, tailWord_516433, baseEnd_516433] using wordTrace_append hprefix tailTrace_516433
  have hstable : (prefixWord ++ tailWord_516433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516433).length < 2 ^ (prefixWord ++ tailWord_516433).sum := by decide
  have hdescent : baseEnd_516433 < baseStart_516433 := by decide
  rcases family_descends (prefixWord ++ tailWord_516433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516470 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_516470 : Nat := 118140960795 + 516470 * 2 ^ 59
def prefixEnd_516470 : Nat := 4983230072969 + 3 ^ 40 * 516470 * 2
def baseEnd_516470 : Nat := 235730981002399593288715

theorem tailTrace_516470 : CollatzResearch.WordTrace tailWord_516470 prefixEnd_516470 235730981002399593288715 := by
  unfold tailWord_516470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177325527432804431166679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12558138959283247265777909 1177325527432804431166679)
  ·
    refine ⟨1765988291149206646750019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177325527432804431166679 1765988291149206646750019)
    ·
      refine ⟨2648982436723809970125029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765988291149206646750019 2648982436723809970125029)
      ·
        refine ⟨496684206885714369398443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2648982436723809970125029 496684206885714369398443)
        ·
          refine ⟨745026310328571554097665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496684206885714369398443 745026310328571554097665)
          ·
            refine ⟨558769732746428665573249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745026310328571554097665 558769732746428665573249)
            ·
              refine ⟨419077299559821499179937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558769732746428665573249 419077299559821499179937)
              ·
                refine ⟨314307974669866124384953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419077299559821499179937 314307974669866124384953)
                ·
                  refine ⟨235730981002399593288715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314307974669866124384953 235730981002399593288715)
                  ·
                    rfl

theorem cell20_516470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_516470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516470 prefixEnd_516470 := by exact prefixLift 516470
  have htrace : WordTrace (prefixWord ++ tailWord_516470) baseStart_516470 baseEnd_516470 := by
    simpa [prefixWord, tailWord_516470, baseEnd_516470] using wordTrace_append hprefix tailTrace_516470
  have hstable : (prefixWord ++ tailWord_516470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516470).length < 2 ^ (prefixWord ++ tailWord_516470).sum := by decide
  have hdescent : baseEnd_516470 < baseStart_516470 := by decide
  rcases family_descends (prefixWord ++ tailWord_516470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516492 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_516492 : Nat := 118140960795 + 516492 * 2 ^ 59
def prefixEnd_516492 : Nat := 4983230072969 + 3 ^ 40 * 516492 * 2
def baseEnd_516492 : Nat := 235741022401865294555291

theorem tailTrace_516492 : CollatzResearch.WordTrace tailWord_516492 prefixEnd_516492 235741022401865294555291 := by
  unfold tailWord_516492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9419005422422584327983865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12558673896563445770645153 9419005422422584327983865)
  ·
    refine ⟨7064254066816938245987899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9419005422422584327983865 7064254066816938245987899)
    ·
      refine ⟨10596381100225407368981849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064254066816938245987899 10596381100225407368981849)
      ·
        refine ⟨7947285825169055526736387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10596381100225407368981849 7947285825169055526736387)
        ·
          refine ⟨11920928737753583290104581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947285825169055526736387 11920928737753583290104581)
          ·
            refine ⟨2235174138328796866894609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11920928737753583290104581 2235174138328796866894609)
            ·
              refine ⟨1676380603746597650170957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235174138328796866894609 1676380603746597650170957)
              ·
                refine ⟨628642726404974118814109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676380603746597650170957 628642726404974118814109)
                ·
                  refine ⟨235741022401865294555291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628642726404974118814109 235741022401865294555291)
                  ·
                    rfl

theorem cell20_516492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_516492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516492 prefixEnd_516492 := by exact prefixLift 516492
  have htrace : WordTrace (prefixWord ++ tailWord_516492) baseStart_516492 baseEnd_516492 := by
    simpa [prefixWord, tailWord_516492, baseEnd_516492] using wordTrace_append hprefix tailTrace_516492
  have hstable : (prefixWord ++ tailWord_516492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516492).length < 2 ^ (prefixWord ++ tailWord_516492).sum := by decide
  have hdescent : baseEnd_516492 < baseStart_516492 := by decide
  rcases family_descends (prefixWord ++ tailWord_516492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516516 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_516516 : Nat := 118140960795 + 516516 * 2 ^ 59
def prefixEnd_516516 : Nat := 4983230072969 + 3 ^ 40 * 516516 * 2
def baseEnd_516516 : Nat := 235751976655827877755193

theorem tailTrace_516516 : CollatzResearch.WordTrace tailWord_516516 prefixEnd_516516 235751976655827877755193 := by
  unfold tailWord_516516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9419443098379110377420701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12559257464505480503227601 9419443098379110377420701)
  ·
    refine ⟨3532291161892166391532763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9419443098379110377420701 3532291161892166391532763)
    ·
      refine ⟨5298436742838249587299145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532291161892166391532763 5298436742838249587299145)
      ·
        refine ⟨3973827557128687190474359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5298436742838249587299145 3973827557128687190474359)
        ·
          refine ⟨5960741335693030785711539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973827557128687190474359 5960741335693030785711539)
          ·
            refine ⟨8941112003539546178567309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960741335693030785711539 8941112003539546178567309)
            ·
              refine ⟨3352917001327329816962741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8941112003539546178567309 3352917001327329816962741)
              ·
                refine ⟨314335968874437170340257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3352917001327329816962741 314335968874437170340257)
                ·
                  refine ⟨235751976655827877755193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314335968874437170340257 235751976655827877755193)
                  ·
                    rfl

theorem cell20_516516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_516516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516516 prefixEnd_516516 := by exact prefixLift 516516
  have htrace : WordTrace (prefixWord ++ tailWord_516516) baseStart_516516 baseEnd_516516 := by
    simpa [prefixWord, tailWord_516516, baseEnd_516516] using wordTrace_append hprefix tailTrace_516516
  have hstable : (prefixWord ++ tailWord_516516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516516).length < 2 ^ (prefixWord ++ tailWord_516516).sum := by decide
  have hdescent : baseEnd_516516 < baseStart_516516 := by decide
  rcases family_descends (prefixWord ++ tailWord_516516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516522 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_516522 : Nat := 118140960795 + 516522 * 2 ^ 59
def prefixEnd_516522 : Nat := 4983230072969 + 3 ^ 40 * 516522 * 2
def baseEnd_516522 : Nat := 235754715219318523555169

theorem tailTrace_516522 : CollatzResearch.WordTrace tailWord_516522 prefixEnd_516522 235754715219318523555169 := by
  unfold tailWord_516522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709776258684120944889955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12559403356490989186373213 4709776258684120944889955)
  ·
    refine ⟨7064664388026181417334933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4709776258684120944889955 7064664388026181417334933)
    ·
      refine ⟨331156143188727253937575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7064664388026181417334933 331156143188727253937575)
      ·
        refine ⟨496734214783090880906363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331156143188727253937575 496734214783090880906363)
        ·
          refine ⟨745101322174636321359545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496734214783090880906363 745101322174636321359545)
          ·
            refine ⟨558825991630977241019659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745101322174636321359545 558825991630977241019659)
            ·
              refine ⟨838238987446465861529489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558825991630977241019659 838238987446465861529489)
              ·
                refine ⟨628679240584849396147117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838238987446465861529489 628679240584849396147117)
                ·
                  refine ⟨235754715219318523555169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628679240584849396147117 235754715219318523555169)
                  ·
                    rfl

theorem cell20_516522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_516522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516522 prefixEnd_516522 := by exact prefixLift 516522
  have htrace : WordTrace (prefixWord ++ tailWord_516522) baseStart_516522 baseEnd_516522 := by
    simpa [prefixWord, tailWord_516522, baseEnd_516522] using wordTrace_append hprefix tailTrace_516522
  have hstable : (prefixWord ++ tailWord_516522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516522).length < 2 ^ (prefixWord ++ tailWord_516522).sum := by decide
  have hdescent : baseEnd_516522 < baseStart_516522 := by decide
  rcases family_descends (prefixWord ++ tailWord_516522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516537 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_516537 : Nat := 118140960795 + 516537 * 2 ^ 59
def prefixEnd_516537 : Nat := 4983230072969 + 3 ^ 40 * 516537 * 2
def baseEnd_516537 : Nat := 235761561628045138055107

theorem tailTrace_516537 : CollatzResearch.WordTrace tailWord_516537 prefixEnd_516537 235761561628045138055107 := by
  unfold tailWord_516537
  simp only [CollatzResearch.WordTrace]
  refine ⟨18839652129682141341355865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12559768086454760894237243 18839652129682141341355865)
  ·
    refine ⟨14129739097261606006016899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18839652129682141341355865 14129739097261606006016899)
    ·
      refine ⟨21194608645892409009025349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14129739097261606006016899 21194608645892409009025349)
      ·
        refine ⟨3973989121104826689192253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21194608645892409009025349 3973989121104826689192253)
        ·
          refine ⟨1490245920414310008447095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3973989121104826689192253 1490245920414310008447095)
          ·
            refine ⟨2235368880621465012670643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490245920414310008447095 2235368880621465012670643)
            ·
              refine ⟨3353053320932197519005965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235368880621465012670643 3353053320932197519005965)
              ·
                refine ⟨1257394995349574069627237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3353053320932197519005965 1257394995349574069627237)
                ·
                  refine ⟨235761561628045138055107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257394995349574069627237 235761561628045138055107)
                  ·
                    rfl

theorem cell20_516537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_516537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516537 prefixEnd_516537 := by exact prefixLift 516537
  have htrace : WordTrace (prefixWord ++ tailWord_516537) baseStart_516537 baseEnd_516537 := by
    simpa [prefixWord, tailWord_516537, baseEnd_516537] using wordTrace_append hprefix tailTrace_516537
  have hstable : (prefixWord ++ tailWord_516537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516537).length < 2 ^ (prefixWord ++ tailWord_516537).sum := by decide
  have hdescent : baseEnd_516537 < baseStart_516537 := by decide
  rcases family_descends (prefixWord ++ tailWord_516537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516620 : List Nat := [2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_516620 : Nat := 118140960795 + 516620 * 2 ^ 59
def prefixEnd_516620 : Nat := 4983230072969 + 3 ^ 40 * 516620 * 2
def baseEnd_516620 : Nat := 78599815029888579429367

theorem tailTrace_516620 : CollatzResearch.WordTrace tailWord_516620 prefixEnd_516620 78599815029888579429367 := by
  unfold tailWord_516620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421339694190723258313657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12561786258920964344418209 9421339694190723258313657)
  ·
    refine ⟨7066004770643042443735243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9421339694190723258313657 7066004770643042443735243)
    ·
      refine ⟨10599007155964563665602865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066004770643042443735243 10599007155964563665602865)
      ·
        refine ⟨7949255366973422749202149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10599007155964563665602865 7949255366973422749202149)
        ·
          refine ⟨1490485381307516765475403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7949255366973422749202149 1490485381307516765475403)
          ·
            refine ⟨2235728071961275148213105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490485381307516765475403 2235728071961275148213105)
            ·
              refine ⟨1676796053970956361159829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235728071961275148213105 1676796053970956361159829)
              ·
                refine ⟨78599815029888579429367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1676796053970956361159829 78599815029888579429367)
                ·
                  rfl

theorem cell20_516620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_516620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516620 prefixEnd_516620 := by exact prefixLift 516620
  have htrace : WordTrace (prefixWord ++ tailWord_516620) baseStart_516620 baseEnd_516620 := by
    simpa [prefixWord, tailWord_516620, baseEnd_516620] using wordTrace_append hprefix tailTrace_516620
  have hstable : (prefixWord ++ tailWord_516620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516620).length < 2 ^ (prefixWord ++ tailWord_516620).sum := by decide
  have hdescent : baseEnd_516620 < baseStart_516620 := by decide
  rcases family_descends (prefixWord ++ tailWord_516620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516654 : List Nat := [4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_516654 : Nat := 118140960795 + 516654 * 2 ^ 59
def prefixEnd_516654 : Nat := 4983230072969 + 3 ^ 40 * 516654 * 2
def baseEnd_516654 : Nat := 78604987872037577051543

theorem tailTrace_516654 : CollatzResearch.WordTrace tailWord_516654 prefixEnd_516654 78604987872037577051543 := by
  unfold tailWord_516654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355489933782283790420627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12562612980172180215576677 2355489933782283790420627)
  ·
    refine ⟨3533234900673425685630941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2355489933782283790420627 3533234900673425685630941)
    ·
      refine ⟨1324963087752534632111603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3533234900673425685630941 1324963087752534632111603)
      ·
        refine ⟨1987444631628801948167405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324963087752534632111603 1987444631628801948167405)
        ·
          refine ⟨745291736860800730562777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1987444631628801948167405 745291736860800730562777)
          ·
            refine ⟨558968802645600547922083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745291736860800730562777 558968802645600547922083)
            ·
              refine ⟨838453203968400821883125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558968802645600547922083 838453203968400821883125)
              ·
                refine ⟨78604987872037577051543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 838453203968400821883125 78604987872037577051543)
                ·
                  rfl

theorem cell20_516654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_516654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516654 prefixEnd_516654 := by exact prefixLift 516654
  have htrace : WordTrace (prefixWord ++ tailWord_516654) baseStart_516654 baseEnd_516654 := by
    simpa [prefixWord, tailWord_516654, baseEnd_516654] using wordTrace_append hprefix tailTrace_516654
  have hstable : (prefixWord ++ tailWord_516654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516654).length < 2 ^ (prefixWord ++ tailWord_516654).sum := by decide
  have hdescent : baseEnd_516654 < baseStart_516654 := by decide
  rcases family_descends (prefixWord ++ tailWord_516654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516658 : List Nat := [3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_516658 : Nat := 118140960795 + 516658 * 2 ^ 59
def prefixEnd_516658 : Nat := 4983230072969 + 3 ^ 40 * 516658 * 2
def baseEnd_516658 : Nat := 78605596441702165007093

theorem tailTrace_516658 : CollatzResearch.WordTrace tailWord_516658 prefixEnd_516658 78605596441702165007093 := by
  unfold tailWord_516658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711016340560944751627657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12562710241495852671007085 4711016340560944751627657)
  ·
    refine ⟨3533262255420708563720743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4711016340560944751627657 3533262255420708563720743)
    ·
      refine ⟨5299893383131062845581115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533262255420708563720743 5299893383131062845581115)
      ·
        refine ⟨7949840074696594268371673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299893383131062845581115 7949840074696594268371673)
        ·
          refine ⟨5962380056022445701278755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949840074696594268371673 5962380056022445701278755)
          ·
            refine ⟨8943570084033668551918133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962380056022445701278755 8943570084033668551918133)
            ·
              refine ⟨838459695378156426742325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8943570084033668551918133 838459695378156426742325)
              ·
                refine ⟨78605596441702165007093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 838459695378156426742325 78605596441702165007093)
                ·
                  rfl

theorem cell20_516658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_516658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516658 prefixEnd_516658 := by exact prefixLift 516658
  have htrace : WordTrace (prefixWord ++ tailWord_516658) baseStart_516658 baseEnd_516658 := by
    simpa [prefixWord, tailWord_516658, baseEnd_516658] using wordTrace_append hprefix tailTrace_516658
  have hstable : (prefixWord ++ tailWord_516658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516658).length < 2 ^ (prefixWord ++ tailWord_516658).sum := by decide
  have hdescent : baseEnd_516658 < baseStart_516658 := by decide
  rcases family_descends (prefixWord ++ tailWord_516658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516672 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_516672 : Nat := 118140960795 + 516672 * 2 ^ 59
def prefixEnd_516672 : Nat := 4983230072969 + 3 ^ 40 * 516672 * 2
def baseEnd_516672 : Nat := 235823179306584668554555

theorem tailTrace_516672 : CollatzResearch.WordTrace tailWord_516672 prefixEnd_516672 235823179306584668554555 := by
  unfold tailWord_516672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422287992096529698760135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12563050656128706265013513 9422287992096529698760135)
  ·
    refine ⟨14133431988144794548140203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422287992096529698760135 14133431988144794548140203)
    ·
      refine ⟨21200147982217191822210305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133431988144794548140203 21200147982217191822210305)
      ·
        refine ⟨15900110986662893866657729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21200147982217191822210305 15900110986662893866657729)
        ·
          refine ⟨11925083239997170399993297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15900110986662893866657729 11925083239997170399993297)
          ·
            refine ⟨8943812429997877799994973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925083239997170399993297 8943812429997877799994973)
            ·
              refine ⟨3353929661249204174998115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8943812429997877799994973 3353929661249204174998115)
              ·
                refine ⟨5030894491873806262497173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353929661249204174998115 5030894491873806262497173)
                ·
                  refine ⟨235823179306584668554555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5030894491873806262497173 235823179306584668554555)
                  ·
                    rfl

theorem cell20_516672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_516672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516672 prefixEnd_516672 := by exact prefixLift 516672
  have htrace : WordTrace (prefixWord ++ tailWord_516672) baseStart_516672 baseEnd_516672 := by
    simpa [prefixWord, tailWord_516672, baseEnd_516672] using wordTrace_append hprefix tailTrace_516672
  have hstable : (prefixWord ++ tailWord_516672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516672).length < 2 ^ (prefixWord ++ tailWord_516672).sum := by decide
  have hdescent : baseEnd_516672 < baseStart_516672 := by decide
  rcases family_descends (prefixWord ++ tailWord_516672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516685 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 2]
def baseStart_516685 : Nat := 118140960795 + 516685 * 2 ^ 59
def prefixEnd_516685 : Nat := 4983230072969 + 3 ^ 40 * 516685 * 2
def baseEnd_516685 : Nat := 235829112860814401121169

theorem tailTrace_516685 : CollatzResearch.WordTrace tailWord_516685 prefixEnd_516685 235829112860814401121169 := by
  unfold tailWord_516685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18845050133145962617743509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12563366755430641745162339 18845050133145962617743509)
  ·
    refine ⟨883361724991216997706727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18845050133145962617743509 883361724991216997706727)
    ·
      refine ⟨1325042587486825496560091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883361724991216997706727 1325042587486825496560091)
      ·
        refine ⟨1987563881230238244840137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325042587486825496560091 1987563881230238244840137)
        ·
          refine ⟨1490672910922678683630103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987563881230238244840137 1490672910922678683630103)
          ·
            refine ⟨2236009366384018025445155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490672910922678683630103 2236009366384018025445155)
            ·
              refine ⟨3354014049576027038167733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236009366384018025445155 3354014049576027038167733)
              ·
                refine ⟨314438817147752534828225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3354014049576027038167733 314438817147752534828225)
                ·
                  refine ⟨235829112860814401121169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314438817147752534828225 235829112860814401121169)
                  ·
                    rfl

theorem cell20_516685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_516685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516685 prefixEnd_516685 := by exact prefixLift 516685
  have htrace : WordTrace (prefixWord ++ tailWord_516685) baseStart_516685 baseEnd_516685 := by
    simpa [prefixWord, tailWord_516685, baseEnd_516685] using wordTrace_append hprefix tailTrace_516685
  have hstable : (prefixWord ++ tailWord_516685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516685).length < 2 ^ (prefixWord ++ tailWord_516685).sum := by decide
  have hdescent : baseEnd_516685 < baseStart_516685 := by decide
  rcases family_descends (prefixWord ++ tailWord_516685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516741 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_516741 : Nat := 118140960795 + 516741 * 2 ^ 59
def prefixEnd_516741 : Nat := 4983230072969 + 3 ^ 40 * 516741 * 2
def baseEnd_516741 : Nat := 235854672786727095254273

theorem tailTrace_516741 : CollatzResearch.WordTrace tailWord_516741 prefixEnd_516741 235854672786727095254273 := by
  unfold tailWord_516741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847092620943084181782077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12564728413962056121188051 18847092620943084181782077)
  ·
    refine ⟨7067659732853656568168279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18847092620943084181782077 7067659732853656568168279)
    ·
      refine ⟨10601489599280484852252419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067659732853656568168279 10601489599280484852252419)
      ·
        refine ⟨15902234398920727278378629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601489599280484852252419 15902234398920727278378629)
        ·
          refine ⟨2981668949797636364695993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15902234398920727278378629 2981668949797636364695993)
          ·
            refine ⟨2236251712348227273521995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981668949797636364695993 2236251712348227273521995)
            ·
              refine ⟨3354377568522340910282993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236251712348227273521995 3354377568522340910282993)
              ·
                refine ⟨2515783176391755682712245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354377568522340910282993 2515783176391755682712245)
                ·
                  refine ⟨235854672786727095254273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2515783176391755682712245 235854672786727095254273)
                  ·
                    rfl

theorem cell20_516741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_516741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516741 prefixEnd_516741 := by exact prefixLift 516741
  have htrace : WordTrace (prefixWord ++ tailWord_516741) baseStart_516741 baseEnd_516741 := by
    simpa [prefixWord, tailWord_516741, baseEnd_516741] using wordTrace_append hprefix tailTrace_516741
  have hstable : (prefixWord ++ tailWord_516741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516741).length < 2 ^ (prefixWord ++ tailWord_516741).sum := by decide
  have hdescent : baseEnd_516741 < baseStart_516741 := by decide
  rcases family_descends (prefixWord ++ tailWord_516741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516765 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_516765 : Nat := 118140960795 + 516765 * 2 ^ 59
def prefixEnd_516765 : Nat := 4983230072969 + 3 ^ 40 * 516765 * 2
def baseEnd_516765 : Nat := 235865627040689678454175

theorem tailTrace_516765 : CollatzResearch.WordTrace tailWord_516765 prefixEnd_516765 235865627040689678454175 := by
  unfold tailWord_516765
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847967972856136280655749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12565311981904090853770499 18847967972856136280655749)
  ·
    refine ⟨3533993994910525552622953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18847967972856136280655749 3533993994910525552622953)
    ·
      refine ⟨2650495496182894164467215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3533993994910525552622953 2650495496182894164467215)
      ·
        refine ⟨3975743244274341246700823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650495496182894164467215 3975743244274341246700823)
        ·
          refine ⟨5963614866411511870051235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975743244274341246700823 5963614866411511870051235)
          ·
            refine ⟨8945422299617267805076853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963614866411511870051235 8945422299617267805076853)
            ·
              refine ⟨838633340589118856725955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8945422299617267805076853 838633340589118856725955)
              ·
                refine ⟨1257950010883678285088933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838633340589118856725955 1257950010883678285088933)
                ·
                  refine ⟨235865627040689678454175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257950010883678285088933 235865627040689678454175)
                  ·
                    rfl

theorem cell20_516765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_516765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516765 prefixEnd_516765 := by exact prefixLift 516765
  have htrace : WordTrace (prefixWord ++ tailWord_516765) baseStart_516765 baseEnd_516765 := by
    simpa [prefixWord, tailWord_516765, baseEnd_516765] using wordTrace_append hprefix tailTrace_516765
  have hstable : (prefixWord ++ tailWord_516765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516765).length < 2 ^ (prefixWord ++ tailWord_516765).sum := by decide
  have hdescent : baseEnd_516765 < baseStart_516765 := by decide
  rcases family_descends (prefixWord ++ tailWord_516765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516772 : List Nat := [2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_516772 : Nat := 118140960795 + 516772 * 2 ^ 59
def prefixEnd_516772 : Nat := 4983230072969 + 3 ^ 40 * 516772 * 2
def baseEnd_516772 : Nat := 78622940677142921740271

theorem tailTrace_516772 : CollatzResearch.WordTrace tailWord_516772 prefixEnd_516772 78622940677142921740271 := by
  unfold tailWord_516772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9424111641915388238080285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12565482189220517650773713 9424111641915388238080285)
  ·
    refine ⟨3534041865718270589280107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9424111641915388238080285 3534041865718270589280107)
    ·
      refine ⟨5301062798577405883920161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534041865718270589280107 5301062798577405883920161)
      ·
        refine ⟨3975797098933054412940121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5301062798577405883920161 3975797098933054412940121)
        ·
          refine ⟨2981847824199790809705091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3975797098933054412940121 2981847824199790809705091)
          ·
            refine ⟨4472771736299686214557637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981847824199790809705091 4472771736299686214557637)
            ·
              refine ⟨838644700556191165229557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4472771736299686214557637 838644700556191165229557)
              ·
                refine ⟨78622940677142921740271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 838644700556191165229557 78622940677142921740271)
                ·
                  rfl

theorem cell20_516772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_516772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516772 prefixEnd_516772 := by exact prefixLift 516772
  have htrace : WordTrace (prefixWord ++ tailWord_516772) baseStart_516772 baseEnd_516772 := by
    simpa [prefixWord, tailWord_516772, baseEnd_516772] using wordTrace_append hprefix tailTrace_516772
  have hstable : (prefixWord ++ tailWord_516772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516772).length < 2 ^ (prefixWord ++ tailWord_516772).sum := by decide
  have hdescent : baseEnd_516772 < baseStart_516772 := by decide
  rcases family_descends (prefixWord ++ tailWord_516772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516786 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_516786 : Nat := 118140960795 + 516786 * 2 ^ 59
def prefixEnd_516786 : Nat := 4983230072969 + 3 ^ 40 * 516786 * 2
def baseEnd_516786 : Nat := 235875212012906938754089

theorem tailTrace_516786 : CollatzResearch.WordTrace tailWord_516786 prefixEnd_516786 235875212012906938754089 := by
  unfold tailWord_516786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712183476445014216792553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12565822603853371244780141 4712183476445014216792553)
  ·
    refine ⟨3534137607333760662594415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4712183476445014216792553 3534137607333760662594415)
    ·
      refine ⟨5301206411000640993891623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534137607333760662594415 5301206411000640993891623)
      ·
        refine ⟨7951809616500961490837435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5301206411000640993891623 7951809616500961490837435)
        ·
          refine ⟨11927714424751442236256153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951809616500961490837435 11927714424751442236256153)
          ·
            refine ⟨8945785818563581677192115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11927714424751442236256153 8945785818563581677192115)
            ·
              refine ⟨13418678727845372515788173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945785818563581677192115 13418678727845372515788173)
              ·
                refine ⟨5032004522942014693420565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418678727845372515788173 5032004522942014693420565)
                ·
                  refine ⟨235875212012906938754089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5032004522942014693420565 235875212012906938754089)
                  ·
                    rfl

theorem cell20_516786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_516786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516786 prefixEnd_516786 := by exact prefixLift 516786
  have htrace : WordTrace (prefixWord ++ tailWord_516786) baseStart_516786 baseEnd_516786 := by
    simpa [prefixWord, tailWord_516786, baseEnd_516786] using wordTrace_append hprefix tailTrace_516786
  have hstable : (prefixWord ++ tailWord_516786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516786).length < 2 ^ (prefixWord ++ tailWord_516786).sum := by decide
  have hdescent : baseEnd_516786 < baseStart_516786 := by decide
  rcases family_descends (prefixWord ++ tailWord_516786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516806 : List Nat := [6, 1, 2, 1, 2, 8]
def baseStart_516806 : Nat := 118140960795 + 516806 * 2 ^ 59
def prefixEnd_516806 : Nat := 4983230072969 + 3 ^ 40 * 516806 * 2
def baseEnd_516806 : Nat := 8736457057699102151383

theorem tailTrace_516806 : CollatzResearch.WordTrace tailWord_516806 prefixEnd_516806 8736457057699102151383 := by
  unfold tailWord_516806
  simp only [CollatzResearch.WordTrace]
  refine ⟨589045730178362508840571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12566308910471733521932181 589045730178362508840571)
  ·
    refine ⟨883568595267543763260857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589045730178362508840571 883568595267543763260857)
    ·
      refine ⟨662676446450657822445643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883568595267543763260857 662676446450657822445643)
      ·
        refine ⟨994014669675986733668465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662676446450657822445643 994014669675986733668465)
        ·
          refine ⟨745511002256990050251349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994014669675986733668465 745511002256990050251349)
          ·
            refine ⟨8736457057699102151383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 745511002256990050251349 8736457057699102151383)
            ·
              rfl

theorem cell20_516806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 8].length) (baseStart_516806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516806 prefixEnd_516806 := by exact prefixLift 516806
  have htrace : WordTrace (prefixWord ++ tailWord_516806) baseStart_516806 baseEnd_516806 := by
    simpa [prefixWord, tailWord_516806, baseEnd_516806] using wordTrace_append hprefix tailTrace_516806
  have hstable : (prefixWord ++ tailWord_516806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516806).length < 2 ^ (prefixWord ++ tailWord_516806).sum := by decide
  have hdescent : baseEnd_516806 < baseStart_516806 := by decide
  rcases family_descends (prefixWord ++ tailWord_516806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516848 : List Nat := [2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_516848 : Nat := 118140960795 + 516848 * 2 ^ 59
def prefixEnd_516848 : Nat := 4983230072969 + 3 ^ 40 * 516848 * 2
def baseEnd_516848 : Nat := 78634503500770092895723

theorem tailTrace_516848 : CollatzResearch.WordTrace tailWord_516848 prefixEnd_516848 78634503500770092895723 := by
  unfold tailWord_516848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425497615777720727963599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12567330154370294303951465 9425497615777720727963599)
  ·
    refine ⟨14138246423666581091945399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9425497615777720727963599 14138246423666581091945399)
    ·
      refine ⟨21207369635499871637918099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14138246423666581091945399 21207369635499871637918099)
      ·
        refine ⟨31811054453249807456877149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207369635499871637918099 31811054453249807456877149)
        ·
          refine ⟨11929145419968677796328931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31811054453249807456877149 11929145419968677796328931)
          ·
            refine ⟨17893718129953016694493397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11929145419968677796328931 17893718129953016694493397)
            ·
              refine ⟨419384018670773828777189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17893718129953016694493397 419384018670773828777189)
              ·
                refine ⟨78634503500770092895723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419384018670773828777189 78634503500770092895723)
                ·
                  rfl

theorem cell20_516848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_516848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516848 prefixEnd_516848 := by exact prefixLift 516848
  have htrace : WordTrace (prefixWord ++ tailWord_516848) baseStart_516848 baseEnd_516848 := by
    simpa [prefixWord, tailWord_516848, baseEnd_516848] using wordTrace_append hprefix tailTrace_516848
  have hstable : (prefixWord ++ tailWord_516848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516848).length < 2 ^ (prefixWord ++ tailWord_516848).sum := by decide
  have hdescent : baseEnd_516848 < baseStart_516848 := by decide
  rcases family_descends (prefixWord ++ tailWord_516848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516872 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_516872 : Nat := 118140960795 + 516872 * 2 ^ 59
def prefixEnd_516872 : Nat := 4983230072969 + 3 ^ 40 * 516872 * 2
def baseEnd_516872 : Nat := 235914464756272861887071

theorem tailTrace_516872 : CollatzResearch.WordTrace tailWord_516872 prefixEnd_516872 235914464756272861887071 := by
  unfold tailWord_516872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425935291734246777400435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12567913722312329036533913 9425935291734246777400435)
  ·
    refine ⟨14138902937601370166100653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9425935291734246777400435 14138902937601370166100653)
    ·
      refine ⟨5302088601600513812287745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14138902937601370166100653 5302088601600513812287745)
      ·
        refine ⟨3976566451200385359215809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5302088601600513812287745 3976566451200385359215809)
        ·
          refine ⟨2982424838400289019411857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976566451200385359215809 2982424838400289019411857)
          ·
            refine ⟨2236818628800216764558893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982424838400289019411857 2236818628800216764558893)
            ·
              refine ⟨838806985800081286709585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2236818628800216764558893 838806985800081286709585)
              ·
                refine ⟨629105239350060965032189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838806985800081286709585 629105239350060965032189)
                ·
                  refine ⟨235914464756272861887071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629105239350060965032189 235914464756272861887071)
                  ·
                    rfl

theorem cell20_516872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_516872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516872 prefixEnd_516872 := by exact prefixLift 516872
  have htrace : WordTrace (prefixWord ++ tailWord_516872) baseStart_516872 baseEnd_516872 := by
    simpa [prefixWord, tailWord_516872, baseEnd_516872] using wordTrace_append hprefix tailTrace_516872
  have hstable : (prefixWord ++ tailWord_516872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516872).length < 2 ^ (prefixWord ++ tailWord_516872).sum := by decide
  have hdescent : baseEnd_516872 < baseStart_516872 := by decide
  rcases family_descends (prefixWord ++ tailWord_516872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516879 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 2]
def baseStart_516879 : Nat := 118140960795 + 516879 * 2 ^ 59
def prefixEnd_516879 : Nat := 4983230072969 + 3 ^ 40 * 516879 * 2
def baseEnd_516879 : Nat := 235917659747011948653709

theorem tailTrace_516879 : CollatzResearch.WordTrace tailWord_516879 prefixEnd_516879 235917659747011948653709 := by
  unfold tailWord_516879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852125894443133750305691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12568083929628755833537127 18852125894443133750305691)
  ·
    refine ⟨28278188841664700625458537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18852125894443133750305691 28278188841664700625458537)
    ·
      refine ⟨21208641631248525469093903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28278188841664700625458537 21208641631248525469093903)
      ·
        refine ⟨31812962446872788203640855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21208641631248525469093903 31812962446872788203640855)
        ·
          refine ⟨47719443670309182305461283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31812962446872788203640855 47719443670309182305461283)
          ·
            refine ⟨71579165505463773458191925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47719443670309182305461283 71579165505463773458191925)
            ·
              refine ⟨6710546766137228761705493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71579165505463773458191925 6710546766137228761705493)
              ·
                refine ⟨314556879662682598204945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6710546766137228761705493 314556879662682598204945)
                ·
                  refine ⟨235917659747011948653709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314556879662682598204945 235917659747011948653709)
                  ·
                    rfl

theorem cell20_516879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2].length) (baseStart_516879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516879 prefixEnd_516879 := by exact prefixLift 516879
  have htrace : WordTrace (prefixWord ++ tailWord_516879) baseStart_516879 baseEnd_516879 := by
    simpa [prefixWord, tailWord_516879, baseEnd_516879] using wordTrace_append hprefix tailTrace_516879
  have hstable : (prefixWord ++ tailWord_516879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516879).length < 2 ^ (prefixWord ++ tailWord_516879).sum := by decide
  have hdescent : baseEnd_516879 < baseStart_516879 := by decide
  rcases family_descends (prefixWord ++ tailWord_516879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516909 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 2]
def baseStart_516909 : Nat := 118140960795 + 516909 * 2 ^ 59
def prefixEnd_516909 : Nat := 4983230072969 + 3 ^ 40 * 516909 * 2
def baseEnd_516909 : Nat := 235931352564465177653587

theorem tailTrace_516909 : CollatzResearch.WordTrace tailWord_516909 prefixEnd_516909 235931352564465177653587 := by
  unfold tailWord_516909
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853220084334448873897781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12568813389556299249265187 18853220084334448873897781)
  ·
    refine ⟨1767489382906354581927917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18853220084334448873897781 1767489382906354581927917)
    ·
      refine ⟨662808518589882968222969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1767489382906354581927917 662808518589882968222969)
      ·
        refine ⟨497106388942412226167227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662808518589882968222969 497106388942412226167227)
        ·
          refine ⟨745659583413618339250841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497106388942412226167227 745659583413618339250841)
          ·
            refine ⟨559244687560213754438131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745659583413618339250841 559244687560213754438131)
            ·
              refine ⟨838867031340320631657197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559244687560213754438131 838867031340320631657197)
              ·
                refine ⟨314575136752620236871449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838867031340320631657197 314575136752620236871449)
                ·
                  refine ⟨235931352564465177653587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314575136752620236871449 235931352564465177653587)
                  ·
                    rfl

theorem cell20_516909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_516909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516909 prefixEnd_516909 := by exact prefixLift 516909
  have htrace : WordTrace (prefixWord ++ tailWord_516909) baseStart_516909 baseEnd_516909 := by
    simpa [prefixWord, tailWord_516909, baseEnd_516909] using wordTrace_append hprefix tailTrace_516909
  have hstable : (prefixWord ++ tailWord_516909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516909).length < 2 ^ (prefixWord ++ tailWord_516909).sum := by decide
  have hdescent : baseEnd_516909 < baseStart_516909 := by decide
  rcases family_descends (prefixWord ++ tailWord_516909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516910 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_516910 : Nat := 118140960795 + 516910 * 2 ^ 59
def prefixEnd_516910 : Nat := 4983230072969 + 3 ^ 40 * 516910 * 2
def baseEnd_516910 : Nat := 235931808991713618620249

theorem tailTrace_516910 : CollatzResearch.WordTrace tailWord_516910 prefixEnd_516910 235931808991713618620249 := by
  unfold tailWord_516910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2356657069666353255585523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12568837704887217363122789 2356657069666353255585523)
  ·
    refine ⟨3534985604499529883378285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2356657069666353255585523 3534985604499529883378285)
    ·
      refine ⟨1325619601687323706266857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3534985604499529883378285 1325619601687323706266857)
      ·
        refine ⟨994214701265492779700143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1325619601687323706266857 994214701265492779700143)
        ·
          refine ⟨1491322051898239169550215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994214701265492779700143 1491322051898239169550215)
          ·
            refine ⟨2236983077847358754325323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491322051898239169550215 2236983077847358754325323)
            ·
              refine ⟨3355474616771038131487985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236983077847358754325323 3355474616771038131487985)
              ·
                refine ⟨2516605962578278598615989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355474616771038131487985 2516605962578278598615989)
                ·
                  refine ⟨235931808991713618620249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2516605962578278598615989 235931808991713618620249)
                  ·
                    rfl

theorem cell20_516910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_516910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516910 prefixEnd_516910 := by exact prefixLift 516910
  have htrace : WordTrace (prefixWord ++ tailWord_516910) baseStart_516910 baseEnd_516910 := by
    simpa [prefixWord, tailWord_516910, baseEnd_516910] using wordTrace_append hprefix tailTrace_516910
  have hstable : (prefixWord ++ tailWord_516910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516910).length < 2 ^ (prefixWord ++ tailWord_516910).sum := by decide
  have hdescent : baseEnd_516910 < baseStart_516910 := by decide
  rcases family_descends (prefixWord ++ tailWord_516910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516931 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_516931 : Nat := 118140960795 + 516931 * 2 ^ 59
def prefixEnd_516931 : Nat := 4983230072969 + 3 ^ 40 * 516931 * 2
def baseEnd_516931 : Nat := 235941393963930878920163

theorem tailTrace_516931 : CollatzResearch.WordTrace tailWord_516931 prefixEnd_516931 235941393963930878920163 := by
  unfold tailWord_516931
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854022490254746631198647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12569348326836497754132431 18854022490254746631198647)
  ·
    refine ⟨28281033735382119946797971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18854022490254746631198647 28281033735382119946797971)
    ·
      refine ⟨42421550603073179920196957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28281033735382119946797971 42421550603073179920196957)
      ·
        refine ⟨15908081476152442470073859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42421550603073179920196957 15908081476152442470073859)
        ·
          refine ⟨23862122214228663705110789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908081476152442470073859 23862122214228663705110789)
          ·
            refine ⟨4474147915167874444708273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23862122214228663705110789 4474147915167874444708273)
            ·
              refine ⟨3355610936375905833531205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474147915167874444708273 3355610936375905833531205)
              ·
                refine ⟨629177050570482343787101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3355610936375905833531205 629177050570482343787101)
                ·
                  refine ⟨235941393963930878920163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629177050570482343787101 235941393963930878920163)
                  ·
                    rfl

theorem cell20_516931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_516931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516931 prefixEnd_516931 := by exact prefixLift 516931
  have htrace : WordTrace (prefixWord ++ tailWord_516931) baseStart_516931 baseEnd_516931 := by
    simpa [prefixWord, tailWord_516931, baseEnd_516931] using wordTrace_append hprefix tailTrace_516931
  have hstable : (prefixWord ++ tailWord_516931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516931).length < 2 ^ (prefixWord ++ tailWord_516931).sum := by decide
  have hdescent : baseEnd_516931 < baseStart_516931 := by decide
  rcases family_descends (prefixWord ++ tailWord_516931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516938 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_516938 : Nat := 118140960795 + 516938 * 2 ^ 59
def prefixEnd_516938 : Nat := 4983230072969 + 3 ^ 40 * 516938 * 2
def baseEnd_516938 : Nat := 235944588954669965686801

theorem tailTrace_516938 : CollatzResearch.WordTrace tailWord_516938 prefixEnd_516938 235944588954669965686801 := by
  unfold tailWord_516938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713569450307346706675867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12569518534152924551135645 4713569450307346706675867)
  ·
    refine ⟨7070354175461020060013801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713569450307346706675867 7070354175461020060013801)
    ·
      refine ⟨5302765631595765045010351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070354175461020060013801 5302765631595765045010351)
      ·
        refine ⟨7954148447393647567515527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302765631595765045010351 7954148447393647567515527)
        ·
          refine ⟨11931222671090471351273291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954148447393647567515527 11931222671090471351273291)
          ·
            refine ⟨17896834006635707026909937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931222671090471351273291 17896834006635707026909937)
            ·
              refine ⟨13422625504976780270182453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17896834006635707026909937 13422625504976780270182453)
              ·
                refine ⟨1258371141091573150329605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13422625504976780270182453 1258371141091573150329605)
                ·
                  refine ⟨235944588954669965686801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258371141091573150329605 235944588954669965686801)
                  ·
                    rfl

theorem cell20_516938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_516938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_516938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_516938 prefixEnd_516938 := by exact prefixLift 516938
  have htrace : WordTrace (prefixWord ++ tailWord_516938) baseStart_516938 baseEnd_516938 := by
    simpa [prefixWord, tailWord_516938, baseEnd_516938] using wordTrace_append hprefix tailTrace_516938
  have hstable : (prefixWord ++ tailWord_516938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516938).length < 2 ^ (prefixWord ++ tailWord_516938).sum := by decide
  have hdescent : baseEnd_516938 < baseStart_516938 := by decide
  rcases family_descends (prefixWord ++ tailWord_516938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517000 : List Nat := [2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_517000 : Nat := 118140960795 + 517000 * 2 ^ 59
def prefixEnd_517000 : Nat := 4983230072969 + 3 ^ 40 * 517000 * 2
def baseEnd_517000 : Nat := 78657629148024435206627

theorem tailTrace_517000 : CollatzResearch.WordTrace tailWord_517000 prefixEnd_517000 78657629148024435206627 := by
  unfold tailWord_517000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9428269563502385707730227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12571026084669847610306969 9428269563502385707730227)
  ·
    refine ⟨14142404345253578561595341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9428269563502385707730227 14142404345253578561595341)
    ·
      refine ⟨5303401629470091960598253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14142404345253578561595341 5303401629470091960598253)
      ·
        refine ⟨1988775611051284485224345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5303401629470091960598253 1988775611051284485224345)
        ·
          refine ⟨1491581708288463363918259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988775611051284485224345 1491581708288463363918259)
          ·
            refine ⟨2237372562432695045877389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491581708288463363918259 2237372562432695045877389)
            ·
              refine ⟨839014710912260642204021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237372562432695045877389 839014710912260642204021)
              ·
                refine ⟨78657629148024435206627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 839014710912260642204021 78657629148024435206627)
                ·
                  rfl

theorem cell20_517000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_517000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517000 prefixEnd_517000 := by exact prefixLift 517000
  have htrace : WordTrace (prefixWord ++ tailWord_517000) baseStart_517000 baseEnd_517000 := by
    simpa [prefixWord, tailWord_517000, baseEnd_517000] using wordTrace_append hprefix tailTrace_517000
  have hstable : (prefixWord ++ tailWord_517000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517000).length < 2 ^ (prefixWord ++ tailWord_517000).sum := by decide
  have hdescent : baseEnd_517000 < baseStart_517000 := by decide
  rcases family_descends (prefixWord ++ tailWord_517000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517010 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_517010 : Nat := 118140960795 + 517010 * 2 ^ 59
def prefixEnd_517010 : Nat := 4983230072969 + 3 ^ 40 * 517010 * 2
def baseEnd_517010 : Nat := 235977451716557715286507

theorem tailTrace_517010 : CollatzResearch.WordTrace tailWord_517010 prefixEnd_517010 235977451716557715286507 := by
  unfold tailWord_517010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714225964242135780831121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12571269237979028748882989 4714225964242135780831121)
  ·
    refine ⟨3535669473181601835623341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4714225964242135780831121 3535669473181601835623341)
    ·
      refine ⟨1325876052443100688358753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3535669473181601835623341 1325876052443100688358753)
      ·
        refine ⟨994407039332325516269065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1325876052443100688358753 994407039332325516269065)
        ·
          refine ⟨745805279499244137201799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994407039332325516269065 745805279499244137201799)
          ·
            refine ⟨1118707919248866205802699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745805279499244137201799 1118707919248866205802699)
            ·
              refine ⟨1678061878873299308704049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118707919248866205802699 1678061878873299308704049)
              ·
                refine ⟨1258546409154974481528037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678061878873299308704049 1258546409154974481528037)
                ·
                  refine ⟨235977451716557715286507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258546409154974481528037 235977451716557715286507)
                  ·
                    rfl

theorem cell20_517010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_517010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517010 prefixEnd_517010 := by exact prefixLift 517010
  have htrace : WordTrace (prefixWord ++ tailWord_517010) baseStart_517010 baseEnd_517010 := by
    simpa [prefixWord, tailWord_517010, baseEnd_517010] using wordTrace_append hprefix tailTrace_517010
  have hstable : (prefixWord ++ tailWord_517010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517010).length < 2 ^ (prefixWord ++ tailWord_517010).sum := by decide
  have hdescent : baseEnd_517010 < baseStart_517010 := by decide
  rcases family_descends (prefixWord ++ tailWord_517010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517037 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 3]
def baseStart_517037 : Nat := 118140960795 + 517037 * 2 ^ 59
def prefixEnd_517037 : Nat := 4983230072969 + 3 ^ 40 * 517037 * 2
def baseEnd_517037 : Nat := 235989775252265621386397

theorem tailTrace_517037 : CollatzResearch.WordTrace tailWord_517037 prefixEnd_517037 235989775252265621386397 := by
  unfold tailWord_517037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18857888627870726734557365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12571925751913817823038243 18857888627870726734557365)
  ·
    refine ⟨1767927058862880631364753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18857888627870726734557365 1767927058862880631364753)
    ·
      refine ⟨1325945294147160473523565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1767927058862880631364753 1325945294147160473523565)
      ·
        refine ⟨497229485305185177571337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1325945294147160473523565 497229485305185177571337)
        ·
          refine ⟨372922113978888883178503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497229485305185177571337 372922113978888883178503)
          ·
            refine ⟨559383170968333324767755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372922113978888883178503 559383170968333324767755)
            ·
              refine ⟨839074756452499987151633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559383170968333324767755 839074756452499987151633)
              ·
                refine ⟨629306067339374990363725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839074756452499987151633 629306067339374990363725)
                ·
                  refine ⟨235989775252265621386397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629306067339374990363725 235989775252265621386397)
                  ·
                    rfl

theorem cell20_517037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_517037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517037 prefixEnd_517037 := by exact prefixLift 517037
  have htrace : WordTrace (prefixWord ++ tailWord_517037) baseStart_517037 baseEnd_517037 := by
    simpa [prefixWord, tailWord_517037, baseEnd_517037] using wordTrace_append hprefix tailTrace_517037
  have hstable : (prefixWord ++ tailWord_517037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517037).length < 2 ^ (prefixWord ++ tailWord_517037).sum := by decide
  have hdescent : baseEnd_517037 < baseStart_517037 := by decide
  rcases family_descends (prefixWord ++ tailWord_517037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
