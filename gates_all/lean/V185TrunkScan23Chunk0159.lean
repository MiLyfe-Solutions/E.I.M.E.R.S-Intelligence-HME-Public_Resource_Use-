import V185TrunkScan23Chunk0158

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_940140 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_940140 : Nat := 118140960795 + 940140 * 2 ^ 59
def prefixEnd_940140 : Nat := 4983230072969 + 3 ^ 40 * 940140 * 2
def baseEnd_940140 : Nat := 482743702518056931626381

theorem tailTrace_940140 : CollatzResearch.WordTrace tailWord_940140 prefixEnd_940140 482743702518056931626381 := by
  unfold tailWord_940140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144861407020408987012937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22859815209360545316017249 17144861407020408987012937)
  ·
    refine ⟨12858646055265306740259703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17144861407020408987012937 12858646055265306740259703)
    ·
      refine ⟨19287969082897960110389555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12858646055265306740259703 19287969082897960110389555)
      ·
        refine ⟨28931953624346940165584333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19287969082897960110389555 28931953624346940165584333)
        ·
          refine ⟨10849482609130102562094125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28931953624346940165584333 10849482609130102562094125)
          ·
            refine ⟨4068555978423788460785297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10849482609130102562094125 4068555978423788460785297)
            ·
              refine ⟨3051416983817841345588973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068555978423788460785297 3051416983817841345588973)
              ·
                refine ⟨1144281368931690504595865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051416983817841345588973 1144281368931690504595865)
                ·
                  refine ⟨858211026698767878446899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144281368931690504595865 858211026698767878446899)
                  ·
                    refine ⟨1287316540048151817670349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858211026698767878446899 1287316540048151817670349)
                    ·
                      refine ⟨482743702518056931626381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287316540048151817670349 482743702518056931626381)
                      ·
                        rfl

theorem cell23_940140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_940140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940140 prefixEnd_940140 := by exact prefixLift 940140
  have htrace : WordTrace (prefixWord ++ tailWord_940140) baseStart_940140 baseEnd_940140 := by
    simpa [prefixWord, tailWord_940140, baseEnd_940140] using wordTrace_append hprefix tailTrace_940140
  have hstable : (prefixWord ++ tailWord_940140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940140).length < 2 ^ (prefixWord ++ tailWord_940140).sum := by decide
  have hdescent : baseEnd_940140 < baseStart_940140 := by decide
  rcases family_descends (prefixWord ++ tailWord_940140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940167 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_940167 : Nat := 118140960795 + 940167 * 2 ^ 59
def prefixEnd_940167 : Nat := 4983230072969 + 3 ^ 40 * 940167 * 2
def baseEnd_940167 : Nat := 482757566495728325988757

theorem tailTrace_940167 : CollatzResearch.WordTrace tailWord_940167 prefixEnd_940167 482757566495728325988757 := by
  unfold tailWord_940167
  simp only [CollatzResearch.WordTrace]
  refine ⟨34290707584943001585258755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22860471723295334390172503 34290707584943001585258755)
  ·
    refine ⟨51436061377414502377888133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34290707584943001585258755 51436061377414502377888133)
    ·
      refine ⟨9644261508265219195854025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51436061377414502377888133 9644261508265219195854025)
      ·
        refine ⟨7233196131198914396890519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9644261508265219195854025 7233196131198914396890519)
        ·
          refine ⟨10849794196798371595335779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233196131198914396890519 10849794196798371595335779)
          ·
            refine ⟨16274691295197557393003669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849794196798371595335779 16274691295197557393003669)
            ·
              refine ⟨762876154462385502797047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16274691295197557393003669 762876154462385502797047)
              ·
                refine ⟨1144314231693578254195571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762876154462385502797047 1144314231693578254195571)
                ·
                  refine ⟨1716471347540367381293357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144314231693578254195571 1716471347540367381293357)
                  ·
                    refine ⟨643676755327637767985009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716471347540367381293357 643676755327637767985009)
                    ·
                      refine ⟨482757566495728325988757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643676755327637767985009 482757566495728325988757)
                      ·
                        rfl

theorem cell23_940167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_940167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940167 prefixEnd_940167 := by exact prefixLift 940167
  have htrace : WordTrace (prefixWord ++ tailWord_940167) baseStart_940167 baseEnd_940167 := by
    simpa [prefixWord, tailWord_940167, baseEnd_940167] using wordTrace_append hprefix tailTrace_940167
  have hstable : (prefixWord ++ tailWord_940167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940167).length < 2 ^ (prefixWord ++ tailWord_940167).sum := by decide
  have hdescent : baseEnd_940167 < baseStart_940167 := by decide
  rcases family_descends (prefixWord ++ tailWord_940167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940174 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_940174 : Nat := 118140960795 + 940174 * 2 ^ 59
def prefixEnd_940174 : Nat := 4983230072969 + 3 ^ 40 * 940174 * 2
def baseEnd_940174 : Nat := 482761160860309798601225

theorem tailTrace_940174 : CollatzResearch.WordTrace tailWord_940174 prefixEnd_940174 482761160860309798601225 := by
  unfold tailWord_940174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286370361989705222595447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22860641930611761187175717 4286370361989705222595447)
  ·
    refine ⟨6429555542984557833893171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286370361989705222595447 6429555542984557833893171)
    ·
      refine ⟨9644333314476836750839757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429555542984557833893171 9644333314476836750839757)
      ·
        refine ⟨3616624992928813781564909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9644333314476836750839757 3616624992928813781564909)
        ·
          refine ⟨1356234372348305168086841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3616624992928813781564909 1356234372348305168086841)
          ·
            refine ⟨1017175779261228876065131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356234372348305168086841 1017175779261228876065131)
            ·
              refine ⟨1525763668891843314097697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017175779261228876065131 1525763668891843314097697)
              ·
                refine ⟨1144322751668882485573273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525763668891843314097697 1144322751668882485573273)
                ·
                  refine ⟨858242063751661864179955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144322751668882485573273 858242063751661864179955)
                  ·
                    refine ⟨1287363095627492796269933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858242063751661864179955 1287363095627492796269933)
                    ·
                      refine ⟨482761160860309798601225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287363095627492796269933 482761160860309798601225)
                      ·
                        rfl

theorem cell23_940174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_940174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940174 prefixEnd_940174 := by exact prefixLift 940174
  have htrace : WordTrace (prefixWord ++ tailWord_940174) baseStart_940174 baseEnd_940174 := by
    simpa [prefixWord, tailWord_940174, baseEnd_940174] using wordTrace_append hprefix tailTrace_940174
  have hstable : (prefixWord ++ tailWord_940174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940174).length < 2 ^ (prefixWord ++ tailWord_940174).sum := by decide
  have hdescent : baseEnd_940174 < baseStart_940174 := by decide
  rcases family_descends (prefixWord ++ tailWord_940174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940176 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_940176 : Nat := 118140960795 + 940176 * 2 ^ 59
def prefixEnd_940176 : Nat := 4983230072969 + 3 ^ 40 * 940176 * 2
def baseEnd_940176 : Nat := 482762187821618790776215

theorem tailTrace_940176 : CollatzResearch.WordTrace tailWord_940176 prefixEnd_940176 482762187821618790776215 := by
  unfold tailWord_940176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17145517920955198061168191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22860690561273597414890921 17145517920955198061168191)
  ·
    refine ⟨25718276881432797091752287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17145517920955198061168191 25718276881432797091752287)
    ·
      refine ⟨38577415322149195637628431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25718276881432797091752287 38577415322149195637628431)
      ·
        refine ⟨57866122983223793456442647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38577415322149195637628431 57866122983223793456442647)
        ·
          refine ⟨86799184474835690184663971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57866122983223793456442647 86799184474835690184663971)
          ·
            refine ⟨130198776712253535276995957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86799184474835690184663971 130198776712253535276995957)
            ·
              refine ⟨12206135316773768932218371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130198776712253535276995957 12206135316773768932218371)
              ·
                refine ⟨18309202975160653398327557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206135316773768932218371 18309202975160653398327557)
                ·
                  refine ⟨3432975557842622512186417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18309202975160653398327557 3432975557842622512186417)
                  ·
                    refine ⟨2574731668381966884139813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432975557842622512186417 2574731668381966884139813)
                    ·
                      refine ⟨482762187821618790776215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2574731668381966884139813 482762187821618790776215)
                      ·
                        rfl

theorem cell23_940176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_940176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940176 prefixEnd_940176 := by exact prefixLift 940176
  have htrace : WordTrace (prefixWord ++ tailWord_940176) baseStart_940176 baseEnd_940176 := by
    simpa [prefixWord, tailWord_940176, baseEnd_940176] using wordTrace_append hprefix tailTrace_940176
  have hstable : (prefixWord ++ tailWord_940176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940176).length < 2 ^ (prefixWord ++ tailWord_940176).sum := by decide
  have hdescent : baseEnd_940176 < baseStart_940176 := by decide
  rcases family_descends (prefixWord ++ tailWord_940176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940193 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_940193 : Nat := 118140960795 + 940193 * 2 ^ 59
def prefixEnd_940193 : Nat := 4983230072969 + 3 ^ 40 * 940193 * 2
def baseEnd_940193 : Nat := 482770916992745224263637

theorem tailTrace_940193 : CollatzResearch.WordTrace tailWord_940193 prefixEnd_940193 482770916992745224263637 := by
  unfold tailWord_940193
  simp only [CollatzResearch.WordTrace]
  refine ⟨34291655882848808025705233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22861103921899205350470155 34291655882848808025705233)
  ·
    refine ⟨25718741912136606019278925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34291655882848808025705233 25718741912136606019278925)
    ·
      refine ⟨9644528217051227257229597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25718741912136606019278925 9644528217051227257229597)
      ·
        refine ⟨3616698081394210221461099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9644528217051227257229597 3616698081394210221461099)
        ·
          refine ⟨5425047122091315332191649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616698081394210221461099 5425047122091315332191649)
          ·
            refine ⟨4068785341568486499143737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425047122091315332191649 4068785341568486499143737)
            ·
              refine ⟨3051589006176364874357803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068785341568486499143737 3051589006176364874357803)
              ·
                refine ⟨4577383509264547311536705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051589006176364874357803 4577383509264547311536705)
                ·
                  refine ⟨3433037631948410483652529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4577383509264547311536705 3433037631948410483652529)
                  ·
                    refine ⟨2574778223961307862739397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3433037631948410483652529 2574778223961307862739397)
                    ·
                      refine ⟨482770916992745224263637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2574778223961307862739397 482770916992745224263637)
                      ·
                        rfl

theorem cell23_940193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_940193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940193 prefixEnd_940193 := by exact prefixLift 940193
  have htrace : WordTrace (prefixWord ++ tailWord_940193) baseStart_940193 baseEnd_940193 := by
    simpa [prefixWord, tailWord_940193, baseEnd_940193] using wordTrace_append hprefix tailTrace_940193
  have hstable : (prefixWord ++ tailWord_940193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940193).length < 2 ^ (prefixWord ++ tailWord_940193).sum := by decide
  have hdescent : baseEnd_940193 < baseStart_940193 := by decide
  rcases family_descends (prefixWord ++ tailWord_940193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940216 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_940216 : Nat := 118140960795 + 940216 * 2 ^ 59
def prefixEnd_940216 : Nat := 4983230072969 + 3 ^ 40 * 940216 * 2
def baseEnd_940216 : Nat := 160927575682599544758677

theorem tailTrace_940216 : CollatzResearch.WordTrace tailWord_940216 prefixEnd_940216 160927575682599544758677 := by
  unfold tailWord_940216
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146247380882741476896251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22861663174510321969195001 17146247380882741476896251)
  ·
    refine ⟨25719371071324112215344377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17146247380882741476896251 25719371071324112215344377)
    ·
      refine ⟨19289528303493084161508283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25719371071324112215344377 19289528303493084161508283)
      ·
        refine ⟨28934292455239626242262425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19289528303493084161508283 28934292455239626242262425)
        ·
          refine ⟨21700719341429719681696819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28934292455239626242262425 21700719341429719681696819)
          ·
            refine ⟨32551079012144579522545229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21700719341429719681696819 32551079012144579522545229)
            ·
              refine ⟨12206654629554217320954461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32551079012144579522545229 12206654629554217320954461)
              ·
                refine ⟨4577495486082831495357923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12206654629554217320954461 4577495486082831495357923)
                ·
                  refine ⟨6866243229124247243036885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577495486082831495357923 6866243229124247243036885)
                  ·
                    refine ⟨160927575682599544758677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6866243229124247243036885 160927575682599544758677)
                    ·
                      rfl

theorem cell23_940216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_940216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940216 prefixEnd_940216 := by exact prefixLift 940216
  have htrace : WordTrace (prefixWord ++ tailWord_940216) baseStart_940216 baseEnd_940216 := by
    simpa [prefixWord, tailWord_940216, baseEnd_940216] using wordTrace_append hprefix tailTrace_940216
  have hstable : (prefixWord ++ tailWord_940216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940216).length < 2 ^ (prefixWord ++ tailWord_940216).sum := by decide
  have hdescent : baseEnd_940216 < baseStart_940216 := by decide
  rcases family_descends (prefixWord ++ tailWord_940216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940223 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 7, 2]
def baseStart_940223 : Nat := 118140960795 + 940223 * 2 ^ 59
def prefixEnd_940223 : Nat := 4983230072969 + 3 ^ 40 * 940223 * 2
def baseEnd_940223 : Nat := 482786321412380106888499

theorem tailTrace_940223 : CollatzResearch.WordTrace tailWord_940223 prefixEnd_940223 482786321412380106888499 := by
  unfold tailWord_940223
  simp only [CollatzResearch.WordTrace]
  refine ⟨34292750072740123149297323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22861833381826748766198215 34292750072740123149297323)
  ·
    refine ⟨51439125109110184723945985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34292750072740123149297323 51439125109110184723945985)
    ·
      refine ⟨38579343831832638542959489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51439125109110184723945985 38579343831832638542959489)
      ·
        refine ⟨28934507873874478907219617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38579343831832638542959489 28934507873874478907219617)
        ·
          refine ⟨21700880905405859180414713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28934507873874478907219617 21700880905405859180414713)
          ·
            refine ⟨16275660679054394385311035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21700880905405859180414713 16275660679054394385311035)
            ·
              refine ⟨24413491018581591577966553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16275660679054394385311035 24413491018581591577966553)
              ·
                refine ⟨18310118263936193683474915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24413491018581591577966553 18310118263936193683474915)
                ·
                  refine ⟨27465177395904290525212373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310118263936193683474915 27465177395904290525212373)
                  ·
                    refine ⟨643715095216506809184665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27465177395904290525212373 643715095216506809184665)
                    ·
                      refine ⟨482786321412380106888499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643715095216506809184665 482786321412380106888499)
                      ·
                        rfl

theorem cell23_940223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_940223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940223 prefixEnd_940223 := by exact prefixLift 940223
  have htrace : WordTrace (prefixWord ++ tailWord_940223) baseStart_940223 baseEnd_940223 := by
    simpa [prefixWord, tailWord_940223, baseEnd_940223] using wordTrace_append hprefix tailTrace_940223
  have hstable : (prefixWord ++ tailWord_940223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940223).length < 2 ^ (prefixWord ++ tailWord_940223).sum := by decide
  have hdescent : baseEnd_940223 < baseStart_940223 := by decide
  rcases family_descends (prefixWord ++ tailWord_940223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940270 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_940270 : Nat := 118140960795 + 940270 * 2 ^ 59
def prefixEnd_940270 : Nat := 4983230072969 + 3 ^ 40 * 940270 * 2
def baseEnd_940270 : Nat := 482810455003141423000783

theorem tailTrace_940270 : CollatzResearch.WordTrace tailWord_940270 prefixEnd_940270 482810455003141423000783 := by
  unfold tailWord_940270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286808037946231272032283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22862976202379900117505509 4286808037946231272032283)
  ·
    refine ⟨6430212056919346908048425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286808037946231272032283 6430212056919346908048425)
    ·
      refine ⟨4822659042689510181036319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430212056919346908048425 4822659042689510181036319)
      ·
        refine ⟨7233988564034265271554479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822659042689510181036319 7233988564034265271554479)
        ·
          refine ⟨10850982846051397907331719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233988564034265271554479 10850982846051397907331719)
          ·
            refine ⟨16276474269077096860997579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850982846051397907331719 16276474269077096860997579)
            ·
              refine ⟨24414711403615645291496369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276474269077096860997579 24414711403615645291496369)
              ·
                refine ⟨18311033552711733968622277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24414711403615645291496369 18311033552711733968622277)
                ·
                  refine ⟨3433318791133450119116677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18311033552711733968622277 3433318791133450119116677)
                  ·
                    refine ⟨643747273337521897334377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433318791133450119116677 643747273337521897334377)
                    ·
                      refine ⟨482810455003141423000783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643747273337521897334377 482810455003141423000783)
                      ·
                        rfl

theorem cell23_940270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_940270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940270 prefixEnd_940270 := by exact prefixLift 940270
  have htrace : WordTrace (prefixWord ++ tailWord_940270) baseStart_940270 baseEnd_940270 := by
    simpa [prefixWord, tailWord_940270, baseEnd_940270] using wordTrace_append hprefix tailTrace_940270
  have hstable : (prefixWord ++ tailWord_940270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940270).length < 2 ^ (prefixWord ++ tailWord_940270).sum := by decide
  have hdescent : baseEnd_940270 < baseStart_940270 := by decide
  rcases family_descends (prefixWord ++ tailWord_940270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940273 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_940273 : Nat := 118140960795 + 940273 * 2 ^ 59
def prefixEnd_940273 : Nat := 4983230072969 + 3 ^ 40 * 940273 * 2
def baseEnd_940273 : Nat := 482811995445104911263269

theorem tailTrace_940273 : CollatzResearch.WordTrace tailWord_940273 prefixEnd_940273 482811995445104911263269 := by
  unfold tailWord_940273
  simp only [CollatzResearch.WordTrace]
  refine ⟨34294573722558981688617473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22863049148372654459078315 34294573722558981688617473)
  ·
    refine ⟨25720930291919236266463105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34294573722558981688617473 25720930291919236266463105)
    ·
      refine ⟨19290697718939427199847329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25720930291919236266463105 19290697718939427199847329)
      ·
        refine ⟨14468023289204570399885497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19290697718939427199847329 14468023289204570399885497)
        ·
          refine ⟨10851017466903427799914123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14468023289204570399885497 10851017466903427799914123)
          ·
            refine ⟨16276526200355141699871185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10851017466903427799914123 16276526200355141699871185)
            ·
              refine ⟨12207394650266356274903389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16276526200355141699871185 12207394650266356274903389)
              ·
                refine ⟨4577772993849883603088771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12207394650266356274903389 4577772993849883603088771)
                ·
                  refine ⟨6866659490774825404633157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577772993849883603088771 6866659490774825404633157)
                  ·
                    refine ⟨1287498654520279763368717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866659490774825404633157 1287498654520279763368717)
                    ·
                      refine ⟨482811995445104911263269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287498654520279763368717 482811995445104911263269)
                      ·
                        rfl

theorem cell23_940273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_940273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940273 prefixEnd_940273 := by exact prefixLift 940273
  have htrace : WordTrace (prefixWord ++ tailWord_940273) baseStart_940273 baseEnd_940273 := by
    simpa [prefixWord, tailWord_940273, baseEnd_940273] using wordTrace_append hprefix tailTrace_940273
  have hstable : (prefixWord ++ tailWord_940273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940273).length < 2 ^ (prefixWord ++ tailWord_940273).sum := by decide
  have hdescent : baseEnd_940273 < baseStart_940273 := by decide
  rcases family_descends (prefixWord ++ tailWord_940273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940297 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 1, 4]
def baseStart_940297 : Nat := 118140960795 + 940297 * 2 ^ 59
def prefixEnd_940297 : Nat := 4983230072969 + 3 ^ 40 * 940297 * 2
def baseEnd_940297 : Nat := 160941439660270939121053

theorem tailTrace_940297 : CollatzResearch.WordTrace tailWord_940297 prefixEnd_940297 160941439660270939121053 := by
  unfold tailWord_940297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295449074472033787491145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22863632716314689191660763 34295449074472033787491145)
  ·
    refine ⟨25721586805854025340618359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34295449074472033787491145 25721586805854025340618359)
    ·
      refine ⟨38582380208781038010927539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25721586805854025340618359 38582380208781038010927539)
      ·
        refine ⟨57873570313171557016391309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38582380208781038010927539 57873570313171557016391309)
        ·
          refine ⟨21702588867439333881146741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57873570313171557016391309 21702588867439333881146741)
          ·
            refine ⟨2034617706322437551357507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21702588867439333881146741 2034617706322437551357507)
            ·
              refine ⟨3051926559483656327036261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034617706322437551357507 3051926559483656327036261)
              ·
                refine ⟨572236229903185561319299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3051926559483656327036261 572236229903185561319299)
                ·
                  refine ⟨858354344854778341978949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572236229903185561319299 858354344854778341978949)
                  ·
                    refine ⟨160941439660270939121053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 858354344854778341978949 160941439660270939121053)
                    ·
                      rfl

theorem cell23_940297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 4].length) (baseStart_940297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940297 prefixEnd_940297 := by exact prefixLift 940297
  have htrace : WordTrace (prefixWord ++ tailWord_940297) baseStart_940297 baseEnd_940297 := by
    simpa [prefixWord, tailWord_940297, baseEnd_940297] using wordTrace_append hprefix tailTrace_940297
  have hstable : (prefixWord ++ tailWord_940297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940297).length < 2 ^ (prefixWord ++ tailWord_940297).sum := by decide
  have hdescent : baseEnd_940297 < baseStart_940297 := by decide
  rcases family_descends (prefixWord ++ tailWord_940297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940323 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 3, 5]
def baseStart_940323 : Nat := 118140960795 + 940323 * 2 ^ 59
def prefixEnd_940323 : Nat := 4983230072969 + 3 ^ 40 * 940323 * 2
def baseEnd_940323 : Nat := 160945889825943238546013

theorem tailTrace_940323 : CollatzResearch.WordTrace tailWord_940323 prefixEnd_940323 160945889825943238546013 := by
  unfold tailWord_940323
  simp only [CollatzResearch.WordTrace]
  refine ⟨34296397372377840227937623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22864264914918560151958415 34296397372377840227937623)
  ·
    refine ⟨51444596058566760341906435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34296397372377840227937623 51444596058566760341906435)
    ·
      refine ⟨77166894087850140512859653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51444596058566760341906435 77166894087850140512859653)
      ·
        refine ⟨14468792641471901346161185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77166894087850140512859653 14468792641471901346161185)
        ·
          refine ⟨10851594481103926009620889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14468792641471901346161185 10851594481103926009620889)
          ·
            refine ⟨8138695860827944507215667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10851594481103926009620889 8138695860827944507215667)
            ·
              refine ⟨12208043791241916760823501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138695860827944507215667 12208043791241916760823501)
              ·
                refine ⟨4578016421715718785308813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12208043791241916760823501 4578016421715718785308813)
                ·
                  refine ⟨1716756158143394544490805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4578016421715718785308813 1716756158143394544490805)
                  ·
                    refine ⟨160945889825943238546013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1716756158143394544490805 160945889825943238546013)
                    ·
                      rfl

theorem cell23_940323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 5].length) (baseStart_940323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940323 prefixEnd_940323 := by exact prefixLift 940323
  have htrace : WordTrace (prefixWord ++ tailWord_940323) baseStart_940323 baseEnd_940323 := by
    simpa [prefixWord, tailWord_940323, baseEnd_940323] using wordTrace_append hprefix tailTrace_940323
  have hstable : (prefixWord ++ tailWord_940323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940323).length < 2 ^ (prefixWord ++ tailWord_940323).sum := by decide
  have hdescent : baseEnd_940323 < baseStart_940323 := by decide
  rcases family_descends (prefixWord ++ tailWord_940323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940363 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3]
def baseStart_940363 : Nat := 118140960795 + 940363 * 2 ^ 59
def prefixEnd_940363 : Nat := 4983230072969 + 3 ^ 40 * 940363 * 2
def baseEnd_940363 : Nat := 482858208704009559137855

theorem tailTrace_940363 : CollatzResearch.WordTrace tailWord_940363 prefixEnd_940363 482858208704009559137855 := by
  unfold tailWord_940363
  simp only [CollatzResearch.WordTrace]
  refine ⟨34297856292232927059393743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22865237528155284706262495 34297856292232927059393743)
  ·
    refine ⟨51446784438349390589090615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34297856292232927059393743 51446784438349390589090615)
    ·
      refine ⟨77170176657524085883635923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51446784438349390589090615 77170176657524085883635923)
      ·
        refine ⟨115755264986286128825453885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77170176657524085883635923 115755264986286128825453885)
        ·
          refine ⟨43408224369857298309545207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115755264986286128825453885 43408224369857298309545207)
          ·
            refine ⟨65112336554785947464317811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43408224369857298309545207 65112336554785947464317811)
            ·
              refine ⟨97668504832178921196476717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65112336554785947464317811 97668504832178921196476717)
              ·
                refine ⟨36625689312067095448678769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97668504832178921196476717 36625689312067095448678769)
                ·
                  refine ⟨27469266984050321586509077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36625689312067095448678769 27469266984050321586509077)
                  ·
                    refine ⟨1287621889877358824367613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27469266984050321586509077 1287621889877358824367613)
                    ·
                      refine ⟨482858208704009559137855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287621889877358824367613 482858208704009559137855)
                      ·
                        rfl

theorem cell23_940363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 3].length) (baseStart_940363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940363 prefixEnd_940363 := by exact prefixLift 940363
  have htrace : WordTrace (prefixWord ++ tailWord_940363) baseStart_940363 baseEnd_940363 := by
    simpa [prefixWord, tailWord_940363, baseEnd_940363] using wordTrace_append hprefix tailTrace_940363
  have hstable : (prefixWord ++ tailWord_940363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940363).length < 2 ^ (prefixWord ++ tailWord_940363).sum := by decide
  have hdescent : baseEnd_940363 < baseStart_940363 := by decide
  rcases family_descends (prefixWord ++ tailWord_940363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940370 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_940370 : Nat := 118140960795 + 940370 * 2 ^ 59
def prefixEnd_940370 : Nat := 4983230072969 + 3 ^ 40 * 940370 * 2
def baseEnd_940370 : Nat := 160953934356197010583441

theorem tailTrace_940370 : CollatzResearch.WordTrace tailWord_940370 prefixEnd_940370 160953934356197010583441 := by
  unfold tailWord_940370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574527900801891813724641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22865407735471711503265709 8574527900801891813724641)
  ·
    refine ⟨6430895925601418860293481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8574527900801891813724641 6430895925601418860293481)
    ·
      refine ⟨4823171944201064145220111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430895925601418860293481 4823171944201064145220111)
      ·
        refine ⟨7234757916301596217830167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823171944201064145220111 7234757916301596217830167)
        ·
          refine ⟨10852136874452394326745251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234757916301596217830167 10852136874452394326745251)
          ·
            refine ⟨16278205311678591490117877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10852136874452394326745251 16278205311678591490117877)
            ·
              refine ⟨1526081747969867952198551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16278205311678591490117877 1526081747969867952198551)
              ·
                refine ⟨2289122621954801928297827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526081747969867952198551 2289122621954801928297827)
                ·
                  refine ⟨3433683932932202892446741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289122621954801928297827 3433683932932202892446741)
                  ·
                    refine ⟨160953934356197010583441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3433683932932202892446741 160953934356197010583441)
                    ·
                      rfl

theorem cell23_940370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_940370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940370 prefixEnd_940370 := by exact prefixLift 940370
  have htrace : WordTrace (prefixWord ++ tailWord_940370) baseStart_940370 baseEnd_940370 := by
    simpa [prefixWord, tailWord_940370, baseEnd_940370] using wordTrace_append hprefix tailTrace_940370
  have hstable : (prefixWord ++ tailWord_940370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940370).length < 2 ^ (prefixWord ++ tailWord_940370).sum := by decide
  have hdescent : baseEnd_940370 < baseStart_940370 := by decide
  rcases family_descends (prefixWord ++ tailWord_940370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940382 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_940382 : Nat := 118140960795 + 940382 * 2 ^ 59
def prefixEnd_940382 : Nat := 4983230072969 + 3 ^ 40 * 940382 * 2
def baseEnd_940382 : Nat := 160955988278814994933423

theorem tailTrace_940382 : CollatzResearch.WordTrace tailWord_940382 prefixEnd_940382 160955988278814994933423 := by
  unfold tailWord_940382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287318659895511663041925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22865699519442728869556933 4287318659895511663041925)
  ·
    refine ⟨803872248730408436820361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4287318659895511663041925 803872248730408436820361)
    ·
      refine ⟨602904186547806327615271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 803872248730408436820361 602904186547806327615271)
      ·
        refine ⟨904356279821709491422907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602904186547806327615271 904356279821709491422907)
        ·
          refine ⟨1356534419732564237134361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904356279821709491422907 1356534419732564237134361)
          ·
            refine ⟨1017400814799423177850771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356534419732564237134361 1017400814799423177850771)
            ·
              refine ⟨1526101222199134766776157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017400814799423177850771 1526101222199134766776157)
              ·
                refine ⟨572287958324675537541059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526101222199134766776157 572287958324675537541059)
                ·
                  refine ⟨858431937487013306311589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572287958324675537541059 858431937487013306311589)
                  ·
                    refine ⟨160955988278814994933423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 858431937487013306311589 160955988278814994933423)
                    ·
                      rfl

theorem cell23_940382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_940382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940382 prefixEnd_940382 := by exact prefixLift 940382
  have htrace : WordTrace (prefixWord ++ tailWord_940382) baseStart_940382 baseEnd_940382 := by
    simpa [prefixWord, tailWord_940382, baseEnd_940382] using wordTrace_append hprefix tailTrace_940382
  have hstable : (prefixWord ++ tailWord_940382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940382).length < 2 ^ (prefixWord ++ tailWord_940382).sum := by decide
  have hdescent : baseEnd_940382 < baseStart_940382 := by decide
  rcases family_descends (prefixWord ++ tailWord_940382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940397 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_940397 : Nat := 118140960795 + 940397 * 2 ^ 59
def prefixEnd_940397 : Nat := 4983230072969 + 3 ^ 40 * 940397 * 2
def baseEnd_940397 : Nat := 482875667046262426112699

theorem tailTrace_940397 : CollatzResearch.WordTrace tailWord_940397 prefixEnd_940397 482875667046262426112699 := by
  unfold tailWord_940397
  simp only [CollatzResearch.WordTrace]
  refine ⟨34299096374109750866131445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22866064249406500577420963 34299096374109750866131445)
  ·
    refine ⟨3215540285072789143699823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34299096374109750866131445 3215540285072789143699823)
    ·
      refine ⟨4823310427609183715549735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215540285072789143699823 4823310427609183715549735)
      ·
        refine ⟨7234965641413775573324603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823310427609183715549735 7234965641413775573324603)
        ·
          refine ⟨10852448462120663359986905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234965641413775573324603 10852448462120663359986905)
          ·
            refine ⟨8139336346590497519990179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10852448462120663359986905 8139336346590497519990179)
            ·
              refine ⟨12209004519885746279985269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139336346590497519990179 12209004519885746279985269)
              ·
                refine ⟨1144594173739288713748619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12209004519885746279985269 1144594173739288713748619)
                ·
                  refine ⟨1716891260608933070622929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144594173739288713748619 1716891260608933070622929)
                  ·
                    refine ⟨1287668445456699802967197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1716891260608933070622929 1287668445456699802967197)
                    ·
                      refine ⟨482875667046262426112699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287668445456699802967197 482875667046262426112699)
                      ·
                        rfl

theorem cell23_940397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_940397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940397 prefixEnd_940397 := by exact prefixLift 940397
  have htrace : WordTrace (prefixWord ++ tailWord_940397) baseStart_940397 baseEnd_940397 := by
    simpa [prefixWord, tailWord_940397, baseEnd_940397] using wordTrace_append hprefix tailTrace_940397
  have hstable : (prefixWord ++ tailWord_940397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940397).length < 2 ^ (prefixWord ++ tailWord_940397).sum := by decide
  have hdescent : baseEnd_940397 < baseStart_940397 := by decide
  rcases family_descends (prefixWord ++ tailWord_940397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940463 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_940463 : Nat := 118140960795 + 940463 * 2 ^ 59
def prefixEnd_940463 : Nat := 4983230072969 + 3 ^ 40 * 940463 * 2
def baseEnd_940463 : Nat := 482909556769459167887395

theorem tailTrace_940463 : CollatzResearch.WordTrace tailWord_940463 prefixEnd_940463 482909556769459167887395 := by
  unfold tailWord_940463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301503591870644138034043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22867669061247096092022695 34301503591870644138034043)
  ·
    refine ⟨51452255387805966207051065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34301503591870644138034043 51452255387805966207051065)
    ·
      refine ⟨38589191540854474655288299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51452255387805966207051065 38589191540854474655288299)
      ·
        refine ⟨57883787311281711982932449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38589191540854474655288299 57883787311281711982932449)
        ·
          refine ⟨43412840483461283987199337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57883787311281711982932449 43412840483461283987199337)
          ·
            refine ⟨32559630362595962990399503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43412840483461283987199337 32559630362595962990399503)
            ·
              refine ⟨48839445543893944485599255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32559630362595962990399503 48839445543893944485599255)
              ·
                refine ⟨73259168315840916728398883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48839445543893944485599255 73259168315840916728398883)
                ·
                  refine ⟨109888752473761375092598325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73259168315840916728398883 109888752473761375092598325)
                  ·
                    refine ⟨10302070544415128914931093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109888752473761375092598325 10302070544415128914931093)
                    ·
                      refine ⟨482909556769459167887395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10302070544415128914931093 482909556769459167887395)
                      ·
                        rfl

theorem cell23_940463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_940463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940463 prefixEnd_940463 := by exact prefixLift 940463
  have htrace : WordTrace (prefixWord ++ tailWord_940463) baseStart_940463 baseEnd_940463 := by
    simpa [prefixWord, tailWord_940463, baseEnd_940463] using wordTrace_append hprefix tailTrace_940463
  have hstable : (prefixWord ++ tailWord_940463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940463).length < 2 ^ (prefixWord ++ tailWord_940463).sum := by decide
  have hdescent : baseEnd_940463 < baseStart_940463 := by decide
  rcases family_descends (prefixWord ++ tailWord_940463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940490 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_940490 : Nat := 118140960795 + 940490 * 2 ^ 59
def prefixEnd_940490 : Nat := 4983230072969 + 3 ^ 40 * 940490 * 2
def baseEnd_940490 : Nat := 53658157860792284694419

theorem tailTrace_940490 : CollatzResearch.WordTrace tailWord_940490 prefixEnd_940490 53658157860792284694419 := by
  unfold tailWord_940490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575622090693206937316731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22868325575181885166177949 8575622090693206937316731)
  ·
    refine ⟨12863433136039810405975097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8575622090693206937316731 12863433136039810405975097)
    ·
      refine ⟨9647574852029857804481323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12863433136039810405975097 9647574852029857804481323)
      ·
        refine ⟨14471362278044786706721985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647574852029857804481323 14471362278044786706721985)
        ·
          refine ⟨10853521708533590030041489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14471362278044786706721985 10853521708533590030041489)
          ·
            refine ⟨8140141281400192522531117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10853521708533590030041489 8140141281400192522531117)
            ·
              refine ⟨3052552980525072195949169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8140141281400192522531117 3052552980525072195949169)
              ·
                refine ⟨2289414735393804146961877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052552980525072195949169 2289414735393804146961877)
                ·
                  refine ⟨53658157860792284694419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2289414735393804146961877 53658157860792284694419)
                  ·
                    rfl

theorem cell23_940490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_940490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940490 prefixEnd_940490 := by exact prefixLift 940490
  have htrace : WordTrace (prefixWord ++ tailWord_940490) baseStart_940490 baseEnd_940490 := by
    simpa [prefixWord, tailWord_940490, baseEnd_940490] using wordTrace_append hprefix tailTrace_940490
  have hstable : (prefixWord ++ tailWord_940490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940490).length < 2 ^ (prefixWord ++ tailWord_940490).sum := by decide
  have hdescent : baseEnd_940490 < baseStart_940490 := by decide
  rcases family_descends (prefixWord ++ tailWord_940490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940570 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_940570 : Nat := 118140960795 + 940570 * 2 ^ 59
def prefixEnd_940570 : Nat := 4983230072969 + 3 ^ 40 * 940570 * 2
def baseEnd_940570 : Nat := 482964499199490249249403

theorem tailTrace_940570 : CollatzResearch.WordTrace tailWord_940570 prefixEnd_940570 482964499199490249249403 := by
  unfold tailWord_940570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576351550620750353044791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22870270801655334274786109 8576351550620750353044791)
  ·
    refine ⟨12864527325931125529567187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8576351550620750353044791 12864527325931125529567187)
    ·
      refine ⟨19296790988896688294350781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12864527325931125529567187 19296790988896688294350781)
      ·
        refine ⟨7236296620836258110381543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19296790988896688294350781 7236296620836258110381543)
        ·
          refine ⟨10854444931254387165572315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236296620836258110381543 10854444931254387165572315)
          ·
            refine ⟨16281667396881580748358473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10854444931254387165572315 16281667396881580748358473)
            ·
              refine ⟨12211250547661185561268855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16281667396881580748358473 12211250547661185561268855)
              ·
                refine ⟨18316875821491778341903283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12211250547661185561268855 18316875821491778341903283)
                ·
                  refine ⟨27475313732237667512854925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18316875821491778341903283 27475313732237667512854925)
                  ·
                    refine ⟨10303242649589125317320597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27475313732237667512854925 10303242649589125317320597)
                    ·
                      refine ⟨482964499199490249249403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10303242649589125317320597 482964499199490249249403)
                      ·
                        rfl

theorem cell23_940570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_940570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940570 prefixEnd_940570 := by exact prefixLift 940570
  have htrace : WordTrace (prefixWord ++ tailWord_940570) baseStart_940570 baseEnd_940570 := by
    simpa [prefixWord, tailWord_940570, baseEnd_940570] using wordTrace_append hprefix tailTrace_940570
  have hstable : (prefixWord ++ tailWord_940570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940570).length < 2 ^ (prefixWord ++ tailWord_940570).sum := by decide
  have hdescent : baseEnd_940570 < baseStart_940570 := by decide
  rcases family_descends (prefixWord ++ tailWord_940570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940597 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 6]
def baseStart_940597 : Nat := 118140960795 + 940597 * 2 ^ 59
def prefixEnd_940597 : Nat := 4983230072969 + 3 ^ 40 * 940597 * 2
def baseEnd_940597 : Nat := 53664262575240182623531

theorem tailTrace_940597 : CollatzResearch.WordTrace tailWord_940597 prefixEnd_940597 53664262575240182623531 := by
  unfold tailWord_940597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34306390973385185023412045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22870927315590123348941363 34306390973385185023412045)
  ·
    refine ⟨12864896615019444383779517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34306390973385185023412045 12864896615019444383779517)
    ·
      refine ⟨4824336230632291643917319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12864896615019444383779517 4824336230632291643917319)
      ·
        refine ⟨7236504345948437465875979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4824336230632291643917319 7236504345948437465875979)
        ·
          refine ⟨10854756518922656198813969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236504345948437465875979 10854756518922656198813969)
          ·
            refine ⟨8141067389191992149110477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10854756518922656198813969 8141067389191992149110477)
            ·
              refine ⟨3052900270946997055916429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8141067389191992149110477 3052900270946997055916429)
              ·
                refine ⟨1144837601605123895968661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3052900270946997055916429 1144837601605123895968661)
                ·
                  refine ⟨53664262575240182623531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1144837601605123895968661 53664262575240182623531)
                  ·
                    rfl

theorem cell23_940597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_940597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940597 prefixEnd_940597 := by exact prefixLift 940597
  have htrace : WordTrace (prefixWord ++ tailWord_940597) baseStart_940597 baseEnd_940597 := by
    simpa [prefixWord, tailWord_940597, baseEnd_940597] using wordTrace_append hprefix tailTrace_940597
  have hstable : (prefixWord ++ tailWord_940597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940597).length < 2 ^ (prefixWord ++ tailWord_940597).sum := by decide
  have hdescent : baseEnd_940597 < baseStart_940597 := by decide
  rcases family_descends (prefixWord ++ tailWord_940597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940657 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_940657 : Nat := 118140960795 + 940657 * 2 ^ 59
def prefixEnd_940657 : Nat := 4983230072969 + 3 ^ 40 * 940657 * 2
def baseEnd_940657 : Nat := 161003057338810469620501

theorem tailTrace_940657 : CollatzResearch.WordTrace tailWord_940657 prefixEnd_940657 161003057338810469620501 := by
  unfold tailWord_940657
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308579353167815270596225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22872386235445210180397483 34308579353167815270596225)
  ·
    refine ⟨25731434514875861452947169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34308579353167815270596225 25731434514875861452947169)
    ·
      refine ⟨19298575886156896089710377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25731434514875861452947169 19298575886156896089710377)
      ·
        refine ⟨14473931914617672067282783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19298575886156896089710377 14473931914617672067282783)
        ·
          refine ⟨21710897871926508100924175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14473931914617672067282783 21710897871926508100924175)
          ·
            refine ⟨32566346807889762151386263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21710897871926508100924175 32566346807889762151386263)
            ·
              refine ⟨48849520211834643227079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32566346807889762151386263 48849520211834643227079395)
              ·
                refine ⟨73274280317751964840619093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48849520211834643227079395 73274280317751964840619093)
                ·
                  refine ⟨858682972473655837976005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 73274280317751964840619093 858682972473655837976005)
                  ·
                    refine ⟨161003057338810469620501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 858682972473655837976005 161003057338810469620501)
                    ·
                      rfl

theorem cell23_940657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_940657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940657 prefixEnd_940657 := by exact prefixLift 940657
  have htrace : WordTrace (prefixWord ++ tailWord_940657) baseStart_940657 baseEnd_940657 := by
    simpa [prefixWord, tailWord_940657, baseEnd_940657] using wordTrace_append hprefix tailTrace_940657
  have hstable : (prefixWord ++ tailWord_940657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940657).length < 2 ^ (prefixWord ++ tailWord_940657).sum := by decide
  have hdescent : baseEnd_940657 < baseStart_940657 := by decide
  rcases family_descends (prefixWord ++ tailWord_940657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940711 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_940711 : Nat := 118140960795 + 940711 * 2 ^ 59
def prefixEnd_940711 : Nat := 4983230072969 + 3 ^ 40 * 940711 * 2
def baseEnd_940711 : Nat := 483036899971774197586255

theorem tailTrace_940711 : CollatzResearch.WordTrace tailWord_940711 prefixEnd_940711 483036899971774197586255 := by
  unfold tailWord_940711
  simp only [CollatzResearch.WordTrace]
  refine ⟨34310548894972182493061987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22873699263314788328707991 34310548894972182493061987)
  ·
    refine ⟨51465823342458273739592981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34310548894972182493061987 51465823342458273739592981)
    ·
      refine ⟨2412460469177731581543421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51465823342458273739592981 2412460469177731581543421)
      ·
        refine ⟨904672675941649343078783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2412460469177731581543421 904672675941649343078783)
        ·
          refine ⟨1357009013912474014618175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904672675941649343078783 1357009013912474014618175)
          ·
            refine ⟨2035513520868711021927263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357009013912474014618175 2035513520868711021927263)
            ·
              refine ⟨3053270281303066532890895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035513520868711021927263 3053270281303066532890895)
              ·
                refine ⟨4579905421954599799336343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053270281303066532890895 4579905421954599799336343)
                ·
                  refine ⟨6869858132931899699004515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579905421954599799336343 6869858132931899699004515)
                  ·
                    refine ⟨10304787199397849548506773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6869858132931899699004515 10304787199397849548506773)
                    ·
                      refine ⟨483036899971774197586255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10304787199397849548506773 483036899971774197586255)
                      ·
                        rfl

theorem cell23_940711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_940711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940711 prefixEnd_940711 := by exact prefixLift 940711
  have htrace : WordTrace (prefixWord ++ tailWord_940711) baseStart_940711 baseEnd_940711 := by
    simpa [prefixWord, tailWord_940711, baseEnd_940711] using wordTrace_append hprefix tailTrace_940711
  have hstable : (prefixWord ++ tailWord_940711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940711).length < 2 ^ (prefixWord ++ tailWord_940711).sum := by decide
  have hdescent : baseEnd_940711 < baseStart_940711 := by decide
  rcases family_descends (prefixWord ++ tailWord_940711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940718 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_940718 : Nat := 118140960795 + 940718 * 2 ^ 59
def prefixEnd_940718 : Nat := 4983230072969 + 3 ^ 40 * 940718 * 2
def baseEnd_940718 : Nat := 483040494336355670198723

theorem tailTrace_940718 : CollatzResearch.WordTrace tailWord_940718 prefixEnd_940718 483040494336355670198723 := by
  unfold tailWord_940718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288850525743352836070851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22873869470631215125711205 4288850525743352836070851)
  ·
    refine ⟨6433275788615029254106277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288850525743352836070851 6433275788615029254106277)
    ·
      refine ⟨1206239210365317985144927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6433275788615029254106277 1206239210365317985144927)
      ·
        refine ⟨1809358815547976977717391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206239210365317985144927 1809358815547976977717391)
        ·
          refine ⟨2714038223321965466576087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809358815547976977717391 2714038223321965466576087)
          ·
            refine ⟨4071057334982948199864131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714038223321965466576087 4071057334982948199864131)
            ·
              refine ⟨6106586002474422299796197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071057334982948199864131 6106586002474422299796197)
              ·
                refine ⟨1144984875463954181211787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6106586002474422299796197 1144984875463954181211787)
                ·
                  refine ⟨1717477313195931271817681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144984875463954181211787 1717477313195931271817681)
                  ·
                    refine ⟨1288107984896948453863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1717477313195931271817681 1288107984896948453863261)
                    ·
                      refine ⟨483040494336355670198723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288107984896948453863261 483040494336355670198723)
                      ·
                        rfl

theorem cell23_940718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_940718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940718 prefixEnd_940718 := by exact prefixLift 940718
  have htrace : WordTrace (prefixWord ++ tailWord_940718) baseStart_940718 baseEnd_940718 := by
    simpa [prefixWord, tailWord_940718, baseEnd_940718] using wordTrace_append hprefix tailTrace_940718
  have hstable : (prefixWord ++ tailWord_940718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940718).length < 2 ^ (prefixWord ++ tailWord_940718).sum := by decide
  have hdescent : baseEnd_940718 < baseStart_940718 := by decide
  rcases family_descends (prefixWord ++ tailWord_940718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940749 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_940749 : Nat := 118140960795 + 940749 * 2 ^ 59
def prefixEnd_940749 : Nat := 4983230072969 + 3 ^ 40 * 940749 * 2
def baseEnd_940749 : Nat := 483056412236645048911081

theorem tailTrace_940749 : CollatzResearch.WordTrace tailWord_940749 prefixEnd_940749 483056412236645048911081 := by
  unfold tailWord_940749
  simp only [CollatzResearch.WordTrace]
  refine ⟨34311934868834514982945301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22874623245889676655296867 34311934868834514982945301)
  ·
    refine ⟨1608371946976617889825561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34311934868834514982945301 1608371946976617889825561)
    ·
      refine ⟨1206278960232463417369171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1608371946976617889825561 1206278960232463417369171)
      ·
        refine ⟨1809418440348695126053757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206278960232463417369171 1809418440348695126053757)
        ·
          refine ⟨678531915130760672270159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1809418440348695126053757 678531915130760672270159)
          ·
            refine ⟨1017797872696141008405239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678531915130760672270159 1017797872696141008405239)
            ·
              refine ⟨1526696809044211512607859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017797872696141008405239 1526696809044211512607859)
              ·
                refine ⟨2290045213566317268911789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526696809044211512607859 2290045213566317268911789)
                ·
                  refine ⟨858766955087368975841921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2290045213566317268911789 858766955087368975841921)
                  ·
                    refine ⟨644075216315526731881441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 858766955087368975841921 644075216315526731881441)
                    ·
                      refine ⟨483056412236645048911081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644075216315526731881441 483056412236645048911081)
                      ·
                        rfl

theorem cell23_940749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_940749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940749 prefixEnd_940749 := by exact prefixLift 940749
  have htrace : WordTrace (prefixWord ++ tailWord_940749) baseStart_940749 baseEnd_940749 := by
    simpa [prefixWord, tailWord_940749, baseEnd_940749] using wordTrace_append hprefix tailTrace_940749
  have hstable : (prefixWord ++ tailWord_940749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940749).length < 2 ^ (prefixWord ++ tailWord_940749).sum := by decide
  have hdescent : baseEnd_940749 < baseStart_940749 := by decide
  rcases family_descends (prefixWord ++ tailWord_940749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940777 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 7]
def baseStart_940777 : Nat := 118140960795 + 940777 * 2 ^ 59
def prefixEnd_940777 : Nat := 4983230072969 + 3 ^ 40 * 940777 * 2
def baseEnd_940777 : Nat := 53674532188330104373439

theorem tailTrace_940777 : CollatzResearch.WordTrace tailWord_940777 prefixEnd_940777 53674532188330104373439 := by
  unfold tailWord_940777
  simp only [CollatzResearch.WordTrace]
  refine ⟨34312956112733075764964585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22875304075155383843309723 34312956112733075764964585)
  ·
    refine ⟨25734717084549806823723439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34312956112733075764964585 25734717084549806823723439)
    ·
      refine ⟨38602075626824710235585159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25734717084549806823723439 38602075626824710235585159)
      ·
        refine ⟨57903113440237065353377739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38602075626824710235585159 57903113440237065353377739)
        ·
          refine ⟨86854670160355598030066609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57903113440237065353377739 86854670160355598030066609)
          ·
            refine ⟨65141002620266698522549957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86854670160355598030066609 65141002620266698522549957)
            ·
              refine ⟨12213937991300005972978117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65141002620266698522549957 12213937991300005972978117)
              ·
                refine ⟨2290113373368751119933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12213937991300005972978117 2290113373368751119933397)
                ·
                  refine ⟨53674532188330104373439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2290113373368751119933397 53674532188330104373439)
                  ·
                    rfl

theorem cell23_940777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_940777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940777 prefixEnd_940777 := by exact prefixLift 940777
  have htrace : WordTrace (prefixWord ++ tailWord_940777) baseStart_940777 baseEnd_940777 := by
    simpa [prefixWord, tailWord_940777, baseEnd_940777] using wordTrace_append hprefix tailTrace_940777
  have hstable : (prefixWord ++ tailWord_940777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940777).length < 2 ^ (prefixWord ++ tailWord_940777).sum := by decide
  have hdescent : baseEnd_940777 < baseStart_940777 := by decide
  rcases family_descends (prefixWord ++ tailWord_940777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940818 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_940818 : Nat := 118140960795 + 940818 * 2 ^ 59
def prefixEnd_940818 : Nat := 4983230072969 + 3 ^ 40 * 940818 * 2
def baseEnd_940818 : Nat := 483091842401805278948263

theorem tailTrace_940818 : CollatzResearch.WordTrace tailWord_940818 prefixEnd_940818 483091842401805278948263 := by
  unfold tailWord_940818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578612876396134941801777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22876301003723026511471405 8578612876396134941801777)
  ·
    refine ⟨6433959657297101206351333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8578612876396134941801777 6433959657297101206351333)
    ·
      refine ⟨1206367435743206476190875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6433959657297101206351333 1206367435743206476190875)
      ·
        refine ⟨1809551153614809714286313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206367435743206476190875 1809551153614809714286313)
        ·
          refine ⟨1357163365211107285714735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1809551153614809714286313 1357163365211107285714735)
          ·
            refine ⟨2035745047816660928572103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357163365211107285714735 2035745047816660928572103)
            ·
              refine ⟨3053617571724991392858155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035745047816660928572103 3053617571724991392858155)
              ·
                refine ⟨4580426357587487089287233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053617571724991392858155 4580426357587487089287233)
                ·
                  refine ⟨3435319768190615316965425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580426357587487089287233 3435319768190615316965425)
                  ·
                    refine ⟨2576489826142961487724069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435319768190615316965425 2576489826142961487724069)
                    ·
                      refine ⟨483091842401805278948263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2576489826142961487724069 483091842401805278948263)
                      ·
                        rfl

theorem cell23_940818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_940818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940818 prefixEnd_940818 := by exact prefixLift 940818
  have htrace : WordTrace (prefixWord ++ tailWord_940818) baseStart_940818 baseEnd_940818 := by
    simpa [prefixWord, tailWord_940818, baseEnd_940818] using wordTrace_append hprefix tailTrace_940818
  have hstable : (prefixWord ++ tailWord_940818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940818).length < 2 ^ (prefixWord ++ tailWord_940818).sum := by decide
  have hdescent : baseEnd_940818 < baseStart_940818 := by decide
  rcases family_descends (prefixWord ++ tailWord_940818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940844 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_940844 : Nat := 118140960795 + 940844 * 2 ^ 59
def prefixEnd_940844 : Nat := 4983230072969 + 3 ^ 40 * 940844 * 2
def baseEnd_940844 : Nat := 483105192898822177223143

theorem tailTrace_940844 : CollatzResearch.WordTrace tailWord_940844 prefixEnd_940844 483105192898822177223143 := by
  unfold tailWord_940844
  simp only [CollatzResearch.WordTrace]
  refine ⟨17157699901745173103826793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22876933202326897471769057 17157699901745173103826793)
  ·
    refine ⟨12868274926308879827870095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17157699901745173103826793 12868274926308879827870095)
    ·
      refine ⟨19302412389463319741805143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12868274926308879827870095 19302412389463319741805143)
      ·
        refine ⟨28953618584194979612707715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302412389463319741805143 28953618584194979612707715)
        ·
          refine ⟨43430427876292469419061573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28953618584194979612707715 43430427876292469419061573)
          ·
            refine ⟨8143205226804838016074045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43430427876292469419061573 8143205226804838016074045)
            ·
              refine ⟨3053701960051814256027767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8143205226804838016074045 3053701960051814256027767)
              ·
                refine ⟨4580552940077721384041651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053701960051814256027767 4580552940077721384041651)
                ·
                  refine ⟨6870829410116582076062477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580552940077721384041651 6870829410116582076062477)
                  ·
                    refine ⟨2576561028793718278523429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6870829410116582076062477 2576561028793718278523429)
                    ·
                      refine ⟨483105192898822177223143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2576561028793718278523429 483105192898822177223143)
                      ·
                        rfl

theorem cell23_940844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_940844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940844 prefixEnd_940844 := by exact prefixLift 940844
  have htrace : WordTrace (prefixWord ++ tailWord_940844) baseStart_940844 baseEnd_940844 := by
    simpa [prefixWord, tailWord_940844, baseEnd_940844] using wordTrace_append hprefix tailTrace_940844
  have hstable : (prefixWord ++ tailWord_940844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940844).length < 2 ^ (prefixWord ++ tailWord_940844).sum := by decide
  have hdescent : baseEnd_940844 < baseStart_940844 := by decide
  rcases family_descends (prefixWord ++ tailWord_940844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940847 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_940847 : Nat := 118140960795 + 940847 * 2 ^ 59
def prefixEnd_940847 : Nat := 4983230072969 + 3 ^ 40 * 940847 * 2
def baseEnd_940847 : Nat := 483106733340785665485629

theorem tailTrace_940847 : CollatzResearch.WordTrace tailWord_940847 prefixEnd_940847 483106733340785665485629 := by
  unfold tailWord_940847
  simp only [CollatzResearch.WordTrace]
  refine ⟨34315509222479477720012795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22877006148319651813341863 34315509222479477720012795)
  ·
    refine ⟨51473263833719216580019193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34315509222479477720012795 51473263833719216580019193)
    ·
      refine ⟨38604947875289412435014395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51473263833719216580019193 38604947875289412435014395)
      ·
        refine ⟨57907421812934118652521593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38604947875289412435014395 57907421812934118652521593)
        ·
          refine ⟨43430566359700588989391195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57907421812934118652521593 43430566359700588989391195)
          ·
            refine ⟨65145849539550883484086793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43430566359700588989391195 65145849539550883484086793)
            ·
              refine ⟨48859387154663162613065095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65145849539550883484086793 48859387154663162613065095)
              ·
                refine ⟨73289080731994743919597643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48859387154663162613065095 73289080731994743919597643)
                ·
                  refine ⟨109933621097992115879396465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73289080731994743919597643 109933621097992115879396465)
                  ·
                    refine ⟨82450215823494086909547349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109933621097992115879396465 82450215823494086909547349)
                    ·
                      refine ⟨483106733340785665485629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 82450215823494086909547349 483106733340785665485629)
                      ·
                        rfl

theorem cell23_940847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_940847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940847 prefixEnd_940847 := by exact prefixLift 940847
  have htrace : WordTrace (prefixWord ++ tailWord_940847) baseStart_940847 baseEnd_940847 := by
    simpa [prefixWord, tailWord_940847, baseEnd_940847] using wordTrace_append hprefix tailTrace_940847
  have hstable : (prefixWord ++ tailWord_940847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940847).length < 2 ^ (prefixWord ++ tailWord_940847).sum := by decide
  have hdescent : baseEnd_940847 < baseStart_940847 := by decide
  rcases family_descends (prefixWord ++ tailWord_940847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940911 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 3]
def baseStart_940911 : Nat := 118140960795 + 940911 * 2 ^ 59
def prefixEnd_940911 : Nat := 4983230072969 + 3 ^ 40 * 940911 * 2
def baseEnd_940911 : Nat := 483139596102673415085335

theorem tailTrace_940911 : CollatzResearch.WordTrace tailWord_940911 prefixEnd_940911 483139596102673415085335 := by
  unfold tailWord_940911
  simp only [CollatzResearch.WordTrace]
  refine ⟨34317843494247616650342587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22878562329498411100228391 34317843494247616650342587)
  ·
    refine ⟨51476765241371424975513881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34317843494247616650342587 51476765241371424975513881)
    ·
      refine ⟨38607573931028568731635411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51476765241371424975513881 38607573931028568731635411)
      ·
        refine ⟨57911360896542853097453117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38607573931028568731635411 57911360896542853097453117)
        ·
          refine ⟨21716760336203569911544919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57911360896542853097453117 21716760336203569911544919)
          ·
            refine ⟨32575140504305354867317379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21716760336203569911544919 32575140504305354867317379)
            ·
              refine ⟨48862710756458032300976069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32575140504305354867317379 48862710756458032300976069)
              ·
                refine ⟨9161758266835881056433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48862710756458032300976069 9161758266835881056433013)
                ·
                  refine ⟨858914837515863849040595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9161758266835881056433013 858914837515863849040595)
                  ·
                    refine ⟨1288372256273795773560893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858914837515863849040595 1288372256273795773560893)
                    ·
                      refine ⟨483139596102673415085335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288372256273795773560893 483139596102673415085335)
                      ·
                        rfl

theorem cell23_940911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_940911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940911 prefixEnd_940911 := by exact prefixLift 940911
  have htrace : WordTrace (prefixWord ++ tailWord_940911) baseStart_940911 baseEnd_940911 := by
    simpa [prefixWord, tailWord_940911, baseEnd_940911] using wordTrace_append hprefix tailTrace_940911
  have hstable : (prefixWord ++ tailWord_940911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940911).length < 2 ^ (prefixWord ++ tailWord_940911).sum := by decide
  have hdescent : baseEnd_940911 < baseStart_940911 := by decide
  rcases family_descends (prefixWord ++ tailWord_940911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940951 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_940951 : Nat := 118140960795 + 940951 * 2 ^ 59
def prefixEnd_940951 : Nat := 4983230072969 + 3 ^ 40 * 940951 * 2
def baseEnd_940951 : Nat := 483160135328853258585151

theorem tailTrace_940951 : CollatzResearch.WordTrace tailWord_940951 prefixEnd_940951 483160135328853258585151 := by
  unfold tailWord_940951
  simp only [CollatzResearch.WordTrace]
  refine ⟨34319302414102703481798707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22879534942735135654532471 34319302414102703481798707)
  ·
    refine ⟨51478953621154055222698061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34319302414102703481798707 51478953621154055222698061)
    ·
      refine ⟨19304607607932770708511773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51478953621154055222698061 19304607607932770708511773)
      ·
        refine ⟨7239227852974789015691915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19304607607932770708511773 7239227852974789015691915)
        ·
          refine ⟨10858841779462183523537873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239227852974789015691915 10858841779462183523537873)
          ·
            refine ⟨8144131334596637642653405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858841779462183523537873 8144131334596637642653405)
            ·
              refine ⟨3054049250473739115995027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8144131334596637642653405 3054049250473739115995027)
              ·
                refine ⟨4581073875710608673992541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054049250473739115995027 4581073875710608673992541)
                ·
                  refine ⟨1717902703391478252747203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4581073875710608673992541 1717902703391478252747203)
                  ·
                    refine ⟨2576854055087217379120805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1717902703391478252747203 2576854055087217379120805)
                    ·
                      refine ⟨483160135328853258585151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2576854055087217379120805 483160135328853258585151)
                      ·
                        rfl

theorem cell23_940951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_940951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940951 prefixEnd_940951 := by exact prefixLift 940951
  have htrace : WordTrace (prefixWord ++ tailWord_940951) baseStart_940951 baseEnd_940951 := by
    simpa [prefixWord, tailWord_940951, baseEnd_940951] using wordTrace_append hprefix tailTrace_940951
  have hstable : (prefixWord ++ tailWord_940951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940951).length < 2 ^ (prefixWord ++ tailWord_940951).sum := by decide
  have hdescent : baseEnd_940951 < baseStart_940951 := by decide
  rcases family_descends (prefixWord ++ tailWord_940951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940961 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_940961 : Nat := 118140960795 + 940961 * 2 ^ 59
def prefixEnd_940961 : Nat := 4983230072969 + 3 ^ 40 * 940961 * 2
def baseEnd_940961 : Nat := 161055090045132739820035

theorem tailTrace_940961 : CollatzResearch.WordTrace tailWord_940961 prefixEnd_940961 161055090045132739820035 := by
  unfold tailWord_940961
  simp only [CollatzResearch.WordTrace]
  refine ⟨34319667144066475189662737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22879778096044316793108491 34319667144066475189662737)
  ·
    refine ⟨25739750358049856392247053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34319667144066475189662737 25739750358049856392247053)
    ·
      refine ⟨9652406384268696147092645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25739750358049856392247053 9652406384268696147092645)
      ·
        refine ⟨1809826197050380527579871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9652406384268696147092645 1809826197050380527579871)
        ·
          refine ⟨2714739295575570791369807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809826197050380527579871 2714739295575570791369807)
          ·
            refine ⟨4072108943363356187054711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714739295575570791369807 4072108943363356187054711)
            ·
              refine ⟨6108163415045034280582067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072108943363356187054711 6108163415045034280582067)
              ·
                refine ⟨9162245122567551420873101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108163415045034280582067 9162245122567551420873101)
                ·
                  refine ⟨3435841920962831782827413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9162245122567551420873101 3435841920962831782827413)
                  ·
                    refine ⟨161055090045132739820035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3435841920962831782827413 161055090045132739820035)
                    ·
                      rfl

theorem cell23_940961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_940961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940961 prefixEnd_940961 := by exact prefixLift 940961
  have htrace : WordTrace (prefixWord ++ tailWord_940961) baseStart_940961 baseEnd_940961 := by
    simpa [prefixWord, tailWord_940961, baseEnd_940961] using wordTrace_append hprefix tailTrace_940961
  have hstable : (prefixWord ++ tailWord_940961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940961).length < 2 ^ (prefixWord ++ tailWord_940961).sum := by decide
  have hdescent : baseEnd_940961 < baseStart_940961 := by decide
  rcases family_descends (prefixWord ++ tailWord_940961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940981 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_940981 : Nat := 118140960795 + 940981 * 2 ^ 59
def prefixEnd_940981 : Nat := 4983230072969 + 3 ^ 40 * 940981 * 2
def baseEnd_940981 : Nat := 483175539748488141210013

theorem tailTrace_940981 : CollatzResearch.WordTrace tailWord_940981 prefixEnd_940981 483175539748488141210013 := by
  unfold tailWord_940981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34320396603994018605390797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22880264402662679070260531 34320396603994018605390797)
  ·
    refine ⟨12870148726497756977021549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34320396603994018605390797 12870148726497756977021549)
    ·
      refine ⟨4826305772436658866383081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12870148726497756977021549 4826305772436658866383081)
      ·
        refine ⟨3619729329327494149787311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4826305772436658866383081 3619729329327494149787311)
        ·
          refine ⟨5429593993991241224680967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619729329327494149787311 5429593993991241224680967)
          ·
            refine ⟨8144390990986861837021451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429593993991241224680967 8144390990986861837021451)
            ·
              refine ⟨12216586486480292755532177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144390990986861837021451 12216586486480292755532177)
              ·
                refine ⟨9162439864860219566649133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12216586486480292755532177 9162439864860219566649133)
                ·
                  refine ⟨3435914949322582337493425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9162439864860219566649133 3435914949322582337493425)
                  ·
                    refine ⟨2576936211991936753120069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435914949322582337493425 2576936211991936753120069)
                    ·
                      refine ⟨483175539748488141210013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2576936211991936753120069 483175539748488141210013)
                      ·
                        rfl

theorem cell23_940981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_940981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940981 prefixEnd_940981 := by exact prefixLift 940981
  have htrace : WordTrace (prefixWord ++ tailWord_940981) baseStart_940981 baseEnd_940981 := by
    simpa [prefixWord, tailWord_940981, baseEnd_940981] using wordTrace_append hprefix tailTrace_940981
  have hstable : (prefixWord ++ tailWord_940981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940981).length < 2 ^ (prefixWord ++ tailWord_940981).sum := by decide
  have hdescent : baseEnd_940981 < baseStart_940981 := by decide
  rcases family_descends (prefixWord ++ tailWord_940981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941018 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_941018 : Nat := 118140960795 + 941018 * 2 ^ 59
def prefixEnd_941018 : Nat := 4983230072969 + 3 ^ 40 * 941018 * 2
def baseEnd_941018 : Nat := 483194538532704496447343

theorem tailTrace_941018 : CollatzResearch.WordTrace tailWord_941018 prefixEnd_941018 483194538532704496447343 := by
  unfold tailWord_941018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580436526214993481121927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22881164069906649282991805 8580436526214993481121927)
  ·
    refine ⟨12870654789322490221682891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8580436526214993481121927 12870654789322490221682891)
    ·
      refine ⟨19305982183983735332524337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12870654789322490221682891 19305982183983735332524337)
      ·
        refine ⟨14479486637987801499393253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19305982183983735332524337 14479486637987801499393253)
        ·
          refine ⟨2714903744622712781136235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14479486637987801499393253 2714903744622712781136235)
          ·
            refine ⟨4072355616934069171704353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714903744622712781136235 4072355616934069171704353)
            ·
              refine ⟨3054266712700551878778265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072355616934069171704353 3054266712700551878778265)
              ·
                refine ⟨2290700034525413909083699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054266712700551878778265 2290700034525413909083699)
                ·
                  refine ⟨3436050051788120863625549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290700034525413909083699 3436050051788120863625549)
                  ·
                    refine ⟨1288518769420545323859581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436050051788120863625549 1288518769420545323859581)
                    ·
                      refine ⟨483194538532704496447343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288518769420545323859581 483194538532704496447343)
                      ·
                        rfl

theorem cell23_941018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_941018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941018 prefixEnd_941018 := by exact prefixLift 941018
  have htrace : WordTrace (prefixWord ++ tailWord_941018) baseStart_941018 baseEnd_941018 := by
    simpa [prefixWord, tailWord_941018, baseEnd_941018] using wordTrace_append hprefix tailTrace_941018
  have hstable : (prefixWord ++ tailWord_941018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941018).length < 2 ^ (prefixWord ++ tailWord_941018).sum := by decide
  have hdescent : baseEnd_941018 < baseStart_941018 := by decide
  rcases family_descends (prefixWord ++ tailWord_941018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941028 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_941028 : Nat := 118140960795 + 941028 * 2 ^ 59
def prefixEnd_941028 : Nat := 4983230072969 + 3 ^ 40 * 941028 * 2
def baseEnd_941028 : Nat := 483199673339249457322297

theorem tailTrace_941028 : CollatzResearch.WordTrace tailWord_941028 prefixEnd_941028 483199673339249457322297 := by
  unfold tailWord_941028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161055417411872816175869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22881407223215830421567825 17161055417411872816175869)
  ·
    refine ⟨6435395781529452306065951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17161055417411872816175869 6435395781529452306065951)
    ·
      refine ⟨9653093672294178459098927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6435395781529452306065951 9653093672294178459098927)
      ·
        refine ⟨14479640508441267688648391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9653093672294178459098927 14479640508441267688648391)
        ·
          refine ⟨21719460762661901532972587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14479640508441267688648391 21719460762661901532972587)
          ·
            refine ⟨32579191143992852299458881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21719460762661901532972587 32579191143992852299458881)
            ·
              refine ⟨24434393357994639224594161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32579191143992852299458881 24434393357994639224594161)
              ·
                refine ⟨18325795018495979418445621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24434393357994639224594161 18325795018495979418445621)
                ·
                  refine ⟨1718043282983998070479277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18325795018495979418445621 1718043282983998070479277)
                  ·
                    refine ⟨644266231118999276429729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718043282983998070479277 644266231118999276429729)
                    ·
                      refine ⟨483199673339249457322297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644266231118999276429729 483199673339249457322297)
                      ·
                        rfl

theorem cell23_941028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_941028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941028 prefixEnd_941028 := by exact prefixLift 941028
  have htrace : WordTrace (prefixWord ++ tailWord_941028) baseStart_941028 baseEnd_941028 := by
    simpa [prefixWord, tailWord_941028, baseEnd_941028] using wordTrace_append hprefix tailTrace_941028
  have hstable : (prefixWord ++ tailWord_941028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941028).length < 2 ^ (prefixWord ++ tailWord_941028).sum := by decide
  have hdescent : baseEnd_941028 < baseStart_941028 := by decide
  rcases family_descends (prefixWord ++ tailWord_941028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941029 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_941029 : Nat := 118140960795 + 941029 * 2 ^ 59
def prefixEnd_941029 : Nat := 4983230072969 + 3 ^ 40 * 941029 * 2
def baseEnd_941029 : Nat := 161066728939967984469931

theorem tailTrace_941029 : CollatzResearch.WordTrace tailWord_941029 prefixEnd_941029 161066728939967984469931 := by
  unfold tailWord_941029
  simp only [CollatzResearch.WordTrace]
  refine ⟨34322147307820122803138141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22881431538546748535425427 34322147307820122803138141)
  ·
    refine ⟨12870805240432546051176803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34322147307820122803138141 12870805240432546051176803)
    ·
      refine ⟨19306207860648819076765205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12870805240432546051176803 19306207860648819076765205)
      ·
        refine ⟨904978493467913394223369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19306207860648819076765205 904978493467913394223369)
        ·
          refine ⟨678733870100935045667527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904978493467913394223369 678733870100935045667527)
          ·
            refine ⟨1018100805151402568501291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678733870100935045667527 1018100805151402568501291)
            ·
              refine ⟨1527151207727103852751937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018100805151402568501291 1527151207727103852751937)
              ·
                refine ⟨1145363405795327889563953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527151207727103852751937 1145363405795327889563953)
                ·
                  refine ⟨859022554346495917172965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145363405795327889563953 859022554346495917172965)
                  ·
                    refine ⟨161066728939967984469931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 859022554346495917172965 161066728939967984469931)
                    ·
                      rfl

theorem cell23_941029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_941029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941029 prefixEnd_941029 := by exact prefixLift 941029
  have htrace : WordTrace (prefixWord ++ tailWord_941029) baseStart_941029 baseEnd_941029 := by
    simpa [prefixWord, tailWord_941029, baseEnd_941029] using wordTrace_append hprefix tailTrace_941029
  have hstable : (prefixWord ++ tailWord_941029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941029).length < 2 ^ (prefixWord ++ tailWord_941029).sum := by decide
  have hdescent : baseEnd_941029 < baseStart_941029 := by decide
  rcases family_descends (prefixWord ++ tailWord_941029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941052 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_941052 : Nat := 118140960795 + 941052 * 2 ^ 59
def prefixEnd_941052 : Nat := 4983230072969 + 3 ^ 40 * 941052 * 2
def baseEnd_941052 : Nat := 483211996874957363422187

theorem tailTrace_941052 : CollatzResearch.WordTrace tailWord_941052 prefixEnd_941052 483211996874957363422187 := by
  unfold tailWord_941052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161493093368398865612705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22881990791157865154150273 17161493093368398865612705)
  ·
    refine ⟨12871119820026299149209529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17161493093368398865612705 12871119820026299149209529)
    ·
      refine ⟨9653339865019724361907147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12871119820026299149209529 9653339865019724361907147)
      ·
        refine ⟨14480009797529586542860721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9653339865019724361907147 14480009797529586542860721)
        ·
          refine ⟨10860007348147189907145541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14480009797529586542860721 10860007348147189907145541)
          ·
            refine ⟨2036251377777598107589789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10860007348147189907145541 2036251377777598107589789)
            ·
              refine ⟨763594266666599290346171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036251377777598107589789 763594266666599290346171)
              ·
                refine ⟨1145391399999898935519257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763594266666599290346171 1145391399999898935519257)
                ·
                  refine ⟨859043549999924201639443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145391399999898935519257 859043549999924201639443)
                  ·
                    refine ⟨1288565324999886302459165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 859043549999924201639443 1288565324999886302459165)
                    ·
                      refine ⟨483211996874957363422187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288565324999886302459165 483211996874957363422187)
                      ·
                        rfl

theorem cell23_941052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_941052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941052 prefixEnd_941052 := by exact prefixLift 941052
  have htrace : WordTrace (prefixWord ++ tailWord_941052) baseStart_941052 baseEnd_941052 := by
    simpa [prefixWord, tailWord_941052, baseEnd_941052] using wordTrace_append hprefix tailTrace_941052
  have hstable : (prefixWord ++ tailWord_941052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941052).length < 2 ^ (prefixWord ++ tailWord_941052).sum := by decide
  have hdescent : baseEnd_941052 < baseStart_941052 := by decide
  rcases family_descends (prefixWord ++ tailWord_941052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941061 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_941061 : Nat := 118140960795 + 941061 * 2 ^ 59
def prefixEnd_941061 : Nat := 4983230072969 + 3 ^ 40 * 941061 * 2
def baseEnd_941061 : Nat := 483216618200847828209645

theorem tailTrace_941061 : CollatzResearch.WordTrace tailWord_941061 prefixEnd_941061 483216618200847828209645 := by
  unfold tailWord_941061
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323314443704192268303037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22882209629136128178868691 34323314443704192268303037)
  ·
    refine ⟨12871242916389072100613639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34323314443704192268303037 12871242916389072100613639)
    ·
      refine ⟨19306864374583608150920459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12871242916389072100613639 19306864374583608150920459)
      ·
        refine ⟨28960296561875412226380689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19306864374583608150920459 28960296561875412226380689)
        ·
          refine ⟨21720222421406559169785517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28960296561875412226380689 21720222421406559169785517)
          ·
            refine ⟨8145083408027459688669569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21720222421406559169785517 8145083408027459688669569)
            ·
              refine ⟨6108812556020594766502177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145083408027459688669569 6108812556020594766502177)
              ·
                refine ⟨4581609417015446074876633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108812556020594766502177 4581609417015446074876633)
                ·
                  refine ⟨3436207062761584556157475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581609417015446074876633 3436207062761584556157475)
                  ·
                    refine ⟨5154310594142376834236213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3436207062761584556157475 5154310594142376834236213)
                    ·
                      refine ⟨483216618200847828209645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5154310594142376834236213 483216618200847828209645)
                      ·
                        rfl

theorem cell23_941061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_941061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941061 prefixEnd_941061 := by exact prefixLift 941061
  have htrace : WordTrace (prefixWord ++ tailWord_941061) baseStart_941061 baseEnd_941061 := by
    simpa [prefixWord, tailWord_941061, baseEnd_941061] using wordTrace_append hprefix tailTrace_941061
  have hstable : (prefixWord ++ tailWord_941061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941061).length < 2 ^ (prefixWord ++ tailWord_941061).sum := by decide
  have hdescent : baseEnd_941061 < baseStart_941061 := by decide
  rcases family_descends (prefixWord ++ tailWord_941061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941092 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_941092 : Nat := 118140960795 + 941092 * 2 ^ 59
def prefixEnd_941092 : Nat := 4983230072969 + 3 ^ 40 * 941092 * 2
def baseEnd_941092 : Nat := 483232536101137206922003

theorem tailTrace_941092 : CollatzResearch.WordTrace tailWord_941092 prefixEnd_941092 483232536101137206922003 := by
  unfold tailWord_941092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162222553295942281340765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22882963404394589708454353 17162222553295942281340765)
  ·
    refine ⟨6435833457485978355502787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17162222553295942281340765 6435833457485978355502787)
    ·
      refine ⟨9653750186228967533254181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6435833457485978355502787 9653750186228967533254181)
      ·
        refine ⟨1810078159917931412485159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9653750186228967533254181 1810078159917931412485159)
        ·
          refine ⟨2715117239876897118727739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810078159917931412485159 2715117239876897118727739)
          ·
            refine ⟨4072675859815345678091609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715117239876897118727739 4072675859815345678091609)
            ·
              refine ⟨3054506894861509258568707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072675859815345678091609 3054506894861509258568707)
              ·
                refine ⟨4581760342292263887853061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054506894861509258568707 4581760342292263887853061)
                ·
                  refine ⟨859080064179799478972449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4581760342292263887853061 859080064179799478972449)
                  ·
                    refine ⟨644310048134849609229337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 859080064179799478972449 644310048134849609229337)
                    ·
                      refine ⟨483232536101137206922003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644310048134849609229337 483232536101137206922003)
                      ·
                        rfl

theorem cell23_941092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_941092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941092 prefixEnd_941092 := by exact prefixLift 941092
  have htrace : WordTrace (prefixWord ++ tailWord_941092) baseStart_941092 baseEnd_941092 := by
    simpa [prefixWord, tailWord_941092, baseEnd_941092] using wordTrace_append hprefix tailTrace_941092
  have hstable : (prefixWord ++ tailWord_941092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941092).length < 2 ^ (prefixWord ++ tailWord_941092).sum := by decide
  have hdescent : baseEnd_941092 < baseStart_941092 := by decide
  rcases family_descends (prefixWord ++ tailWord_941092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941111 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 6, 5]
def baseStart_941111 : Nat := 118140960795 + 941111 * 2 ^ 59
def prefixEnd_941111 : Nat := 4983230072969 + 3 ^ 40 * 941111 * 2
def baseEnd_941111 : Nat := 161080764077857544194805

theorem tailTrace_941111 : CollatzResearch.WordTrace tailWord_941111 prefixEnd_941111 161080764077857544194805 := by
  unfold tailWord_941111
  simp only [CollatzResearch.WordTrace]
  refine ⟨34325138093523050807623187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22883425395682033871748791 34325138093523050807623187)
  ·
    refine ⟨51487707140284576211434781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34325138093523050807623187 51487707140284576211434781)
    ·
      refine ⟨19307890177606716079288043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51487707140284576211434781 19307890177606716079288043)
      ·
        refine ⟨28961835266410074118932065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19307890177606716079288043 28961835266410074118932065)
        ·
          refine ⟨21721376449807555589199049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28961835266410074118932065 21721376449807555589199049)
          ·
            refine ⟨16291032337355666691899287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21721376449807555589199049 16291032337355666691899287)
            ·
              refine ⟨24436548506033500037848931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16291032337355666691899287 24436548506033500037848931)
              ·
                refine ⟨36654822759050250056773397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24436548506033500037848931 36654822759050250056773397)
                ·
                  refine ⟨1718194816830480471411253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36654822759050250056773397 1718194816830480471411253)
                  ·
                    refine ⟨161080764077857544194805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1718194816830480471411253 161080764077857544194805)
                    ·
                      rfl

theorem cell23_941111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_941111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941111 prefixEnd_941111 := by exact prefixLift 941111
  have htrace : WordTrace (prefixWord ++ tailWord_941111) baseStart_941111 baseEnd_941111 := by
    simpa [prefixWord, tailWord_941111, baseEnd_941111] using wordTrace_append hprefix tailTrace_941111
  have hstable : (prefixWord ++ tailWord_941111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941111).length < 2 ^ (prefixWord ++ tailWord_941111).sum := by decide
  have hdescent : baseEnd_941111 < baseStart_941111 := by decide
  rcases family_descends (prefixWord ++ tailWord_941111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941128 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_941128 : Nat := 118140960795 + 941128 * 2 ^ 59
def prefixEnd_941128 : Nat := 4983230072969 + 3 ^ 40 * 941128 * 2
def baseEnd_941128 : Nat := 161083673801566355357279

theorem tailTrace_941128 : CollatzResearch.WordTrace tailWord_941128 prefixEnd_941128 161083673801566355357279 := by
  unfold tailWord_941128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162879067230731355496019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22883838756307641807328025 17162879067230731355496019)
  ·
    refine ⟨25744318600846097033244029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17162879067230731355496019 25744318600846097033244029)
    ·
      refine ⟨9654119475317286387466511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25744318600846097033244029 9654119475317286387466511)
      ·
        refine ⟨14481179212975929581199767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654119475317286387466511 14481179212975929581199767)
        ·
          refine ⟨21721768819463894371799651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481179212975929581199767 21721768819463894371799651)
          ·
            refine ⟨32582653229195841557699477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21721768819463894371799651 32582653229195841557699477)
            ·
              refine ⟨1527311870118555073017163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32582653229195841557699477 1527311870118555073017163)
              ·
                refine ⟨2290967805177832609525745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527311870118555073017163 2290967805177832609525745)
                ·
                  refine ⟨1718225853883374457144309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2290967805177832609525745 1718225853883374457144309)
                  ·
                    refine ⟨161083673801566355357279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1718225853883374457144309 161083673801566355357279)
                    ·
                      rfl

theorem cell23_941128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_941128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941128 prefixEnd_941128 := by exact prefixLift 941128
  have htrace : WordTrace (prefixWord ++ tailWord_941128) baseStart_941128 baseEnd_941128 := by
    simpa [prefixWord, tailWord_941128, baseEnd_941128] using wordTrace_append hprefix tailTrace_941128
  have hstable : (prefixWord ++ tailWord_941128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941128).length < 2 ^ (prefixWord ++ tailWord_941128).sum := by decide
  have hdescent : baseEnd_941128 < baseStart_941128 := by decide
  rcases family_descends (prefixWord ++ tailWord_941128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941138 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_941138 : Nat := 118140960795 + 941138 * 2 ^ 59
def prefixEnd_941138 : Nat := 4983230072969 + 3 ^ 40 * 941138 * 2
def baseEnd_941138 : Nat := 483256156211244026946791

theorem tailTrace_941138 : CollatzResearch.WordTrace tailWord_941138 prefixEnd_941138 483256156211244026946791 := by
  unfold tailWord_941138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581530716106308604714017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22884081909616822945904045 8581530716106308604714017)
  ·
    refine ⟨6436148037079731453535513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8581530716106308604714017 6436148037079731453535513)
    ·
      refine ⟨4827111027809798590151635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6436148037079731453535513 4827111027809798590151635)
      ·
        refine ⟨7240666541714697885227453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827111027809798590151635 7240666541714697885227453)
        ·
          refine ⟨2715249953143011706960295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7240666541714697885227453 2715249953143011706960295)
          ·
            refine ⟨4072874929714517560440443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715249953143011706960295 4072874929714517560440443)
            ·
              refine ⟨6109312394571776340660665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072874929714517560440443 6109312394571776340660665)
              ·
                refine ⟨4581984295928832255495499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109312394571776340660665 4581984295928832255495499)
                ·
                  refine ⟨6872976443893248383243249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581984295928832255495499 6872976443893248383243249)
                  ·
                    refine ⟨5154732332919936287432437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872976443893248383243249 5154732332919936287432437)
                    ·
                      refine ⟨483256156211244026946791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5154732332919936287432437 483256156211244026946791)
                      ·
                        rfl

theorem cell23_941138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_941138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941138 prefixEnd_941138 := by exact prefixLift 941138
  have htrace : WordTrace (prefixWord ++ tailWord_941138) baseStart_941138 baseEnd_941138 := by
    simpa [prefixWord, tailWord_941138, baseEnd_941138] using wordTrace_append hprefix tailTrace_941138
  have hstable : (prefixWord ++ tailWord_941138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941138).length < 2 ^ (prefixWord ++ tailWord_941138).sum := by decide
  have hdescent : baseEnd_941138 < baseStart_941138 := by decide
  rcases family_descends (prefixWord ++ tailWord_941138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941151 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_941151 : Nat := 118140960795 + 941151 * 2 ^ 59
def prefixEnd_941151 : Nat := 4983230072969 + 3 ^ 40 * 941151 * 2
def baseEnd_941151 : Nat := 483262831459752476084231

theorem tailTrace_941151 : CollatzResearch.WordTrace tailWord_941151 prefixEnd_941151 483262831459752476084231 := by
  unfold tailWord_941151
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326597013378137639079307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22884398008918758426052871 34326597013378137639079307)
  ·
    refine ⟨51489895520067206458618961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34326597013378137639079307 51489895520067206458618961)
    ·
      refine ⟨38617421640050404843964221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51489895520067206458618961 38617421640050404843964221)
      ·
        refine ⟨14481533115018901816486583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38617421640050404843964221 14481533115018901816486583)
        ·
          refine ⟨21722299672528352724729875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481533115018901816486583 21722299672528352724729875)
          ·
            refine ⟨32583449508792529087094813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722299672528352724729875 32583449508792529087094813)
            ·
              refine ⟨12218793565797198407660555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32583449508792529087094813 12218793565797198407660555)
              ·
                refine ⟨18328190348695797611490833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12218793565797198407660555 18328190348695797611490833)
                ·
                  refine ⟨13746142761521848208618125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18328190348695797611490833 13746142761521848208618125)
                  ·
                    refine ⟨5154803535570693078231797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13746142761521848208618125 5154803535570693078231797)
                    ·
                      refine ⟨483262831459752476084231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5154803535570693078231797 483262831459752476084231)
                      ·
                        rfl

theorem cell23_941151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_941151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941151 prefixEnd_941151 := by exact prefixLift 941151
  have htrace : WordTrace (prefixWord ++ tailWord_941151) baseStart_941151 baseEnd_941151 := by
    simpa [prefixWord, tailWord_941151, baseEnd_941151] using wordTrace_append hprefix tailTrace_941151
  have hstable : (prefixWord ++ tailWord_941151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941151).length < 2 ^ (prefixWord ++ tailWord_941151).sum := by decide
  have hdescent : baseEnd_941151 < baseStart_941151 := by decide
  rcases family_descends (prefixWord ++ tailWord_941151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941165 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_941165 : Nat := 118140960795 + 941165 * 2 ^ 59
def prefixEnd_941165 : Nat := 4983230072969 + 3 ^ 40 * 941165 * 2
def baseEnd_941165 : Nat := 483270020188915421309167

theorem tailTrace_941165 : CollatzResearch.WordTrace tailWord_941165 prefixEnd_941165 483270020188915421309167 := by
  unfold tailWord_941165
  simp only [CollatzResearch.WordTrace]
  refine ⟨34327107635327418030088949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22884738423551612020059299 34327107635327418030088949)
  ·
    refine ⟨3218166340811945440320839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34327107635327418030088949 3218166340811945440320839)
    ·
      refine ⟨4827249511217918160481259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218166340811945440320839 4827249511217918160481259)
      ·
        refine ⟨7240874266826877240721889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827249511217918160481259 7240874266826877240721889)
        ·
          refine ⟨5430655700120157930541417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7240874266826877240721889 5430655700120157930541417)
          ·
            refine ⟨4072991775090118447906063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430655700120157930541417 4072991775090118447906063)
            ·
              refine ⟨6109487662635177671859095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072991775090118447906063 6109487662635177671859095)
              ·
                refine ⟨9164231493952766507788643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109487662635177671859095 9164231493952766507788643)
                ·
                  refine ⟨13746347240929149761682965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164231493952766507788643 13746347240929149761682965)
                  ·
                    refine ⟨644360026918553895078889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13746347240929149761682965 644360026918553895078889)
                    ·
                      refine ⟨483270020188915421309167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644360026918553895078889 483270020188915421309167)
                      ·
                        rfl

theorem cell23_941165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_941165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941165 prefixEnd_941165 := by exact prefixLift 941165
  have htrace : WordTrace (prefixWord ++ tailWord_941165) baseStart_941165 baseEnd_941165 := by
    simpa [prefixWord, tailWord_941165, baseEnd_941165] using wordTrace_append hprefix tailTrace_941165
  have hstable : (prefixWord ++ tailWord_941165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941165).length < 2 ^ (prefixWord ++ tailWord_941165).sum := by decide
  have hdescent : baseEnd_941165 < baseStart_941165 := by decide
  rcases family_descends (prefixWord ++ tailWord_941165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941168 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_941168 : Nat := 118140960795 + 941168 * 2 ^ 59
def prefixEnd_941168 : Nat := 4983230072969 + 3 ^ 40 * 941168 * 2
def baseEnd_941168 : Nat := 483271560630878909571653

theorem tailTrace_941168 : CollatzResearch.WordTrace tailWord_941168 prefixEnd_941168 483271560630878909571653 := by
  unfold tailWord_941168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163608527158274771224079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22884811369544366361632105 17163608527158274771224079)
  ·
    refine ⟨25745412790737412156836119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17163608527158274771224079 25745412790737412156836119)
    ·
      refine ⟨38618119186106118235254179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25745412790737412156836119 38618119186106118235254179)
      ·
        refine ⟨57927178779159177352881269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38618119186106118235254179 57927178779159177352881269)
        ·
          refine ⟨5430673010546172876832619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57927178779159177352881269 5430673010546172876832619)
          ·
            refine ⟨8146009515819259315248929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430673010546172876832619 8146009515819259315248929)
            ·
              refine ⟨6109507136864444486436697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8146009515819259315248929 6109507136864444486436697)
              ·
                refine ⟨4582130352648333364827523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109507136864444486436697 4582130352648333364827523)
                ·
                  refine ⟨6873195528972500047241285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582130352648333364827523 6873195528972500047241285)
                  ·
                    refine ⟨1288724161682343758857741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873195528972500047241285 1288724161682343758857741)
                    ·
                      refine ⟨483271560630878909571653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288724161682343758857741 483271560630878909571653)
                      ·
                        rfl

theorem cell23_941168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_941168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941168 prefixEnd_941168 := by exact prefixLift 941168
  have htrace : WordTrace (prefixWord ++ tailWord_941168) baseStart_941168 baseEnd_941168 := by
    simpa [prefixWord, tailWord_941168, baseEnd_941168] using wordTrace_append hprefix tailTrace_941168
  have hstable : (prefixWord ++ tailWord_941168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941168).length < 2 ^ (prefixWord ++ tailWord_941168).sum := by decide
  have hdescent : baseEnd_941168 < baseStart_941168 := by decide
  rcases family_descends (prefixWord ++ tailWord_941168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941185 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_941185 : Nat := 118140960795 + 941185 * 2 ^ 59
def prefixEnd_941185 : Nat := 4983230072969 + 3 ^ 40 * 941185 * 2
def baseEnd_941185 : Nat := 483280289802005343059075

theorem tailTrace_941185 : CollatzResearch.WordTrace tailWord_941185 prefixEnd_941185 483280289802005343059075 := by
  unfold tailWord_941185
  simp only [CollatzResearch.WordTrace]
  refine ⟨34327837095254961445817009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22885224730169974297211339 34327837095254961445817009)
  ·
    refine ⟨25745877821441221084362757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34327837095254961445817009 25745877821441221084362757)
    ·
      refine ⟨4827352091520228953318017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25745877821441221084362757 4827352091520228953318017)
      ·
        refine ⟨3620514068640171714988513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827352091520228953318017 3620514068640171714988513)
        ·
          refine ⟨2715385551480128786241385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620514068640171714988513 2715385551480128786241385)
          ·
            refine ⟨2036539163610096589681039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715385551480128786241385 2036539163610096589681039)
            ·
              refine ⟨3054808745415144884521559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036539163610096589681039 3054808745415144884521559)
              ·
                refine ⟨4582213118122717326782339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054808745415144884521559 4582213118122717326782339)
                ·
                  refine ⟨6873319677184075990173509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582213118122717326782339 6873319677184075990173509)
                  ·
                    refine ⟨1288747439472014248157533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873319677184075990173509 1288747439472014248157533)
                    ·
                      refine ⟨483280289802005343059075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288747439472014248157533 483280289802005343059075)
                      ·
                        rfl

theorem cell23_941185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_941185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941185 prefixEnd_941185 := by exact prefixLift 941185
  have htrace : WordTrace (prefixWord ++ tailWord_941185) baseStart_941185 baseEnd_941185 := by
    simpa [prefixWord, tailWord_941185, baseEnd_941185] using wordTrace_append hprefix tailTrace_941185
  have hstable : (prefixWord ++ tailWord_941185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941185).length < 2 ^ (prefixWord ++ tailWord_941185).sum := by decide
  have hdescent : baseEnd_941185 < baseStart_941185 := by decide
  rcases family_descends (prefixWord ++ tailWord_941185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941208 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_941208 : Nat := 118140960795 + 941208 * 2 ^ 59
def prefixEnd_941208 : Nat := 4983230072969 + 3 ^ 40 * 941208 * 2
def baseEnd_941208 : Nat := 483292099857058753071469

theorem tailTrace_941208 : CollatzResearch.WordTrace tailWord_941208 prefixEnd_941208 483292099857058753071469 := by
  unfold tailWord_941208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164337987085818186952139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22885783982781090915936185 17164337987085818186952139)
  ·
    refine ⟨25746506980628727280428209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17164337987085818186952139 25746506980628727280428209)
    ·
      refine ⟨19309880235471545460321157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25746506980628727280428209 19309880235471545460321157)
      ·
        refine ⟨3620602544150914773810217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19309880235471545460321157 3620602544150914773810217)
        ·
          refine ⟨2715451908113186080357663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620602544150914773810217 2715451908113186080357663)
          ·
            refine ⟨4073177862169779120536495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715451908113186080357663 4073177862169779120536495)
            ·
              refine ⟨6109766793254668680804743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073177862169779120536495 6109766793254668680804743)
              ·
                refine ⟨9164650189882003021207115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109766793254668680804743 9164650189882003021207115)
                ·
                  refine ⟨13746975284823004531810673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164650189882003021207115 13746975284823004531810673)
                  ·
                    refine ⟨10310231463617253398858005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746975284823004531810673 10310231463617253398858005)
                    ·
                      refine ⟨483292099857058753071469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10310231463617253398858005 483292099857058753071469)
                      ·
                        rfl

theorem cell23_941208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_941208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941208 prefixEnd_941208 := by exact prefixLift 941208
  have htrace : WordTrace (prefixWord ++ tailWord_941208) baseStart_941208 baseEnd_941208 := by
    simpa [prefixWord, tailWord_941208, baseEnd_941208] using wordTrace_append hprefix tailTrace_941208
  have hstable : (prefixWord ++ tailWord_941208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941208).length < 2 ^ (prefixWord ++ tailWord_941208).sum := by decide
  have hdescent : baseEnd_941208 < baseStart_941208 := by decide
  rcases family_descends (prefixWord ++ tailWord_941208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941211 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_941211 : Nat := 118140960795 + 941211 * 2 ^ 59
def prefixEnd_941211 : Nat := 4983230072969 + 3 ^ 40 * 941211 * 2
def baseEnd_941211 : Nat := 483293640299022241333955

theorem tailTrace_941211 : CollatzResearch.WordTrace tailWord_941211 prefixEnd_941211 483293640299022241333955 := by
  unfold tailWord_941211
  simp only [CollatzResearch.WordTrace]
  refine ⟨34328785393160767886263487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22885856928773845257508991 34328785393160767886263487)
  ·
    refine ⟨51493178089741151829395231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34328785393160767886263487 51493178089741151829395231)
    ·
      refine ⟨77239767134611727744092847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51493178089741151829395231 77239767134611727744092847)
      ·
        refine ⟨115859650701917591616139271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77239767134611727744092847 115859650701917591616139271)
        ·
          refine ⟨173789476052876387424208907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115859650701917591616139271 173789476052876387424208907)
          ·
            refine ⟨260684214079314581136313361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173789476052876387424208907 260684214079314581136313361)
            ·
              refine ⟨195513160559485935852235021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260684214079314581136313361 195513160559485935852235021)
              ·
                refine ⟨73317435209807225944588133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195513160559485935852235021 73317435209807225944588133)
                ·
                  refine ⟨13747019101838854864610275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73317435209807225944588133 13747019101838854864610275)
                  ·
                    refine ⟨20620528652758282296915413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13747019101838854864610275 20620528652758282296915413)
                    ·
                      refine ⟨483293640299022241333955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20620528652758282296915413 483293640299022241333955)
                      ·
                        rfl

theorem cell23_941211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_941211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941211 prefixEnd_941211 := by exact prefixLift 941211
  have htrace : WordTrace (prefixWord ++ tailWord_941211) baseStart_941211 baseEnd_941211 := by
    simpa [prefixWord, tailWord_941211, baseEnd_941211] using wordTrace_append hprefix tailTrace_941211
  have hstable : (prefixWord ++ tailWord_941211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941211).length < 2 ^ (prefixWord ++ tailWord_941211).sum := by decide
  have hdescent : baseEnd_941211 < baseStart_941211 := by decide
  rcases family_descends (prefixWord ++ tailWord_941211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941265 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_941265 : Nat := 118140960795 + 941265 * 2 ^ 59
def prefixEnd_941265 : Nat := 4983230072969 + 3 ^ 40 * 941265 * 2
def baseEnd_941265 : Nat := 161107122751455010019569

theorem tailTrace_941265 : CollatzResearch.WordTrace tailWord_941265 prefixEnd_941265 161107122751455010019569 := by
  unfold tailWord_941265
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330754934965135108729249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22887169956643423405819499 34330754934965135108729249)
  ·
    refine ⟨25748066201223851331546937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34330754934965135108729249 25748066201223851331546937)
    ·
      refine ⟨19311049650917888498660203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25748066201223851331546937 19311049650917888498660203)
      ·
        refine ⟨28966574476376832747990305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19311049650917888498660203 28966574476376832747990305)
        ·
          refine ⟨21724930857282624560992729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28966574476376832747990305 21724930857282624560992729)
          ·
            refine ⟨16293698142961968420744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21724930857282624560992729 16293698142961968420744547)
            ·
              refine ⟨24440547214442952631116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293698142961968420744547 24440547214442952631116821)
              ·
                refine ⟨1145650650677013404583601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24440547214442952631116821 1145650650677013404583601)
                ·
                  refine ⟨859237988007760053437701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145650650677013404583601 859237988007760053437701)
                  ·
                    refine ⟨161107122751455010019569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 859237988007760053437701 161107122751455010019569)
                    ·
                      rfl

theorem cell23_941265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_941265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941265 prefixEnd_941265 := by exact prefixLift 941265
  have htrace : WordTrace (prefixWord ++ tailWord_941265) baseStart_941265 baseEnd_941265 := by
    simpa [prefixWord, tailWord_941265, baseEnd_941265] using wordTrace_append hprefix tailTrace_941265
  have hstable : (prefixWord ++ tailWord_941265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941265).length < 2 ^ (prefixWord ++ tailWord_941265).sum := by decide
  have hdescent : baseEnd_941265 < baseStart_941265 := by decide
  rcases family_descends (prefixWord ++ tailWord_941265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941266 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_941266 : Nat := 118140960795 + 941266 * 2 ^ 59
def prefixEnd_941266 : Nat := 4983230072969 + 3 ^ 40 * 941266 * 2
def baseEnd_941266 : Nat := 483321881735019526146203

theorem tailTrace_941266 : CollatzResearch.WordTrace tailWord_941266 prefixEnd_941266 483321881735019526146203 := by
  unfold tailWord_941266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582697851990378069878913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22887194271974341519677101 8582697851990378069878913)
  ·
    refine ⟨6437023388992783552409185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8582697851990378069878913 6437023388992783552409185)
    ·
      refine ⟨4827767541744587664306889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6437023388992783552409185 4827767541744587664306889)
      ·
        refine ⟨3620825656308440748230167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827767541744587664306889 3620825656308440748230167)
        ·
          refine ⟨5431238484462661122345251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620825656308440748230167 5431238484462661122345251)
          ·
            refine ⟨8146857726693991683517877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431238484462661122345251 8146857726693991683517877)
            ·
              refine ⟨763767911877561720329801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8146857726693991683517877 763767911877561720329801)
              ·
                refine ⟨572825933908171290247351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763767911877561720329801 572825933908171290247351)
                ·
                  refine ⟨859238900862256935371027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572825933908171290247351 859238900862256935371027)
                  ·
                    refine ⟨1288858351293385403056541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 859238900862256935371027 1288858351293385403056541)
                    ·
                      refine ⟨483321881735019526146203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288858351293385403056541 483321881735019526146203)
                      ·
                        rfl

theorem cell23_941266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_941266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941266 prefixEnd_941266 := by exact prefixLift 941266
  have htrace : WordTrace (prefixWord ++ tailWord_941266) baseStart_941266 baseEnd_941266 := by
    simpa [prefixWord, tailWord_941266, baseEnd_941266] using wordTrace_append hprefix tailTrace_941266
  have hstable : (prefixWord ++ tailWord_941266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941266).length < 2 ^ (prefixWord ++ tailWord_941266).sum := by decide
  have hdescent : baseEnd_941266 < baseStart_941266 := by decide
  rcases family_descends (prefixWord ++ tailWord_941266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941292 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_941292 : Nat := 118140960795 + 941292 * 2 ^ 59
def prefixEnd_941292 : Nat := 4983230072969 + 3 ^ 40 * 941292 * 2
def baseEnd_941292 : Nat := 483335232232036424421083

theorem tailTrace_941292 : CollatzResearch.WordTrace tailWord_941292 prefixEnd_941292 483335232232036424421083 := by
  unfold tailWord_941292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17165869852933659359981065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22887826470578212479974753 17165869852933659359981065)
  ·
    refine ⟨12874402389700244519985799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17165869852933659359981065 12874402389700244519985799)
    ·
      refine ⟨19311603584550366779978699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12874402389700244519985799 19311603584550366779978699)
      ·
        refine ⟨28967405376825550169968049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19311603584550366779978699 28967405376825550169968049)
        ·
          refine ⟨21725554032619162627476037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28967405376825550169968049 21725554032619162627476037)
          ·
            refine ⟨4073541381116092992651757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21725554032619162627476037 4073541381116092992651757)
            ·
              refine ⟨1527578017918534872244409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4073541381116092992651757 1527578017918534872244409)
              ·
                refine ⟨1145683513438901154183307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527578017918534872244409 1145683513438901154183307)
                ·
                  refine ⟨1718525270158351731274961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145683513438901154183307 1718525270158351731274961)
                  ·
                    refine ⟨1288893952618763798456221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1718525270158351731274961 1288893952618763798456221)
                    ·
                      refine ⟨483335232232036424421083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288893952618763798456221 483335232232036424421083)
                      ·
                        rfl

theorem cell23_941292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_941292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941292 prefixEnd_941292 := by exact prefixLift 941292
  have htrace : WordTrace (prefixWord ++ tailWord_941292) baseStart_941292 baseEnd_941292 := by
    simpa [prefixWord, tailWord_941292, baseEnd_941292] using wordTrace_append hprefix tailTrace_941292
  have hstable : (prefixWord ++ tailWord_941292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941292).length < 2 ^ (prefixWord ++ tailWord_941292).sum := by decide
  have hdescent : baseEnd_941292 < baseStart_941292 := by decide
  rcases family_descends (prefixWord ++ tailWord_941292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941305 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_941305 : Nat := 118140960795 + 941305 * 2 ^ 59
def prefixEnd_941305 : Nat := 4983230072969 + 3 ^ 40 * 941305 * 2
def baseEnd_941305 : Nat := 483341907480544873558523

theorem tailTrace_941305 : CollatzResearch.WordTrace tailWord_941305 prefixEnd_941305 483341907480544873558523 := by
  unfold tailWord_941305
  simp only [CollatzResearch.WordTrace]
  refine ⟨34332213854820221940185369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22888142569880147960123579 34332213854820221940185369)
  ·
    refine ⟨25749160391115166455139027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34332213854820221940185369 25749160391115166455139027)
    ·
      refine ⟨38623740586672749682708541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25749160391115166455139027 38623740586672749682708541)
      ·
        refine ⟨14483902720002281131015703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38623740586672749682708541 14483902720002281131015703)
        ·
          refine ⟨21725854080003421696523555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14483902720002281131015703 21725854080003421696523555)
          ·
            refine ⟨32588781120005132544785333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21725854080003421696523555 32588781120005132544785333)
            ·
              refine ⟨3055198230000481176073625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32588781120005132544785333 3055198230000481176073625)
              ·
                refine ⟨2291398672500360882055219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055198230000481176073625 2291398672500360882055219)
                ·
                  refine ⟨3437098008750541323082829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291398672500360882055219 3437098008750541323082829)
                  ·
                    refine ⟨1288911753281452996156061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437098008750541323082829 1288911753281452996156061)
                    ·
                      refine ⟨483341907480544873558523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1288911753281452996156061 483341907480544873558523)
                      ·
                        rfl

theorem cell23_941305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_941305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941305 prefixEnd_941305 := by exact prefixLift 941305
  have htrace : WordTrace (prefixWord ++ tailWord_941305) baseStart_941305 baseEnd_941305 := by
    simpa [prefixWord, tailWord_941305, baseEnd_941305] using wordTrace_append hprefix tailTrace_941305
  have hstable : (prefixWord ++ tailWord_941305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941305).length < 2 ^ (prefixWord ++ tailWord_941305).sum := by decide
  have hdescent : baseEnd_941305 < baseStart_941305 := by decide
  rcases family_descends (prefixWord ++ tailWord_941305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941323 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 1, 2, 2]
def baseStart_941323 : Nat := 118140960795 + 941323 * 2 ^ 59
def prefixEnd_941323 : Nat := 4983230072969 + 3 ^ 40 * 941323 * 2
def baseEnd_941323 : Nat := 483351150132325803133441

theorem tailTrace_941323 : CollatzResearch.WordTrace tailWord_941323 prefixEnd_941323 483351150132325803133441 := by
  unfold tailWord_941323
  simp only [CollatzResearch.WordTrace]
  refine ⟨34332870368755011014340623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22888580245836674009560415 34332870368755011014340623)
  ·
    refine ⟨51499305553132516521510935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34332870368755011014340623 51499305553132516521510935)
    ·
      refine ⟨77248958329698774782266403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51499305553132516521510935 77248958329698774782266403)
      ·
        refine ⟨115873437494548162173399605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77248958329698774782266403 115873437494548162173399605)
        ·
          refine ⟨10863134765113890203756213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115873437494548162173399605 10863134765113890203756213)
          ·
            refine ⟨1018418884229427206602145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10863134765113890203756213 1018418884229427206602145)
            ·
              refine ⟨763814163172070404951609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018418884229427206602145 763814163172070404951609)
              ·
                refine ⟨572860622379052803713707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763814163172070404951609 572860622379052803713707)
                ·
                  refine ⟨859290933568579205570561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572860622379052803713707 859290933568579205570561)
                  ·
                    refine ⟨644468200176434404177921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 859290933568579205570561 644468200176434404177921)
                    ·
                      refine ⟨483351150132325803133441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644468200176434404177921 483351150132325803133441)
                      ·
                        rfl

theorem cell23_941323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 2, 2].length) (baseStart_941323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941323 prefixEnd_941323 := by exact prefixLift 941323
  have htrace : WordTrace (prefixWord ++ tailWord_941323) baseStart_941323 baseEnd_941323 := by
    simpa [prefixWord, tailWord_941323, baseEnd_941323] using wordTrace_append hprefix tailTrace_941323
  have hstable : (prefixWord ++ tailWord_941323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941323).length < 2 ^ (prefixWord ++ tailWord_941323).sum := by decide
  have hdescent : baseEnd_941323 < baseStart_941323 := by decide
  rcases family_descends (prefixWord ++ tailWord_941323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941368 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 11]
def baseStart_941368 : Nat := 118140960795 + 941368 * 2 ^ 59
def prefixEnd_941368 : Nat := 4983230072969 + 3 ^ 40 * 941368 * 2
def baseEnd_941368 : Nat := 53708250751308680785637

theorem tailTrace_941368 : CollatzResearch.WordTrace tailWord_941368 prefixEnd_941368 53708250751308680785637 := by
  unfold tailWord_941368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17167255826795991849864379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22889674435727989133152505 17167255826795991849864379)
  ·
    refine ⟨25750883740193987774796569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17167255826795991849864379 25750883740193987774796569)
    ·
      refine ⟨19313162805145490831097427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25750883740193987774796569 19313162805145490831097427)
      ·
        refine ⟨28969744207718236246646141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19313162805145490831097427 28969744207718236246646141)
        ·
          refine ⟨10863654077894338592492303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28969744207718236246646141 10863654077894338592492303)
          ·
            refine ⟨16295481116841507888738455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863654077894338592492303 16295481116841507888738455)
            ·
              refine ⟨24443221675262261833107683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295481116841507888738455 24443221675262261833107683)
              ·
                refine ⟨36664832512893392749661525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24443221675262261833107683 36664832512893392749661525)
                ·
                  refine ⟨53708250751308680785637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 36664832512893392749661525 53708250751308680785637)
                  ·
                    rfl

theorem cell23_941368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_941368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941368 prefixEnd_941368 := by exact prefixLift 941368
  have htrace : WordTrace (prefixWord ++ tailWord_941368) baseStart_941368 baseEnd_941368 := by
    simpa [prefixWord, tailWord_941368, baseEnd_941368] using wordTrace_append hprefix tailTrace_941368
  have hstable : (prefixWord ++ tailWord_941368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941368).length < 2 ^ (prefixWord ++ tailWord_941368).sum := by decide
  have hdescent : baseEnd_941368 < baseStart_941368 := by decide
  rcases family_descends (prefixWord ++ tailWord_941368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941373 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_941373 : Nat := 118140960795 + 941373 * 2 ^ 59
def prefixEnd_941373 : Nat := 4983230072969 + 3 ^ 40 * 941373 * 2
def baseEnd_941373 : Nat := 483376824165050607508211

theorem tailTrace_941373 : CollatzResearch.WordTrace tailWord_941373 prefixEnd_941373 483376824165050607508211 := by
  unfold tailWord_941373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34334694018573869553660773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22889796012382579702440515 34334694018573869553660773)
  ·
    refine ⟨6437755128482600541311395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34334694018573869553660773 6437755128482600541311395)
    ·
      refine ⟨9656632692723900811967093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6437755128482600541311395 9656632692723900811967093)
      ·
        refine ⟨905309314942865701121915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9656632692723900811967093 905309314942865701121915)
        ·
          refine ⟨1357963972414298551682873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905309314942865701121915 1357963972414298551682873)
          ·
            refine ⟨1018472979310723913762155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1357963972414298551682873 1018472979310723913762155)
            ·
              refine ⟨1527709468966085870643233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018472979310723913762155 1527709468966085870643233)
              ·
                refine ⟨1145782101724564402982425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527709468966085870643233 1145782101724564402982425)
                ·
                  refine ⟨859336576293423302236819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145782101724564402982425 859336576293423302236819)
                  ·
                    refine ⟨1289004864440134953355229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 859336576293423302236819 1289004864440134953355229)
                    ·
                      refine ⟨483376824165050607508211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289004864440134953355229 483376824165050607508211)
                      ·
                        rfl

theorem cell23_941373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_941373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941373 prefixEnd_941373 := by exact prefixLift 941373
  have htrace : WordTrace (prefixWord ++ tailWord_941373) baseStart_941373 baseEnd_941373 := by
    simpa [prefixWord, tailWord_941373, baseEnd_941373] using wordTrace_append hprefix tailTrace_941373
  have hstable : (prefixWord ++ tailWord_941373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941373).length < 2 ^ (prefixWord ++ tailWord_941373).sum := by decide
  have hdescent : baseEnd_941373 < baseStart_941373 := by decide
  rcases family_descends (prefixWord ++ tailWord_941373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941375 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_941375 : Nat := 118140960795 + 941375 * 2 ^ 59
def prefixEnd_941375 : Nat := 4983230072969 + 3 ^ 40 * 941375 * 2
def baseEnd_941375 : Nat := 483377851126359599683201

theorem tailTrace_941375 : CollatzResearch.WordTrace tailWord_941375 prefixEnd_941375 483377851126359599683201 := by
  unfold tailWord_941375
  simp only [CollatzResearch.WordTrace]
  refine ⟨34334766964566623895233579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22889844643044415930155719 34334766964566623895233579)
  ·
    refine ⟨51502150446849935842850369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34334766964566623895233579 51502150446849935842850369)
    ·
      refine ⟨38626612835137451882137777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51502150446849935842850369 38626612835137451882137777)
      ·
        refine ⟨28969959626353088911603333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38626612835137451882137777 28969959626353088911603333)
        ·
          refine ⟨5431867429941204170925625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28969959626353088911603333 5431867429941204170925625)
          ·
            refine ⟨4073900572455903128194219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5431867429941204170925625 4073900572455903128194219)
            ·
              refine ⟨6110850858683854692291329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073900572455903128194219 6110850858683854692291329)
              ·
                refine ⟨4583138144012891019218497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110850858683854692291329 4583138144012891019218497)
                ·
                  refine ⟨3437353608009668264413873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583138144012891019218497 3437353608009668264413873)
                  ·
                    refine ⟨2578015206007251198310405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3437353608009668264413873 2578015206007251198310405)
                    ·
                      refine ⟨483377851126359599683201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2578015206007251198310405 483377851126359599683201)
                      ·
                        rfl

theorem cell23_941375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_941375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941375 prefixEnd_941375 := by exact prefixLift 941375
  have htrace : WordTrace (prefixWord ++ tailWord_941375) baseStart_941375 baseEnd_941375 := by
    simpa [prefixWord, tailWord_941375, baseEnd_941375] using wordTrace_append hprefix tailTrace_941375
  have hstable : (prefixWord ++ tailWord_941375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941375).length < 2 ^ (prefixWord ++ tailWord_941375).sum := by decide
  have hdescent : baseEnd_941375 < baseStart_941375 := by decide
  rcases family_descends (prefixWord ++ tailWord_941375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941395 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3]
def baseStart_941395 : Nat := 118140960795 + 941395 * 2 ^ 59
def prefixEnd_941395 : Nat := 4983230072969 + 3 ^ 40 * 941395 * 2
def baseEnd_941395 : Nat := 483388120739449521433109

theorem tailTrace_941395 : CollatzResearch.WordTrace tailWord_941395 prefixEnd_941395 483388120739449521433109 := by
  unfold tailWord_941395
  simp only [CollatzResearch.WordTrace]
  refine ⟨34335496424494167310961639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22890330949662778207307759 34335496424494167310961639)
  ·
    refine ⟨51503244636741250966442459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34335496424494167310961639 51503244636741250966442459)
    ·
      refine ⟨77254866955111876449663689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51503244636741250966442459 77254866955111876449663689)
      ·
        refine ⟨57941150216333907337247767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77254866955111876449663689 57941150216333907337247767)
        ·
          refine ⟨86911725324500861005871651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57941150216333907337247767 86911725324500861005871651)
          ·
            refine ⟨130367587986751291508807477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86911725324500861005871651 130367587986751291508807477)
            ·
              refine ⟨12221961373757933578950701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130367587986751291508807477 12221961373757933578950701)
              ·
                refine ⟨4583235515159225092106513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12221961373757933578950701 4583235515159225092106513)
                ·
                  refine ⟨3437426636369418819079885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583235515159225092106513 3437426636369418819079885)
                  ·
                    refine ⟨1289034988638532057154957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437426636369418819079885 1289034988638532057154957)
                    ·
                      refine ⟨483388120739449521433109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289034988638532057154957 483388120739449521433109)
                      ·
                        rfl

theorem cell23_941395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_941395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941395 prefixEnd_941395 := by exact prefixLift 941395
  have htrace : WordTrace (prefixWord ++ tailWord_941395) baseStart_941395 baseEnd_941395 := by
    simpa [prefixWord, tailWord_941395, baseEnd_941395] using wordTrace_append hprefix tailTrace_941395
  have hstable : (prefixWord ++ tailWord_941395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941395).length < 2 ^ (prefixWord ++ tailWord_941395).sum := by decide
  have hdescent : baseEnd_941395 < baseStart_941395 := by decide
  rcases family_descends (prefixWord ++ tailWord_941395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941452 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_941452 : Nat := 118140960795 + 941452 * 2 ^ 59
def prefixEnd_941452 : Nat := 4983230072969 + 3 ^ 40 * 941452 * 2
def baseEnd_941452 : Nat := 483417389136755798420347

theorem tailTrace_941452 : CollatzResearch.WordTrace tailWord_941452 prefixEnd_941452 483417389136755798420347 := by
  unfold tailWord_941452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168787692643833022893305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22891716923525110697191073 17168787692643833022893305)
  ·
    refine ⟨12876590769482874767169979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17168787692643833022893305 12876590769482874767169979)
    ·
      refine ⟨19314886154224312150754969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12876590769482874767169979 19314886154224312150754969)
      ·
        refine ⟨14486164615668234113066227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19314886154224312150754969 14486164615668234113066227)
        ·
          refine ⟨21729246923502351169599341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14486164615668234113066227 21729246923502351169599341)
          ·
            refine ⟨8148467596313381688599753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21729246923502351169599341 8148467596313381688599753)
            ·
              refine ⟨6111350697235036266449815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8148467596313381688599753 6111350697235036266449815)
              ·
                refine ⟨9167026045852554399674723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111350697235036266449815 9167026045852554399674723)
                ·
                  refine ⟨13750539068778831599512085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167026045852554399674723 13750539068778831599512085)
                  ·
                    refine ⟨644556518849007731227129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13750539068778831599512085 644556518849007731227129)
                    ·
                      refine ⟨483417389136755798420347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644556518849007731227129 483417389136755798420347)
                      ·
                        rfl

theorem cell23_941452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_941452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941452 prefixEnd_941452 := by exact prefixLift 941452
  have htrace : WordTrace (prefixWord ++ tailWord_941452) baseStart_941452 baseEnd_941452 := by
    simpa [prefixWord, tailWord_941452, baseEnd_941452] using wordTrace_append hprefix tailTrace_941452
  have hstable : (prefixWord ++ tailWord_941452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941452).length < 2 ^ (prefixWord ++ tailWord_941452).sum := by decide
  have hdescent : baseEnd_941452 < baseStart_941452 := by decide
  rcases family_descends (prefixWord ++ tailWord_941452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941469 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_941469 : Nat := 118140960795 + 941469 * 2 ^ 59
def prefixEnd_941469 : Nat := 4983230072969 + 3 ^ 40 * 941469 * 2
def baseEnd_941469 : Nat := 483426118307882231907769

theorem tailTrace_941469 : CollatzResearch.WordTrace tailWord_941469 prefixEnd_941469 483426118307882231907769 := by
  unfold tailWord_941469
  simp only [CollatzResearch.WordTrace]
  refine ⟨34338195426226077949155461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22892130284150718632770307 34338195426226077949155461)
  ·
    refine ⟨6438411642417389615466649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34338195426226077949155461 6438411642417389615466649)
    ·
      refine ⟨4828808731813042211599987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6438411642417389615466649 4828808731813042211599987)
      ·
        refine ⟨7243213097719563317399981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828808731813042211599987 7243213097719563317399981)
        ·
          refine ⟨2716204911644836244024993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7243213097719563317399981 2716204911644836244024993)
          ·
            refine ⟨2037153683733627183018745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2716204911644836244024993 2037153683733627183018745)
            ·
              refine ⟨1527865262800220387264059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037153683733627183018745 1527865262800220387264059)
              ·
                refine ⟨2291797894200330580896089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527865262800220387264059 2291797894200330580896089)
                ·
                  refine ⟨1718848420650247935672067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2291797894200330580896089 1718848420650247935672067)
                  ·
                    refine ⟨2578272630975371903508101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1718848420650247935672067 2578272630975371903508101)
                    ·
                      refine ⟨483426118307882231907769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2578272630975371903508101 483426118307882231907769)
                      ·
                        rfl

theorem cell23_941469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_941469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941469 prefixEnd_941469 := by exact prefixLift 941469
  have htrace : WordTrace (prefixWord ++ tailWord_941469) baseStart_941469 baseEnd_941469 := by
    simpa [prefixWord, tailWord_941469, baseEnd_941469] using wordTrace_append hprefix tailTrace_941469
  have hstable : (prefixWord ++ tailWord_941469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941469).length < 2 ^ (prefixWord ++ tailWord_941469).sum := by decide
  have hdescent : baseEnd_941469 < baseStart_941469 := by decide
  rcases family_descends (prefixWord ++ tailWord_941469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941495 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_941495 : Nat := 118140960795 + 941495 * 2 ^ 59
def prefixEnd_941495 : Nat := 4983230072969 + 3 ^ 40 * 941495 * 2
def baseEnd_941495 : Nat := 483439468804899130182649

theorem tailTrace_941495 : CollatzResearch.WordTrace tailWord_941495 prefixEnd_941495 483439468804899130182649 := by
  unfold tailWord_941495
  simp only [CollatzResearch.WordTrace]
  refine ⟨34339143724131884389601939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22892762482754589593067959 34339143724131884389601939)
  ·
    refine ⟨51508715586197826584402909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34339143724131884389601939 51508715586197826584402909)
    ·
      refine ⟨19315768344824184969151091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51508715586197826584402909 19315768344824184969151091)
      ·
        refine ⟨28973652517236277453726637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19315768344824184969151091 28973652517236277453726637)
        ·
          refine ⟨10865119693963604045147489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28973652517236277453726637 10865119693963604045147489)
          ·
            refine ⟨8148839770472703033860617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10865119693963604045147489 8148839770472703033860617)
            ·
              refine ⟨6111629827854527275395463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8148839770472703033860617 6111629827854527275395463)
              ·
                refine ⟨9167444741781790913093195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111629827854527275395463 9167444741781790913093195)
                ·
                  refine ⟨13751167112672686369639793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167444741781790913093195 13751167112672686369639793)
                  ·
                    refine ⟨10313375334504514777229845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13751167112672686369639793 10313375334504514777229845)
                    ·
                      refine ⟨483439468804899130182649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10313375334504514777229845 483439468804899130182649)
                      ·
                        rfl

theorem cell23_941495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_941495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941495 prefixEnd_941495 := by exact prefixLift 941495
  have htrace : WordTrace (prefixWord ++ tailWord_941495) baseStart_941495 baseEnd_941495 := by
    simpa [prefixWord, tailWord_941495, baseEnd_941495] using wordTrace_append hprefix tailTrace_941495
  have hstable : (prefixWord ++ tailWord_941495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941495).length < 2 ^ (prefixWord ++ tailWord_941495).sum := by decide
  have hdescent : baseEnd_941495 < baseStart_941495 := by decide
  rcases family_descends (prefixWord ++ tailWord_941495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941496 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 1, 4]
def baseStart_941496 : Nat := 118140960795 + 941496 * 2 ^ 59
def prefixEnd_941496 : Nat := 4983230072969 + 3 ^ 40 * 941496 * 2
def baseEnd_941496 : Nat := 161146660761851208756715

theorem tailTrace_941496 : CollatzResearch.WordTrace tailWord_941496 prefixEnd_941496 161146660761851208756715 := by
  unfold tailWord_941496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17169590098564130780194171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22892786798085507706925561 17169590098564130780194171)
  ·
    refine ⟨25754385147846196170291257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17169590098564130780194171 25754385147846196170291257)
    ·
      refine ⟨19315788860884647127718443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25754385147846196170291257 19315788860884647127718443)
      ·
        refine ⟨28973683291326970691577665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19315788860884647127718443 28973683291326970691577665)
        ·
          refine ⟨21730262468495228018683249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28973683291326970691577665 21730262468495228018683249)
          ·
            refine ⟨16297696851371421014012437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21730262468495228018683249 16297696851371421014012437)
            ·
              refine ⟨763954539908035360031833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16297696851371421014012437 763954539908035360031833)
              ·
                refine ⟨572965904931026520023875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763954539908035360031833 572965904931026520023875)
                ·
                  refine ⟨859448857396539780035813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572965904931026520023875 859448857396539780035813)
                  ·
                    refine ⟨161146660761851208756715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 859448857396539780035813 161146660761851208756715)
                    ·
                      rfl

theorem cell23_941496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_941496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941496 prefixEnd_941496 := by exact prefixLift 941496
  have htrace : WordTrace (prefixWord ++ tailWord_941496) baseStart_941496 baseEnd_941496 := by
    simpa [prefixWord, tailWord_941496, baseEnd_941496] using wordTrace_append hprefix tailTrace_941496
  have hstable : (prefixWord ++ tailWord_941496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941496).length < 2 ^ (prefixWord ++ tailWord_941496).sum := by decide
  have hdescent : baseEnd_941496 < baseStart_941496 := by decide
  rcases family_descends (prefixWord ++ tailWord_941496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941502 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_941502 : Nat := 118140960795 + 941502 * 2 ^ 59
def prefixEnd_941502 : Nat := 4983230072969 + 3 ^ 40 * 941502 * 2
def baseEnd_941502 : Nat := 483443063169480602795117

theorem tailTrace_941502 : CollatzResearch.WordTrace tailWord_941502 prefixEnd_941502 483443063169480602795117 := by
  unfold tailWord_941502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292424879388315573138345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22892932690071016390071173 4292424879388315573138345)
  ·
    refine ⟨3219318659541236679853759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4292424879388315573138345 3219318659541236679853759)
    ·
      refine ⟨4828977989311855019780639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3219318659541236679853759 4828977989311855019780639)
      ·
        refine ⟨7243466983967782529670959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828977989311855019780639 7243466983967782529670959)
        ·
          refine ⟨10865200475951673794506439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243466983967782529670959 10865200475951673794506439)
          ·
            refine ⟨16297800713927510691759659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10865200475951673794506439 16297800713927510691759659)
            ·
              refine ⟨24446701070891266037639489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16297800713927510691759659 24446701070891266037639489)
              ·
                refine ⟨18335025803168449528229617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24446701070891266037639489 18335025803168449528229617)
                ·
                  refine ⟨13751269352376337146172213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18335025803168449528229617 13751269352376337146172213)
                  ·
                    refine ⟨1289181501785281607453645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13751269352376337146172213 1289181501785281607453645)
                    ·
                      refine ⟨483443063169480602795117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289181501785281607453645 483443063169480602795117)
                      ·
                        rfl

theorem cell23_941502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_941502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941502 prefixEnd_941502 := by exact prefixLift 941502
  have htrace : WordTrace (prefixWord ++ tailWord_941502) baseStart_941502 baseEnd_941502 := by
    simpa [prefixWord, tailWord_941502, baseEnd_941502] using wordTrace_append hprefix tailTrace_941502
  have hstable : (prefixWord ++ tailWord_941502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941502).length < 2 ^ (prefixWord ++ tailWord_941502).sum := by decide
  have hdescent : baseEnd_941502 < baseStart_941502 := by decide
  rcases family_descends (prefixWord ++ tailWord_941502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941529 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 5, 2]
def baseStart_941529 : Nat := 118140960795 + 941529 * 2 ^ 59
def prefixEnd_941529 : Nat := 4983230072969 + 3 ^ 40 * 941529 * 2
def baseEnd_941529 : Nat := 483456927147151997157493

theorem tailTrace_941529 : CollatzResearch.WordTrace tailWord_941529 prefixEnd_941529 483456927147151997157493 := by
  unfold tailWord_941529
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340383806008708196339641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22893589204005805464226427 34340383806008708196339641)
  ·
    refine ⟨25755287854506531147254731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34340383806008708196339641 25755287854506531147254731)
    ·
      refine ⟨38632931781759796720882097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25755287854506531147254731 38632931781759796720882097)
      ·
        refine ⟨28974698836319847540661573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38632931781759796720882097 28974698836319847540661573)
        ·
          refine ⟨5432756031809971413874045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28974698836319847540661573 5432756031809971413874045)
          ·
            refine ⟨2037283511928739280202767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432756031809971413874045 2037283511928739280202767)
            ·
              refine ⟨3055925267893108920304151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037283511928739280202767 3055925267893108920304151)
              ·
                refine ⟨4583887901839663380456227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055925267893108920304151 4583887901839663380456227)
                ·
                  refine ⟨6875831852759495070684341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583887901839663380456227 6875831852759495070684341)
                  ·
                    refine ⟨644609236196202662876657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6875831852759495070684341 644609236196202662876657)
                    ·
                      refine ⟨483456927147151997157493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644609236196202662876657 483456927147151997157493)
                      ·
                        rfl

theorem cell23_941529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_941529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941529 prefixEnd_941529 := by exact prefixLift 941529
  have htrace : WordTrace (prefixWord ++ tailWord_941529) baseStart_941529 baseEnd_941529 := by
    simpa [prefixWord, tailWord_941529, baseEnd_941529] using wordTrace_append hprefix tailTrace_941529
  have hstable : (prefixWord ++ tailWord_941529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941529).length < 2 ^ (prefixWord ++ tailWord_941529).sum := by decide
  have hdescent : baseEnd_941529 < baseStart_941529 := by decide
  rcases family_descends (prefixWord ++ tailWord_941529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941539 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 1, 5]
def baseStart_941539 : Nat := 118140960795 + 941539 * 2 ^ 59
def prefixEnd_941539 : Nat := 4983230072969 + 3 ^ 40 * 941539 * 2
def baseEnd_941539 : Nat := 161154020651232319344149

theorem tailTrace_941539 : CollatzResearch.WordTrace tailWord_941539 prefixEnd_941539 161154020651232319344149 := by
  unfold tailWord_941539
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340748535972479904203671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22893832357314986602802447 34340748535972479904203671)
  ·
    refine ⟨51511122803958719856305507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34340748535972479904203671 51511122803958719856305507)
    ·
      refine ⟨77266684205938079784458261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51511122803958719856305507 77266684205938079784458261)
      ·
        refine ⟨3621875822153347489896481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77266684205938079784458261 3621875822153347489896481)
        ·
          refine ⟨2716406866615010617422361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621875822153347489896481 2716406866615010617422361)
          ·
            refine ⟨2037305149961257963066771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2716406866615010617422361 2037305149961257963066771)
            ·
              refine ⟨3055957724941886944600157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037305149961257963066771 3055957724941886944600157)
              ·
                refine ⟨1145984146853207604225059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3055957724941886944600157 1145984146853207604225059)
                ·
                  refine ⟨1718976220279811406337589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145984146853207604225059 1718976220279811406337589)
                  ·
                    refine ⟨161154020651232319344149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1718976220279811406337589 161154020651232319344149)
                    ·
                      rfl

theorem cell23_941539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 5].length) (baseStart_941539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941539 prefixEnd_941539 := by exact prefixLift 941539
  have htrace : WordTrace (prefixWord ++ tailWord_941539) baseStart_941539 baseEnd_941539 := by
    simpa [prefixWord, tailWord_941539, baseEnd_941539] using wordTrace_append hprefix tailTrace_941539
  have hstable : (prefixWord ++ tailWord_941539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941539).length < 2 ^ (prefixWord ++ tailWord_941539).sum := by decide
  have hdescent : baseEnd_941539 < baseStart_941539 := by decide
  rcases family_descends (prefixWord ++ tailWord_941539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941562 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_941562 : Nat := 118140960795 + 941562 * 2 ^ 59
def prefixEnd_941562 : Nat := 4983230072969 + 3 ^ 40 * 941562 * 2
def baseEnd_941562 : Nat := 483473872008750368044841

theorem tailTrace_941562 : CollatzResearch.WordTrace tailWord_941562 prefixEnd_941562 483473872008750368044841 := by
  unfold tailWord_941562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585396853722288708072735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22894391609926103221527293 8585396853722288708072735)
  ·
    refine ⟨12878095280583433062109103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8585396853722288708072735 12878095280583433062109103)
    ·
      refine ⟨19317142920875149593163655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878095280583433062109103 19317142920875149593163655)
      ·
        refine ⟨28975714381312724389745483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19317142920875149593163655 28975714381312724389745483)
        ·
          refine ⟨43463571571969086584618225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28975714381312724389745483 43463571571969086584618225)
          ·
            refine ⟨32597678678976814938463669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43463571571969086584618225 32597678678976814938463669)
            ·
              refine ⟨3056032376154076400480969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32597678678976814938463669 3056032376154076400480969)
              ·
                refine ⟨2292024282115557300360727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056032376154076400480969 2292024282115557300360727)
                ·
                  refine ⟨3438036423173335950541091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292024282115557300360727 3438036423173335950541091)
                  ·
                    refine ⟨5157054634760003925811637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3438036423173335950541091 5157054634760003925811637)
                    ·
                      refine ⟨483473872008750368044841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5157054634760003925811637 483473872008750368044841)
                      ·
                        rfl

theorem cell23_941562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_941562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941562 prefixEnd_941562 := by exact prefixLift 941562
  have htrace : WordTrace (prefixWord ++ tailWord_941562) baseStart_941562 baseEnd_941562 := by
    simpa [prefixWord, tailWord_941562, baseEnd_941562] using wordTrace_append hprefix tailTrace_941562
  have hstable : (prefixWord ++ tailWord_941562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941562).length < 2 ^ (prefixWord ++ tailWord_941562).sum := by decide
  have hdescent : baseEnd_941562 < baseStart_941562 := by decide
  rcases family_descends (prefixWord ++ tailWord_941562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941576 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_941576 : Nat := 118140960795 + 941576 * 2 ^ 59
def prefixEnd_941576 : Nat := 4983230072969 + 3 ^ 40 * 941576 * 2
def baseEnd_941576 : Nat := 483481060737913313269777

theorem tailTrace_941576 : CollatzResearch.WordTrace tailWord_941576 prefixEnd_941576 483481060737913313269777 := by
  unfold tailWord_941576
  simp only [CollatzResearch.WordTrace]
  refine ⟨17171049018419217611650291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22894732024558956815533721 17171049018419217611650291)
  ·
    refine ⟨25756573527628826417475437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17171049018419217611650291 25756573527628826417475437)
    ·
      refine ⟨9658715072860809906553289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25756573527628826417475437 9658715072860809906553289)
      ·
        refine ⟨7244036304645607429914967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9658715072860809906553289 7244036304645607429914967)
        ·
          refine ⟨10866054456968411144872451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244036304645607429914967 10866054456968411144872451)
          ·
            refine ⟨16299081685452616717308677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866054456968411144872451 16299081685452616717308677)
            ·
              refine ⟨3056077816022365634495377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16299081685452616717308677 3056077816022365634495377)
              ·
                refine ⟨2292058362016774225871533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056077816022365634495377 2292058362016774225871533)
                ·
                  refine ⟨859521885756290334701825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2292058362016774225871533 859521885756290334701825)
                  ·
                    refine ⟨644641414317217751026369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 859521885756290334701825 644641414317217751026369)
                    ·
                      refine ⟨483481060737913313269777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644641414317217751026369 483481060737913313269777)
                      ·
                        rfl

theorem cell23_941576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_941576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941576 prefixEnd_941576 := by exact prefixLift 941576
  have htrace : WordTrace (prefixWord ++ tailWord_941576) baseStart_941576 baseEnd_941576 := by
    simpa [prefixWord, tailWord_941576, baseEnd_941576] using wordTrace_append hprefix tailTrace_941576
  have hstable : (prefixWord ++ tailWord_941576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941576).length < 2 ^ (prefixWord ++ tailWord_941576).sum := by decide
  have hdescent : baseEnd_941576 < baseStart_941576 := by decide
  rcases family_descends (prefixWord ++ tailWord_941576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941626 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_941626 : Nat := 118140960795 + 941626 * 2 ^ 59
def prefixEnd_941626 : Nat := 4983230072969 + 3 ^ 40 * 941626 * 2
def baseEnd_941626 : Nat := 483506734770638117644547

theorem tailTrace_941626 : CollatzResearch.WordTrace tailWord_941626 prefixEnd_941626 483506734770638117644547 := by
  unfold tailWord_941626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585980421664323440655183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22895947791104862508413821 8585980421664323440655183)
  ·
    refine ⟨12878970632496485160982775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8585980421664323440655183 12878970632496485160982775)
    ·
      refine ⟨19318455948744727741474163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878970632496485160982775 19318455948744727741474163)
      ·
        refine ⟨28977683923117091612211245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318455948744727741474163 28977683923117091612211245)
        ·
          refine ⟨10866631471168909354579217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28977683923117091612211245 10866631471168909354579217)
          ·
            refine ⟨8149973603376682015934413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10866631471168909354579217 8149973603376682015934413)
            ·
              refine ⟨3056240101266255755975405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8149973603376682015934413 3056240101266255755975405)
              ·
                refine ⟨1146090037974845908490777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3056240101266255755975405 1146090037974845908490777)
                ·
                  refine ⟨859567528481134431368083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1146090037974845908490777 859567528481134431368083)
                  ·
                    refine ⟨1289351292721701647052125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 859567528481134431368083 1289351292721701647052125)
                    ·
                      refine ⟨483506734770638117644547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289351292721701647052125 483506734770638117644547)
                      ·
                        rfl

theorem cell23_941626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_941626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941626 prefixEnd_941626 := by exact prefixLift 941626
  have htrace : WordTrace (prefixWord ++ tailWord_941626) baseStart_941626 baseEnd_941626 := by
    simpa [prefixWord, tailWord_941626, baseEnd_941626] using wordTrace_append hprefix tailTrace_941626
  have hstable : (prefixWord ++ tailWord_941626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941626).length < 2 ^ (prefixWord ++ tailWord_941626).sum := by decide
  have hdescent : baseEnd_941626 < baseStart_941626 := by decide
  rcases family_descends (prefixWord ++ tailWord_941626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941661 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_941661 : Nat := 118140960795 + 941661 * 2 ^ 59
def prefixEnd_941661 : Nat := 4983230072969 + 3 ^ 40 * 941661 * 2
def baseEnd_941661 : Nat := 483524706593545480706887

theorem tailTrace_941661 : CollatzResearch.WordTrace tailWord_941661 prefixEnd_941661 483524706593545480706887 := by
  unfold tailWord_941661
  simp only [CollatzResearch.WordTrace]
  refine ⟨34345198241530494740144837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22896798827686996493429891 34345198241530494740144837)
  ·
    refine ⟨6439724670286967763777157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34345198241530494740144837 6439724670286967763777157)
    ·
      refine ⟨1207448375678806455708217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6439724670286967763777157 1207448375678806455708217)
      ·
        refine ⟨905586281759104841781163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207448375678806455708217 905586281759104841781163)
        ·
          refine ⟨1358379422638657262671745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905586281759104841781163 1358379422638657262671745)
          ·
            refine ⟨1018784566978992947003809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358379422638657262671745 1018784566978992947003809)
            ·
              refine ⟨764088425234244710252857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018784566978992947003809 764088425234244710252857)
              ·
                refine ⟨573066318925683532689643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764088425234244710252857 573066318925683532689643)
                ·
                  refine ⟨859599478388525299034465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573066318925683532689643 859599478388525299034465)
                  ·
                    refine ⟨644699608791393974275849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 859599478388525299034465 644699608791393974275849)
                    ·
                      refine ⟨483524706593545480706887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644699608791393974275849 483524706593545480706887)
                      ·
                        rfl

theorem cell23_941661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_941661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941661 prefixEnd_941661 := by exact prefixLift 941661
  have htrace : WordTrace (prefixWord ++ tailWord_941661) baseStart_941661 baseEnd_941661 := by
    simpa [prefixWord, tailWord_941661, baseEnd_941661] using wordTrace_append hprefix tailTrace_941661
  have hstable : (prefixWord ++ tailWord_941661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941661).length < 2 ^ (prefixWord ++ tailWord_941661).sum := by decide
  have hdescent : baseEnd_941661 < baseStart_941661 := by decide
  rcases family_descends (prefixWord ++ tailWord_941661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941669 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_941669 : Nat := 118140960795 + 941669 * 2 ^ 59
def prefixEnd_941669 : Nat := 4983230072969 + 3 ^ 40 * 941669 * 2
def baseEnd_941669 : Nat := 483528814438781449406849

theorem tailTrace_941669 : CollatzResearch.WordTrace tailWord_941669 prefixEnd_941669 483528814438781449406849 := by
  unfold tailWord_941669
  simp only [CollatzResearch.WordTrace]
  refine ⟨34345490025501512106436061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22896993350334341404290707 34345490025501512106436061)
  ·
    refine ⟨12879558759563067039913523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34345490025501512106436061 12879558759563067039913523)
    ·
      refine ⟨19319338139344600559870285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12879558759563067039913523 19319338139344600559870285)
      ·
        refine ⟨7244751802254225209951357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19319338139344600559870285 7244751802254225209951357)
        ·
          refine ⟨2716781925845334453731759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7244751802254225209951357 2716781925845334453731759)
          ·
            refine ⟨4075172888768001680597639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716781925845334453731759 4075172888768001680597639)
            ·
              refine ⟨6112759333152002520896459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075172888768001680597639 6112759333152002520896459)
              ·
                refine ⟨9169138999728003781344689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112759333152002520896459 9169138999728003781344689)
                ·
                  refine ⟨6876854249796002836008517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169138999728003781344689 6876854249796002836008517)
                  ·
                    refine ⟨1289410171836750531751597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876854249796002836008517 1289410171836750531751597)
                    ·
                      refine ⟨483528814438781449406849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289410171836750531751597 483528814438781449406849)
                      ·
                        rfl

theorem cell23_941669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_941669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941669 prefixEnd_941669 := by exact prefixLift 941669
  have htrace : WordTrace (prefixWord ++ tailWord_941669) baseStart_941669 baseEnd_941669 := by
    simpa [prefixWord, tailWord_941669, baseEnd_941669] using wordTrace_append hprefix tailTrace_941669
  have hstable : (prefixWord ++ tailWord_941669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941669).length < 2 ^ (prefixWord ++ tailWord_941669).sum := by decide
  have hdescent : baseEnd_941669 < baseStart_941669 := by decide
  rcases family_descends (prefixWord ++ tailWord_941669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941704 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_941704 : Nat := 118140960795 + 941704 * 2 ^ 59
def prefixEnd_941704 : Nat := 4983230072969 + 3 ^ 40 * 941704 * 2
def baseEnd_941704 : Nat := 483546786261688812469189

theorem tailTrace_941704 : CollatzResearch.WordTrace tailWord_941704 prefixEnd_941704 483546786261688812469189 := by
  unfold tailWord_941704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173383290187356541980083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22897844386916475389306777 17173383290187356541980083)
  ·
    refine ⟨25760074935281034812970125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173383290187356541980083 25760074935281034812970125)
    ·
      refine ⟨9660028100730388054863797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25760074935281034812970125 9660028100730388054863797)
      ·
        refine ⟨905627634443473880143481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9660028100730388054863797 905627634443473880143481)
        ·
          refine ⟨679220725832605410107611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905627634443473880143481 679220725832605410107611)
          ·
            refine ⟨1018831088748908115161417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679220725832605410107611 1018831088748908115161417)
            ·
              refine ⟨764123316561681086371063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018831088748908115161417 764123316561681086371063)
              ·
                refine ⟨1146184974842521629556595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764123316561681086371063 1146184974842521629556595)
                ·
                  refine ⟨1719277462263782444334893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146184974842521629556595 1719277462263782444334893)
                  ·
                    refine ⟨644729048348918416625585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719277462263782444334893 644729048348918416625585)
                    ·
                      refine ⟨483546786261688812469189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 644729048348918416625585 483546786261688812469189)
                      ·
                        rfl

theorem cell23_941704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_941704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941704 prefixEnd_941704 := by exact prefixLift 941704
  have htrace : WordTrace (prefixWord ++ tailWord_941704) baseStart_941704 baseEnd_941704 := by
    simpa [prefixWord, tailWord_941704, baseEnd_941704] using wordTrace_append hprefix tailTrace_941704
  have hstable : (prefixWord ++ tailWord_941704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941704).length < 2 ^ (prefixWord ++ tailWord_941704).sum := by decide
  have hdescent : baseEnd_941704 < baseStart_941704 := by decide
  rcases family_descends (prefixWord ++ tailWord_941704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941706 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_941706 : Nat := 118140960795 + 941706 * 2 ^ 59
def prefixEnd_941706 : Nat := 4983230072969 + 3 ^ 40 * 941706 * 2
def baseEnd_941706 : Nat := 53727534802555311627131

theorem tailTrace_941706 : CollatzResearch.WordTrace tailWord_941706 prefixEnd_941706 53727534802555311627131 := by
  unfold tailWord_941706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586709881591866856383243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22897893017578311617021981 8586709881591866856383243)
  ·
    refine ⟨12880064822387800284574865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8586709881591866856383243 12880064822387800284574865)
    ·
      refine ⟨9660048616790850213431149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12880064822387800284574865 9660048616790850213431149)
      ·
        refine ⟨3622518231296568830036681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9660048616790850213431149 3622518231296568830036681)
        ·
          refine ⟨2716888673472426622527511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3622518231296568830036681 2716888673472426622527511)
          ·
            refine ⟨4075333010208639933791267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716888673472426622527511 4075333010208639933791267)
            ·
              refine ⟨6112999515312959900686901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075333010208639933791267 6112999515312959900686901)
              ·
                refine ⟨573093704560589990689397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6112999515312959900686901 573093704560589990689397)
                ·
                  refine ⟨53727534802555311627131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573093704560589990689397 53727534802555311627131)
                  ·
                    rfl

theorem cell23_941706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_941706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941706 prefixEnd_941706 := by exact prefixLift 941706
  have htrace : WordTrace (prefixWord ++ tailWord_941706) baseStart_941706 baseEnd_941706 := by
    simpa [prefixWord, tailWord_941706, baseEnd_941706] using wordTrace_append hprefix tailTrace_941706
  have hstable : (prefixWord ++ tailWord_941706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941706).length < 2 ^ (prefixWord ++ tailWord_941706).sum := by decide
  have hdescent : baseEnd_941706 < baseStart_941706 := by decide
  rcases family_descends (prefixWord ++ tailWord_941706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941712 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_941712 : Nat := 118140960795 + 941712 * 2 ^ 59
def prefixEnd_941712 : Nat := 4983230072969 + 3 ^ 40 * 941712 * 2
def baseEnd_941712 : Nat := 483550894106924781169151

theorem tailTrace_941712 : CollatzResearch.WordTrace tailWord_941712 prefixEnd_941712 483550894106924781169151 := by
  unfold tailWord_941712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173529182172865225125695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22898038909563820300167593 17173529182172865225125695)
  ·
    refine ⟨25760293773259297837688543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173529182172865225125695 25760293773259297837688543)
    ·
      refine ⟨38640440659888946756532815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25760293773259297837688543 38640440659888946756532815)
      ·
        refine ⟨57960660989833420134799223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38640440659888946756532815 57960660989833420134799223)
        ·
          refine ⟨86940991484750130202198835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57960660989833420134799223 86940991484750130202198835)
          ·
            refine ⟨130411487227125195303298253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86940991484750130202198835 130411487227125195303298253)
            ·
              refine ⟨48904307710171948238736845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130411487227125195303298253 48904307710171948238736845)
              ·
                refine ⟨18339115391314480589526317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48904307710171948238736845 18339115391314480589526317)
                ·
                  refine ⟨6877168271742930221072369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18339115391314480589526317 6877168271742930221072369)
                  ·
                    refine ⟨5157876203807197665804277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6877168271742930221072369 5157876203807197665804277)
                    ·
                      refine ⟨483550894106924781169151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5157876203807197665804277 483550894106924781169151)
                      ·
                        rfl

theorem cell23_941712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_941712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941712 prefixEnd_941712 := by exact prefixLift 941712
  have htrace : WordTrace (prefixWord ++ tailWord_941712) baseStart_941712 baseEnd_941712 := by
    simpa [prefixWord, tailWord_941712, baseEnd_941712] using wordTrace_append hprefix tailTrace_941712
  have hstable : (prefixWord ++ tailWord_941712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941712).length < 2 ^ (prefixWord ++ tailWord_941712).sum := by decide
  have hdescent : baseEnd_941712 < baseStart_941712 := by decide
  rcases family_descends (prefixWord ++ tailWord_941712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941759 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_941759 : Nat := 118140960795 + 941759 * 2 ^ 59
def prefixEnd_941759 : Nat := 4983230072969 + 3 ^ 40 * 941759 * 2
def baseEnd_941759 : Nat := 483575027697686097281435

theorem tailTrace_941759 : CollatzResearch.WordTrace tailWord_941759 prefixEnd_941759 483575027697686097281435 := by
  unfold tailWord_941759
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348772595175457477212331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22899181730116971651474887 34348772595175457477212331)
  ·
    refine ⟨51523158892763186215818497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34348772595175457477212331 51523158892763186215818497)
    ·
      refine ⟨38642369169572389661863873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51523158892763186215818497 38642369169572389661863873)
      ·
        refine ⟨28981776877179292246397905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38642369169572389661863873 28981776877179292246397905)
        ·
          refine ⟨21736332657884469184798429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28981776877179292246397905 21736332657884469184798429)
          ·
            refine ⟨8151124746706675944299411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21736332657884469184798429 8151124746706675944299411)
            ·
              refine ⟨12226687120060013916449117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151124746706675944299411 12226687120060013916449117)
              ·
                refine ⟨4585007670022505218668419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12226687120060013916449117 4585007670022505218668419)
                ·
                  refine ⟨6877511505033757828002629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585007670022505218668419 6877511505033757828002629)
                  ·
                    refine ⟨1289533407193829592750493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877511505033757828002629 1289533407193829592750493)
                    ·
                      refine ⟨483575027697686097281435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289533407193829592750493 483575027697686097281435)
                      ·
                        rfl

theorem cell23_941759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_941759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941759 prefixEnd_941759 := by exact prefixLift 941759
  have htrace : WordTrace (prefixWord ++ tailWord_941759) baseStart_941759 baseEnd_941759 := by
    simpa [prefixWord, tailWord_941759, baseEnd_941759] using wordTrace_append hprefix tailTrace_941759
  have hstable : (prefixWord ++ tailWord_941759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941759).length < 2 ^ (prefixWord ++ tailWord_941759).sum := by decide
  have hdescent : baseEnd_941759 < baseStart_941759 := by decide
  rcases family_descends (prefixWord ++ tailWord_941759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941773 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_941773 : Nat := 118140960795 + 941773 * 2 ^ 59
def prefixEnd_941773 : Nat := 4983230072969 + 3 ^ 40 * 941773 * 2
def baseEnd_941773 : Nat := 483582216426849042506371

theorem tailTrace_941773 : CollatzResearch.WordTrace tailWord_941773 prefixEnd_941773 483582216426849042506371 := by
  unfold tailWord_941773
  simp only [CollatzResearch.WordTrace]
  refine ⟨34349283217124737868221973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22899522144749825245481315 34349283217124737868221973)
  ·
    refine ⟨1610122650802722087572905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34349283217124737868221973 1610122650802722087572905)
    ·
      refine ⟨1207591988102041565679679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1610122650802722087572905 1207591988102041565679679)
      ·
        refine ⟨1811387982153062348519519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207591988102041565679679 1811387982153062348519519)
        ·
          refine ⟨2717081973229593522779279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811387982153062348519519 2717081973229593522779279)
          ·
            refine ⟨4075622959844390284168919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717081973229593522779279 4075622959844390284168919)
            ·
              refine ⟨6113434439766585426253379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075622959844390284168919 6113434439766585426253379)
              ·
                refine ⟨9170151659649878139380069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113434439766585426253379 9170151659649878139380069)
                ·
                  refine ⟨1719403436184352151133763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9170151659649878139380069 1719403436184352151133763)
                  ·
                    refine ⟨2579105154276528226700645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719403436184352151133763 2579105154276528226700645)
                    ·
                      refine ⟨483582216426849042506371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2579105154276528226700645 483582216426849042506371)
                      ·
                        rfl

theorem cell23_941773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_941773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941773 prefixEnd_941773 := by exact prefixLift 941773
  have htrace : WordTrace (prefixWord ++ tailWord_941773) baseStart_941773 baseEnd_941773 := by
    simpa [prefixWord, tailWord_941773, baseEnd_941773] using wordTrace_append hprefix tailTrace_941773
  have hstable : (prefixWord ++ tailWord_941773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941773).length < 2 ^ (prefixWord ++ tailWord_941773).sum := by decide
  have hdescent : baseEnd_941773 < baseStart_941773 := by decide
  rcases family_descends (prefixWord ++ tailWord_941773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941856 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_941856 : Nat := 118140960795 + 941856 * 2 ^ 59
def prefixEnd_941856 : Nat := 4983230072969 + 3 ^ 40 * 941856 * 2
def baseEnd_941856 : Nat := 161208278440390739256163

theorem tailTrace_941856 : CollatzResearch.WordTrace tailWord_941856 prefixEnd_941856 161208278440390739256163 := by
  unfold tailWord_941856
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176155237912021521746711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22901540317216028695662281 17176155237912021521746711)
  ·
    refine ⟨25764232856868032282620067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17176155237912021521746711 25764232856868032282620067)
    ·
      refine ⟨38646349285302048423930101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25764232856868032282620067 38646349285302048423930101)
      ·
        refine ⟨3623095245497067039743447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38646349285302048423930101 3623095245497067039743447)
        ·
          refine ⟨5434642868245600559615171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623095245497067039743447 5434642868245600559615171)
          ·
            refine ⟨8151964302368400839422757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434642868245600559615171 8151964302368400839422757)
            ·
              refine ⟨1528493306694075157391767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8151964302368400839422757 1528493306694075157391767)
              ·
                refine ⟨2292739960041112736087651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528493306694075157391767 2292739960041112736087651)
                ·
                  refine ⟨3439109940061669104131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292739960041112736087651 3439109940061669104131477)
                  ·
                    refine ⟨161208278440390739256163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3439109940061669104131477 161208278440390739256163)
                    ·
                      rfl

theorem cell23_941856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_941856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941856 prefixEnd_941856 := by exact prefixLift 941856
  have htrace : WordTrace (prefixWord ++ tailWord_941856) baseStart_941856 baseEnd_941856 := by
    simpa [prefixWord, tailWord_941856, baseEnd_941856] using wordTrace_append hprefix tailTrace_941856
  have hstable : (prefixWord ++ tailWord_941856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941856).length < 2 ^ (prefixWord ++ tailWord_941856).sum := by decide
  have hdescent : baseEnd_941856 < baseStart_941856 := by decide
  rcases family_descends (prefixWord ++ tailWord_941856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941859 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_941859 : Nat := 118140960795 + 941859 * 2 ^ 59
def prefixEnd_941859 : Nat := 4983230072969 + 3 ^ 40 * 941859 * 2
def baseEnd_941859 : Nat := 483626375763135706030975

theorem tailTrace_941859 : CollatzResearch.WordTrace tailWord_941859 prefixEnd_941859 483626375763135706030975 := by
  unfold tailWord_941859
  simp only [CollatzResearch.WordTrace]
  refine ⟨34352419894813174555852631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22901613263208783037235087 34352419894813174555852631)
  ·
    refine ⟨51528629842219761833778947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34352419894813174555852631 51528629842219761833778947)
    ·
      refine ⟨77292944763329642750668421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51528629842219761833778947 77292944763329642750668421)
      ·
        refine ⟨14492427143124308015750329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77292944763329642750668421 14492427143124308015750329)
        ·
          refine ⟨10869320357343231011812747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14492427143124308015750329 10869320357343231011812747)
          ·
            refine ⟨16303980536014846517719121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869320357343231011812747 16303980536014846517719121)
            ·
              refine ⟨12227985402011134888289341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16303980536014846517719121 12227985402011134888289341)
              ·
                refine ⟨4585494525754175583108503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12227985402011134888289341 4585494525754175583108503)
                ·
                  refine ⟨6878241788631263374662755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585494525754175583108503 6878241788631263374662755)
                  ·
                    refine ⟨10317362682946895061994133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878241788631263374662755 10317362682946895061994133)
                    ·
                      refine ⟨483626375763135706030975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10317362682946895061994133 483626375763135706030975)
                      ·
                        rfl

theorem cell23_941859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_941859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941859 prefixEnd_941859 := by exact prefixLift 941859
  have htrace : WordTrace (prefixWord ++ tailWord_941859) baseStart_941859 baseEnd_941859 := by
    simpa [prefixWord, tailWord_941859, baseEnd_941859] using wordTrace_append hprefix tailTrace_941859
  have hstable : (prefixWord ++ tailWord_941859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941859).length < 2 ^ (prefixWord ++ tailWord_941859).sum := by decide
  have hdescent : baseEnd_941859 < baseStart_941859 := by decide
  rcases family_descends (prefixWord ++ tailWord_941859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941877 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_941877 : Nat := 118140960795 + 941877 * 2 ^ 59
def prefixEnd_941877 : Nat := 4983230072969 + 3 ^ 40 * 941877 * 2
def baseEnd_941877 : Nat := 161211872804972211868631

theorem tailTrace_941877 : CollatzResearch.WordTrace tailWord_941877 prefixEnd_941877 161211872804972211868631 := by
  unfold tailWord_941877
  simp only [CollatzResearch.WordTrace]
  refine ⟨34353076408747963630007885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22902050939165309086671923 34353076408747963630007885)
  ·
    refine ⟨12882403653280486361252957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34353076408747963630007885 12882403653280486361252957)
    ·
      refine ⟨4830901369980182385469859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12882403653280486361252957 4830901369980182385469859)
      ·
        refine ⟨7246352054970273578204789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4830901369980182385469859 7246352054970273578204789)
        ·
          refine ⟨679345505153463147956699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7246352054970273578204789 679345505153463147956699)
          ·
            refine ⟨1019018257730194721935049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679345505153463147956699 1019018257730194721935049)
            ·
              refine ⟨764263693297646041451287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019018257730194721935049 764263693297646041451287)
              ·
                refine ⟨1146395539946469062176931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764263693297646041451287 1146395539946469062176931)
                ·
                  refine ⟨1719593309919703593265397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146395539946469062176931 1719593309919703593265397)
                  ·
                    refine ⟨161211872804972211868631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1719593309919703593265397 161211872804972211868631)
                    ·
                      rfl

theorem cell23_941877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_941877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941877 prefixEnd_941877 := by exact prefixLift 941877
  have htrace : WordTrace (prefixWord ++ tailWord_941877) baseStart_941877 baseEnd_941877 := by
    simpa [prefixWord, tailWord_941877, baseEnd_941877] using wordTrace_append hprefix tailTrace_941877
  have hstable : (prefixWord ++ tailWord_941877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941877).length < 2 ^ (prefixWord ++ tailWord_941877).sum := by decide
  have hdescent : baseEnd_941877 < baseStart_941877 := by decide
  rcases family_descends (prefixWord ++ tailWord_941877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941880 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_941880 : Nat := 118140960795 + 941880 * 2 ^ 59
def prefixEnd_941880 : Nat := 4983230072969 + 3 ^ 40 * 941880 * 2
def baseEnd_941880 : Nat := 483637158856880123868379

theorem tailTrace_941880 : CollatzResearch.WordTrace tailWord_941880 prefixEnd_941880 483637158856880123868379 := by
  unfold tailWord_941880
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176592913868547571183547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22902123885158063428244729 17176592913868547571183547)
  ·
    refine ⟨25764889370802821356775321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17176592913868547571183547 25764889370802821356775321)
    ·
      refine ⟨19323667028102116017581491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25764889370802821356775321 19323667028102116017581491)
      ·
        refine ⟨28985500542153174026372237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19323667028102116017581491 28985500542153174026372237)
        ·
          refine ⟨10869562703307440259889589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28985500542153174026372237 10869562703307440259889589)
          ·
            refine ⟨1019021503435072524364649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10869562703307440259889589 1019021503435072524364649)
            ·
              refine ⟨764266127576304393273487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019021503435072524364649 764266127576304393273487)
              ·
                refine ⟨1146399191364456589910231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764266127576304393273487 1146399191364456589910231)
                ·
                  refine ⟨1719598787046684884865347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146399191364456589910231 1719598787046684884865347)
                  ·
                    refine ⟨2579398180570027327298021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719598787046684884865347 2579398180570027327298021)
                    ·
                      refine ⟨483637158856880123868379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2579398180570027327298021 483637158856880123868379)
                      ·
                        rfl

theorem cell23_941880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_941880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941880 prefixEnd_941880 := by exact prefixLift 941880
  have htrace : WordTrace (prefixWord ++ tailWord_941880) baseStart_941880 baseEnd_941880 := by
    simpa [prefixWord, tailWord_941880, baseEnd_941880] using wordTrace_append hprefix tailTrace_941880
  have hstable : (prefixWord ++ tailWord_941880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941880).length < 2 ^ (prefixWord ++ tailWord_941880).sum := by decide
  have hdescent : baseEnd_941880 < baseStart_941880 := by decide
  rcases family_descends (prefixWord ++ tailWord_941880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941886 : List Nat := [4, 2, 1, 2, 2, 2, 10]
def baseStart_941886 : Nat := 118140960795 + 941886 * 2 ^ 59
def prefixEnd_941886 : Nat := 4983230072969 + 3 ^ 40 * 941886 * 2
def baseEnd_941886 : Nat := 5970867157293914819671

theorem tailTrace_941886 : CollatzResearch.WordTrace tailWord_941886 prefixEnd_941886 5970867157293914819671 := by
  unfold tailWord_941886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294175583214419770885689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22902269777143572111390341 4294175583214419770885689)
  ·
    refine ⟨3220631687410814828164267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4294175583214419770885689 3220631687410814828164267)
    ·
      refine ⟨4830947531116222242246401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3220631687410814828164267 4830947531116222242246401)
      ·
        refine ⟨3623210648337166681684801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830947531116222242246401 3623210648337166681684801)
        ·
          refine ⟨2717407986252875011263601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623210648337166681684801 2717407986252875011263601)
          ·
            refine ⟨2038055989689656258447701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717407986252875011263601 2038055989689656258447701)
            ·
              refine ⟨5970867157293914819671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2038055989689656258447701 5970867157293914819671)
              ·
                rfl

theorem cell23_941886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 10].length) (baseStart_941886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941886 prefixEnd_941886 := by exact prefixLift 941886
  have htrace : WordTrace (prefixWord ++ tailWord_941886) baseStart_941886 baseEnd_941886 := by
    simpa [prefixWord, tailWord_941886, baseEnd_941886] using wordTrace_append hprefix tailTrace_941886
  have hstable : (prefixWord ++ tailWord_941886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941886).length < 2 ^ (prefixWord ++ tailWord_941886).sum := by decide
  have hdescent : baseEnd_941886 < baseStart_941886 := by decide
  rcases family_descends (prefixWord ++ tailWord_941886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941929 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_941929 : Nat := 118140960795 + 941929 * 2 ^ 59
def prefixEnd_941929 : Nat := 4983230072969 + 3 ^ 40 * 941929 * 2
def baseEnd_941929 : Nat := 161220773136316810718551

theorem tailTrace_941929 : CollatzResearch.WordTrace tailWord_941929 prefixEnd_941929 161220773136316810718551 := by
  unfold tailWord_941929
  simp only [CollatzResearch.WordTrace]
  refine ⟨34354973004559576510900841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22903315336373051007267227 34354973004559576510900841)
  ·
    refine ⟨25766229753419682383175631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34354973004559576510900841 25766229753419682383175631)
    ·
      refine ⟨38649344630129523574763447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25766229753419682383175631 38649344630129523574763447)
      ·
        refine ⟨57974016945194285362145171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38649344630129523574763447 57974016945194285362145171)
        ·
          refine ⟨86961025417791428043217757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57974016945194285362145171 86961025417791428043217757)
          ·
            refine ⟨32610384531671785516206659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86961025417791428043217757 32610384531671785516206659)
            ·
              refine ⟨48915576797507678274309989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32610384531671785516206659 48915576797507678274309989)
              ·
                refine ⟨9171670649532689676433123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48915576797507678274309989 9171670649532689676433123)
                ·
                  refine ⟨13757505974299034514649685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171670649532689676433123 13757505974299034514649685)
                  ·
                    refine ⟨161220773136316810718551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13757505974299034514649685 161220773136316810718551)
                    ·
                      rfl

theorem cell23_941929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_941929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_941929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_941929 prefixEnd_941929 := by exact prefixLift 941929
  have htrace : WordTrace (prefixWord ++ tailWord_941929) baseStart_941929 baseEnd_941929 := by
    simpa [prefixWord, tailWord_941929, baseEnd_941929] using wordTrace_append hprefix tailTrace_941929
  have hstable : (prefixWord ++ tailWord_941929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941929).length < 2 ^ (prefixWord ++ tailWord_941929).sum := by decide
  have hdescent : baseEnd_941929 < baseStart_941929 := by decide
  rcases family_descends (prefixWord ++ tailWord_941929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942016 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_942016 : Nat := 118140960795 + 942016 * 2 ^ 59
def prefixEnd_942016 : Nat := 4983230072969 + 3 ^ 40 * 942016 * 2
def baseEnd_942016 : Nat := 483706992225891591767753

theorem tailTrace_942016 : CollatzResearch.WordTrace tailWord_942016 prefixEnd_942016 483706992225891591767753 := by
  unfold tailWord_942016
  simp only [CollatzResearch.WordTrace]
  refine ⟨17179073077622195184658951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22905430770162926912878601 17179073077622195184658951)
  ·
    refine ⟨25768609616433292776988427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17179073077622195184658951 25768609616433292776988427)
    ·
      refine ⟨38652914424649939165482641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768609616433292776988427 38652914424649939165482641)
      ·
        refine ⟨28989685818487454374111981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38652914424649939165482641 28989685818487454374111981)
        ·
          refine ⟨10871132181932795390291993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28989685818487454374111981 10871132181932795390291993)
          ·
            refine ⟨8153349136449596542718995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10871132181932795390291993 8153349136449596542718995)
            ·
              refine ⟨12230023704674394814078493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8153349136449596542718995 12230023704674394814078493)
              ·
                refine ⟨4586258889252898055279435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12230023704674394814078493 4586258889252898055279435)
                ·
                  refine ⟨6879388333879347082919153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586258889252898055279435 6879388333879347082919153)
                  ·
                    refine ⟨5159541250409510312189365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879388333879347082919153 5159541250409510312189365)
                    ·
                      refine ⟨483706992225891591767753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5159541250409510312189365 483706992225891591767753)
                      ·
                        rfl

theorem cell23_942016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_942016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942016 prefixEnd_942016 := by exact prefixLift 942016
  have htrace : WordTrace (prefixWord ++ tailWord_942016) baseStart_942016 baseEnd_942016 := by
    simpa [prefixWord, tailWord_942016, baseEnd_942016] using wordTrace_append hprefix tailTrace_942016
  have hstable : (prefixWord ++ tailWord_942016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942016).length < 2 ^ (prefixWord ++ tailWord_942016).sum := by decide
  have hdescent : baseEnd_942016 < baseStart_942016 := by decide
  rcases family_descends (prefixWord ++ tailWord_942016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942063 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_942063 : Nat := 118140960795 + 942063 * 2 ^ 59
def prefixEnd_942063 : Nat := 4983230072969 + 3 ^ 40 * 942063 * 2
def baseEnd_942063 : Nat := 483731125816652907880037

theorem tailTrace_942063 : CollatzResearch.WordTrace tailWord_942063 prefixEnd_942063 483731125816652907880037 := by
  unfold tailWord_942063
  simp only [CollatzResearch.WordTrace]
  refine ⟨34359860386074117396278843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22906573590716078264185895 34359860386074117396278843)
  ·
    refine ⟨51539790579111176094418265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34359860386074117396278843 51539790579111176094418265)
    ·
      refine ⟨38654842934333382070813699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51539790579111176094418265 38654842934333382070813699)
      ·
        refine ⟨57982264401500073106220549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38654842934333382070813699 57982264401500073106220549)
        ·
          refine ⟨10871674575281263707416353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57982264401500073106220549 10871674575281263707416353)
          ·
            refine ⟨8153755931460947780562265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10871674575281263707416353 8153755931460947780562265)
            ·
              refine ⟨6115316948595710835421699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153755931460947780562265 6115316948595710835421699)
              ·
                refine ⟨9172975422893566253132549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115316948595710835421699 9172975422893566253132549)
                ·
                  refine ⟨1719932891792543672462353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9172975422893566253132549 1719932891792543672462353)
                  ·
                    refine ⟨1289949668844407754346765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719932891792543672462353 1289949668844407754346765)
                    ·
                      refine ⟨483731125816652907880037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1289949668844407754346765 483731125816652907880037)
                      ·
                        rfl

theorem cell23_942063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_942063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942063 prefixEnd_942063 := by exact prefixLift 942063
  have htrace : WordTrace (prefixWord ++ tailWord_942063) baseStart_942063 baseEnd_942063 := by
    simpa [prefixWord, tailWord_942063, baseEnd_942063] using wordTrace_append hprefix tailTrace_942063
  have hstable : (prefixWord ++ tailWord_942063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942063).length < 2 ^ (prefixWord ++ tailWord_942063).sum := by decide
  have hdescent : baseEnd_942063 < baseStart_942063 := by decide
  rcases family_descends (prefixWord ++ tailWord_942063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942200 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_942200 : Nat := 118140960795 + 942200 * 2 ^ 59
def prefixEnd_942200 : Nat := 4983230072969 + 3 ^ 40 * 942200 * 2
def baseEnd_942200 : Nat := 483801472666318871866907

theorem tailTrace_942200 : CollatzResearch.WordTrace tailWord_942200 prefixEnd_942200 483801472666318871866907 := by
  unfold tailWord_942200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182428593288894897008027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22909904791051859862677369 17182428593288894897008027)
  ·
    refine ⟨25773642889933342345512041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182428593288894897008027 25773642889933342345512041)
    ·
      refine ⟨19330232167450006759134031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25773642889933342345512041 19330232167450006759134031)
      ·
        refine ⟨28995348251175010138701047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19330232167450006759134031 28995348251175010138701047)
        ·
          refine ⟨43493022376762515208051571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28995348251175010138701047 43493022376762515208051571)
          ·
            refine ⟨65239533565143772812077357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43493022376762515208051571 65239533565143772812077357)
            ·
              refine ⟨24464825086928914804529009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65239533565143772812077357 24464825086928914804529009)
              ·
                refine ⟨18348618815196686103396757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24464825086928914804529009 18348618815196686103396757)
                ·
                  refine ⟨860091506962344661096723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18348618815196686103396757 860091506962344661096723)
                  ·
                    refine ⟨1290137260443516991645085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860091506962344661096723 1290137260443516991645085)
                    ·
                      refine ⟨483801472666318871866907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290137260443516991645085 483801472666318871866907)
                      ·
                        rfl

theorem cell23_942200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_942200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942200 prefixEnd_942200 := by exact prefixLift 942200
  have htrace : WordTrace (prefixWord ++ tailWord_942200) baseStart_942200 baseEnd_942200 := by
    simpa [prefixWord, tailWord_942200, baseEnd_942200] using wordTrace_append hprefix tailTrace_942200
  have hstable : (prefixWord ++ tailWord_942200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942200).length < 2 ^ (prefixWord ++ tailWord_942200).sum := by decide
  have hdescent : baseEnd_942200 < baseStart_942200 := by decide
  rcases family_descends (prefixWord ++ tailWord_942200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942228 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_942228 : Nat := 118140960795 + 942228 * 2 ^ 59
def prefixEnd_942228 : Nat := 4983230072969 + 3 ^ 40 * 942228 * 2
def baseEnd_942228 : Nat := 161271950041548254105593

theorem tailTrace_942228 : CollatzResearch.WordTrace tailWord_942228 prefixEnd_942228 161271950041548254105593 := by
  unfold tailWord_942228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182939215238175288017669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22910585620317567050690225 17182939215238175288017669)
  ·
    refine ⟨3221801102857157866503313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17182939215238175288017669 3221801102857157866503313)
    ·
      refine ⟨2416350827142868399877485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3221801102857157866503313 2416350827142868399877485)
      ·
        refine ⟨906131560178575649954057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2416350827142868399877485 906131560178575649954057)
        ·
          refine ⟨679598670133931737465543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906131560178575649954057 679598670133931737465543)
          ·
            refine ⟨1019398005200897606198315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679598670133931737465543 1019398005200897606198315)
            ·
              refine ⟨1529097007801346409297473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019398005200897606198315 1529097007801346409297473)
              ·
                refine ⟨1146822755851009806973105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529097007801346409297473 1146822755851009806973105)
                ·
                  refine ⟨860117066888257355229829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1146822755851009806973105 860117066888257355229829)
                  ·
                    refine ⟨161271950041548254105593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 860117066888257355229829 161271950041548254105593)
                    ·
                      rfl

theorem cell23_942228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_942228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942228 prefixEnd_942228 := by exact prefixLift 942228
  have htrace : WordTrace (prefixWord ++ tailWord_942228) baseStart_942228 baseEnd_942228 := by
    simpa [prefixWord, tailWord_942228, baseEnd_942228] using wordTrace_append hprefix tailTrace_942228
  have hstable : (prefixWord ++ tailWord_942228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942228).length < 2 ^ (prefixWord ++ tailWord_942228).sum := by decide
  have hdescent : baseEnd_942228 < baseStart_942228 := by decide
  rcases family_descends (prefixWord ++ tailWord_942228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942234 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_942234 : Nat := 118140960795 + 942234 * 2 ^ 59
def prefixEnd_942234 : Nat := 4983230072969 + 3 ^ 40 * 942234 * 2
def baseEnd_942234 : Nat := 483818931008571738841751

theorem tailTrace_942234 : CollatzResearch.WordTrace tailWord_942234 prefixEnd_942234 483818931008571738841751 := by
  unfold tailWord_942234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591524317113653400188439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22910731512303075733835837 8591524317113653400188439)
  ·
    refine ⟨12887286475670480100282659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591524317113653400188439 12887286475670480100282659)
    ·
      refine ⟨19330929713505720150423989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12887286475670480100282659 19330929713505720150423989)
      ·
        refine ⟨1812274660641161264102249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19330929713505720150423989 1812274660641161264102249)
        ·
          refine ⟨1359205995480870948076687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812274660641161264102249 1359205995480870948076687)
          ·
            refine ⟨2038808993221306422115031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359205995480870948076687 2038808993221306422115031)
            ·
              refine ⟨3058213489831959633172547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038808993221306422115031 3058213489831959633172547)
              ·
                refine ⟨4587320234747939449758821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058213489831959633172547 4587320234747939449758821)
                ·
                  refine ⟨860122544015238646829779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4587320234747939449758821 860122544015238646829779)
                  ·
                    refine ⟨1290183816022857970244669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860122544015238646829779 1290183816022857970244669)
                    ·
                      refine ⟨483818931008571738841751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290183816022857970244669 483818931008571738841751)
                      ·
                        rfl

theorem cell23_942234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_942234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942234 prefixEnd_942234 := by exact prefixLift 942234
  have htrace : WordTrace (prefixWord ++ tailWord_942234) baseStart_942234 baseEnd_942234 := by
    simpa [prefixWord, tailWord_942234, baseEnd_942234] using wordTrace_append hprefix tailTrace_942234
  have hstable : (prefixWord ++ tailWord_942234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942234).length < 2 ^ (prefixWord ++ tailWord_942234).sum := by decide
  have hdescent : baseEnd_942234 < baseStart_942234 := by decide
  rcases family_descends (prefixWord ++ tailWord_942234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942243 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_942243 : Nat := 118140960795 + 942243 * 2 ^ 59
def prefixEnd_942243 : Nat := 4983230072969 + 3 ^ 40 * 942243 * 2
def baseEnd_942243 : Nat := 483823552334462203629209

theorem tailTrace_942243 : CollatzResearch.WordTrace tailWord_942243 prefixEnd_942243 483823552334462203629209 := by
  unfold tailWord_942243
  simp only [CollatzResearch.WordTrace]
  refine ⟨34366425525422008137831383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22910950350281338758554255 34366425525422008137831383)
  ·
    refine ⟨51549638288133012206747075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34366425525422008137831383 51549638288133012206747075)
    ·
      refine ⟨77324457432199518310120613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51549638288133012206747075 77324457432199518310120613)
      ·
        refine ⟨14498335768537409683147615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77324457432199518310120613 14498335768537409683147615)
        ·
          refine ⟨21747503652806114524721423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14498335768537409683147615 21747503652806114524721423)
          ·
            refine ⟨32621255479209171787082135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21747503652806114524721423 32621255479209171787082135)
            ·
              refine ⟨48931883218813757680623203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32621255479209171787082135 48931883218813757680623203)
              ·
                refine ⟨73397824828220636520934805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48931883218813757680623203 73397824828220636520934805)
                ·
                  refine ⟨3440523038822842336918819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73397824828220636520934805 3440523038822842336918819)
                  ·
                    refine ⟨5160784558234263505378229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440523038822842336918819 5160784558234263505378229)
                    ·
                      refine ⟨483823552334462203629209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5160784558234263505378229 483823552334462203629209)
                      ·
                        rfl

theorem cell23_942243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_942243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942243 prefixEnd_942243 := by exact prefixLift 942243
  have htrace : WordTrace (prefixWord ++ tailWord_942243) baseStart_942243 baseEnd_942243 := by
    simpa [prefixWord, tailWord_942243, baseEnd_942243] using wordTrace_append hprefix tailTrace_942243
  have hstable : (prefixWord ++ tailWord_942243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942243).length < 2 ^ (prefixWord ++ tailWord_942243).sum := by decide
  have hdescent : baseEnd_942243 < baseStart_942243 := by decide
  rcases family_descends (prefixWord ++ tailWord_942243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942347 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 2, 4, 2]
def baseStart_942347 : Nat := 118140960795 + 942347 * 2 ^ 59
def prefixEnd_942347 : Nat := 4983230072969 + 3 ^ 40 * 942347 * 2
def baseEnd_942347 : Nat := 483876954322529796728731

theorem tailTrace_942347 : CollatzResearch.WordTrace tailWord_942347 prefixEnd_942347 483876954322529796728731 := by
  unfold tailWord_942347
  simp only [CollatzResearch.WordTrace]
  refine ⟨34370218717045233899617295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22913479144696822599744863 34370218717045233899617295)
  ·
    refine ⟨51555328075567850849425943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34370218717045233899617295 51555328075567850849425943)
    ·
      refine ⟨77332992113351776274138915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51555328075567850849425943 77332992113351776274138915)
      ·
        refine ⟨115999488170027664411208373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77332992113351776274138915 115999488170027664411208373)
        ·
          refine ⟨10874952015940093538550785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115999488170027664411208373 10874952015940093538550785)
          ·
            refine ⟨8156214011955070153913089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10874952015940093538550785 8156214011955070153913089)
            ·
              refine ⟨6117160508966302615434817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8156214011955070153913089 6117160508966302615434817)
              ·
                refine ⟨4587870381724726961576113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117160508966302615434817 4587870381724726961576113)
                ·
                  refine ⟨3440902786293545221182085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4587870381724726961576113 3440902786293545221182085)
                  ·
                    refine ⟨645169272430039728971641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3440902786293545221182085 645169272430039728971641)
                    ·
                      refine ⟨483876954322529796728731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645169272430039728971641 483876954322529796728731)
                      ·
                        rfl

theorem cell23_942347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4, 2].length) (baseStart_942347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942347 prefixEnd_942347 := by exact prefixLift 942347
  have htrace : WordTrace (prefixWord ++ tailWord_942347) baseStart_942347 baseEnd_942347 := by
    simpa [prefixWord, tailWord_942347, baseEnd_942347] using wordTrace_append hprefix tailTrace_942347
  have hstable : (prefixWord ++ tailWord_942347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942347).length < 2 ^ (prefixWord ++ tailWord_942347).sum := by decide
  have hdescent : baseEnd_942347 < baseStart_942347 := by decide
  rcases family_descends (prefixWord ++ tailWord_942347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942350 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_942350 : Nat := 118140960795 + 942350 * 2 ^ 59
def prefixEnd_942350 : Nat := 4983230072969 + 3 ^ 40 * 942350 * 2
def baseEnd_942350 : Nat := 483878494764493284991217

theorem tailTrace_942350 : CollatzResearch.WordTrace tailWord_942350 prefixEnd_942350 483878494764493284991217 := by
  unfold tailWord_942350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296291017004295676497063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22913552090689576941317669 4296291017004295676497063)
  ·
    refine ⟨6444436525506443514745595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296291017004295676497063 6444436525506443514745595)
    ·
      refine ⟨9666654788259665272118393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444436525506443514745595 9666654788259665272118393)
      ·
        refine ⟨7249991091194748954088795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9666654788259665272118393 7249991091194748954088795)
        ·
          refine ⟨10874986636792123431133193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249991091194748954088795 10874986636792123431133193)
          ·
            refine ⟨8156239977594092573349895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10874986636792123431133193 8156239977594092573349895)
            ·
              refine ⟨12234359966391138860024843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156239977594092573349895 12234359966391138860024843)
              ·
                refine ⟨18351539949586708290037265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234359966391138860024843 18351539949586708290037265)
                ·
                  refine ⟨13763654962190031217527949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18351539949586708290037265 13763654962190031217527949)
                  ·
                    refine ⟨5161370610821261706572981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13763654962190031217527949 5161370610821261706572981)
                    ·
                      refine ⟨483878494764493284991217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5161370610821261706572981 483878494764493284991217)
                      ·
                        rfl

theorem cell23_942350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_942350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942350 prefixEnd_942350 := by exact prefixLift 942350
  have htrace : WordTrace (prefixWord ++ tailWord_942350) baseStart_942350 baseEnd_942350 := by
    simpa [prefixWord, tailWord_942350, baseEnd_942350] using wordTrace_append hprefix tailTrace_942350
  have hstable : (prefixWord ++ tailWord_942350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942350).length < 2 ^ (prefixWord ++ tailWord_942350).sum := by decide
  have hdescent : baseEnd_942350 < baseStart_942350 := by decide
  rcases family_descends (prefixWord ++ tailWord_942350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942400 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_942400 : Nat := 118140960795 + 942400 * 2 ^ 59
def prefixEnd_942400 : Nat := 4983230072969 + 3 ^ 40 * 942400 * 2
def baseEnd_942400 : Nat := 161301389599072696455329

theorem tailTrace_942400 : CollatzResearch.WordTrace tailWord_942400 prefixEnd_942400 161301389599072696455329 := by
  unfold tailWord_942400
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186075892926611975648327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22914767857235482634197769 17186075892926611975648327)
  ·
    refine ⟨25779113839389917963472491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17186075892926611975648327 25779113839389917963472491)
    ·
      refine ⟨38668670759084876945208737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25779113839389917963472491 38668670759084876945208737)
      ·
        refine ⟨29001503069313657708906553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38668670759084876945208737 29001503069313657708906553)
        ·
          refine ⟨21751127301985243281679915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29001503069313657708906553 21751127301985243281679915)
          ·
            refine ⟨32626690952977864922519873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21751127301985243281679915 32626690952977864922519873)
            ·
              refine ⟨24470018214733398691889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32626690952977864922519873 24470018214733398691889905)
              ·
                refine ⟨18352513661050049018917429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24470018214733398691889905 18352513661050049018917429)
                ·
                  refine ⟨1720548155723442095523509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18352513661050049018917429 1720548155723442095523509)
                  ·
                    refine ⟨161301389599072696455329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1720548155723442095523509 161301389599072696455329)
                    ·
                      rfl

theorem cell23_942400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_942400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942400 prefixEnd_942400 := by exact prefixLift 942400
  have htrace : WordTrace (prefixWord ++ tailWord_942400) baseStart_942400 baseEnd_942400 := by
    simpa [prefixWord, tailWord_942400, baseEnd_942400] using wordTrace_append hprefix tailTrace_942400
  have hstable : (prefixWord ++ tailWord_942400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942400).length < 2 ^ (prefixWord ++ tailWord_942400).sum := by decide
  have hdescent : baseEnd_942400 < baseStart_942400 := by decide
  rcases family_descends (prefixWord ++ tailWord_942400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942404 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 8]
def baseStart_942404 : Nat := 118140960795 + 942404 * 2 ^ 59
def prefixEnd_942404 : Nat := 4983230072969 + 3 ^ 40 * 942404 * 2
def baseEnd_942404 : Nat := 53767358079981785968441

theorem tailTrace_942404 : CollatzResearch.WordTrace tailWord_942404 prefixEnd_942404 53767358079981785968441 := by
  unfold tailWord_942404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186148838919366317221133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22914865118559155089628177 17186148838919366317221133)
  ·
    refine ⟨6444805814594762368957925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17186148838919366317221133 6444805814594762368957925)
    ·
      refine ⟨1208401090236517944179611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6444805814594762368957925 1208401090236517944179611)
      ·
        refine ⟨1812601635354776916269417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208401090236517944179611 1812601635354776916269417)
        ·
          refine ⟨1359451226516082687202063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812601635354776916269417 1359451226516082687202063)
          ·
            refine ⟨2039176839774124030803095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359451226516082687202063 2039176839774124030803095)
            ·
              refine ⟨3058765259661186046204643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039176839774124030803095 3058765259661186046204643)
              ·
                refine ⟨4588147889491779069306965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058765259661186046204643 4588147889491779069306965)
                ·
                  refine ⟨53767358079981785968441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4588147889491779069306965 53767358079981785968441)
                  ·
                    rfl

theorem cell23_942404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_942404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942404 prefixEnd_942404 := by exact prefixLift 942404
  have htrace : WordTrace (prefixWord ++ tailWord_942404) baseStart_942404 baseEnd_942404 := by
    simpa [prefixWord, tailWord_942404, baseEnd_942404] using wordTrace_append hprefix tailTrace_942404
  have hstable : (prefixWord ++ tailWord_942404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942404).length < 2 ^ (prefixWord ++ tailWord_942404).sum := by decide
  have hdescent : baseEnd_942404 < baseStart_942404 := by decide
  rcases family_descends (prefixWord ++ tailWord_942404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942434 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_942434 : Nat := 118140960795 + 942434 * 2 ^ 59
def prefixEnd_942434 : Nat := 4983230072969 + 3 ^ 40 * 942434 * 2
def baseEnd_942434 : Nat := 161307209046490318780277

theorem tailTrace_942434 : CollatzResearch.WordTrace tailWord_942434 prefixEnd_942434 161307209046490318780277 := by
  unfold tailWord_942434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8593347966932511939508589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22915594578486698505356237 8593347966932511939508589)
  ·
    refine ⟨3222505487599691977315721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8593347966932511939508589 3222505487599691977315721)
    ·
      refine ⟨2416879115699768982986791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3222505487599691977315721 2416879115699768982986791)
      ·
        refine ⟨3625318673549653474480187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416879115699768982986791 3625318673549653474480187)
        ·
          refine ⟨5437978010324480211720281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625318673549653474480187 5437978010324480211720281)
          ·
            refine ⟨4078483507743360158790211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5437978010324480211720281 4078483507743360158790211)
            ·
              refine ⟨6117725261615040238185317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078483507743360158790211 6117725261615040238185317)
              ·
                refine ⟨1147073486552820044659747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6117725261615040238185317 1147073486552820044659747)
                ·
                  refine ⟨1720610229829230066989621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147073486552820044659747 1720610229829230066989621)
                  ·
                    refine ⟨161307209046490318780277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1720610229829230066989621 161307209046490318780277)
                    ·
                      rfl

theorem cell23_942434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_942434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942434 prefixEnd_942434 := by exact prefixLift 942434
  have htrace : WordTrace (prefixWord ++ tailWord_942434) baseStart_942434 baseEnd_942434 := by
    simpa [prefixWord, tailWord_942434, baseEnd_942434] using wordTrace_append hprefix tailTrace_942434
  have hstable : (prefixWord ++ tailWord_942434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942434).length < 2 ^ (prefixWord ++ tailWord_942434).sum := by decide
  have hdescent : baseEnd_942434 < baseStart_942434 := by decide
  rcases family_descends (prefixWord ++ tailWord_942434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942448 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 1, 1, 3]
def baseStart_942448 : Nat := 118140960795 + 942448 * 2 ^ 59
def prefixEnd_942448 : Nat := 4983230072969 + 3 ^ 40 * 942448 * 2
def baseEnd_942448 : Nat := 483928815868633901565767

theorem tailTrace_942448 : CollatzResearch.WordTrace tailWord_942448 prefixEnd_942448 483928815868633901565767 := by
  unfold tailWord_942448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186951244839664074521999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22915934993119552099362665 17186951244839664074521999)
  ·
    refine ⟨25780426867259496111782999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17186951244839664074521999 25780426867259496111782999)
    ·
      refine ⟨38670640300889244167674499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25780426867259496111782999 38670640300889244167674499)
      ·
        refine ⟨58005960451333866251511749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38670640300889244167674499 58005960451333866251511749)
        ·
          refine ⟨10876117584625099922158453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58005960451333866251511749 10876117584625099922158453)
          ·
            refine ⟨1019636023558603117702355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10876117584625099922158453 1019636023558603117702355)
            ·
              refine ⟨1529454035337904676553533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019636023558603117702355 1529454035337904676553533)
              ·
                refine ⟨573545263251714253707575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1529454035337904676553533 573545263251714253707575)
                ·
                  refine ⟨860317894877571380561363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573545263251714253707575 860317894877571380561363)
                  ·
                    refine ⟨1290476842316357070842045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860317894877571380561363 1290476842316357070842045)
                    ·
                      refine ⟨483928815868633901565767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290476842316357070842045 483928815868633901565767)
                      ·
                        rfl

theorem cell23_942448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 1, 3].length) (baseStart_942448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942448 prefixEnd_942448 := by exact prefixLift 942448
  have htrace : WordTrace (prefixWord ++ tailWord_942448) baseStart_942448 baseEnd_942448 := by
    simpa [prefixWord, tailWord_942448, baseEnd_942448] using wordTrace_append hprefix tailTrace_942448
  have hstable : (prefixWord ++ tailWord_942448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942448).length < 2 ^ (prefixWord ++ tailWord_942448).sum := by decide
  have hdescent : baseEnd_942448 < baseStart_942448 := by decide
  rcases family_descends (prefixWord ++ tailWord_942448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942457 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_942457 : Nat := 118140960795 + 942457 * 2 ^ 59
def prefixEnd_942457 : Nat := 4983230072969 + 3 ^ 40 * 942457 * 2
def baseEnd_942457 : Nat := 483933437194524366353225

theorem tailTrace_942457 : CollatzResearch.WordTrace tailWord_942457 prefixEnd_942457 483933437194524366353225 := by
  unfold tailWord_942457
  simp only [CollatzResearch.WordTrace]
  refine ⟨34374230746646722686121625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22916153831097815124081083 34374230746646722686121625)
  ·
    refine ⟨25780673059985042014591219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34374230746646722686121625 25780673059985042014591219)
    ·
      refine ⟨38671009589977563021886829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25780673059985042014591219 38671009589977563021886829)
      ·
        refine ⟨14501628596241586133207561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38671009589977563021886829 14501628596241586133207561)
        ·
          refine ⟨10876221447181189599905671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14501628596241586133207561 10876221447181189599905671)
          ·
            refine ⟨16314332170771784399858507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10876221447181189599905671 16314332170771784399858507)
            ·
              refine ⟨24471498256157676599787761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16314332170771784399858507 24471498256157676599787761)
              ·
                refine ⟨18353623692118257449840821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24471498256157676599787761 18353623692118257449840821)
                ·
                  refine ⟨1720652221136086635922577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18353623692118257449840821 1720652221136086635922577)
                  ·
                    refine ⟨1290489165852064976941933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1720652221136086635922577 1290489165852064976941933)
                    ·
                      refine ⟨483933437194524366353225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290489165852064976941933 483933437194524366353225)
                      ·
                        rfl

theorem cell23_942457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_942457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942457 prefixEnd_942457 := by exact prefixLift 942457
  have htrace : WordTrace (prefixWord ++ tailWord_942457) baseStart_942457 baseEnd_942457 := by
    simpa [prefixWord, tailWord_942457, baseEnd_942457] using wordTrace_append hprefix tailTrace_942457
  have hstable : (prefixWord ++ tailWord_942457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942457).length < 2 ^ (prefixWord ++ tailWord_942457).sum := by decide
  have hdescent : baseEnd_942457 < baseStart_942457 := by decide
  rcases family_descends (prefixWord ++ tailWord_942457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942465 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_942465 : Nat := 118140960795 + 942465 * 2 ^ 59
def prefixEnd_942465 : Nat := 4983230072969 + 3 ^ 40 * 942465 * 2
def baseEnd_942465 : Nat := 483937545039760335053189

theorem tailTrace_942465 : CollatzResearch.WordTrace tailWord_942465 prefixEnd_942465 483937545039760335053189 := by
  unfold tailWord_942465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34374522530617740052412849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22916348353745160034941899 34374522530617740052412849)
  ·
    refine ⟨25780891897963305039309637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34374522530617740052412849 25780891897963305039309637)
    ·
      refine ⟨4833917230868119694870557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25780891897963305039309637 4833917230868119694870557)
      ·
        refine ⟨1812718961575544885576459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4833917230868119694870557 1812718961575544885576459)
        ·
          refine ⟨2719078442363317328364689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812718961575544885576459 2719078442363317328364689)
          ·
            refine ⟨2039308831772487996273517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719078442363317328364689 2039308831772487996273517)
            ·
              refine ⟨764740811914682998602569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039308831772487996273517 764740811914682998602569)
              ·
                refine ⟨573555608936012248951927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764740811914682998602569 573555608936012248951927)
                ·
                  refine ⟨860333413404018373427891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573555608936012248951927 860333413404018373427891)
                  ·
                    refine ⟨1290500120106027560141837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860333413404018373427891 1290500120106027560141837)
                    ·
                      refine ⟨483937545039760335053189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290500120106027560141837 483937545039760335053189)
                      ·
                        rfl

theorem cell23_942465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_942465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942465 prefixEnd_942465 := by exact prefixLift 942465
  have htrace : WordTrace (prefixWord ++ tailWord_942465) baseStart_942465 baseEnd_942465 := by
    simpa [prefixWord, tailWord_942465, baseEnd_942465] using wordTrace_append hprefix tailTrace_942465
  have hstable : (prefixWord ++ tailWord_942465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942465).length < 2 ^ (prefixWord ++ tailWord_942465).sum := by decide
  have hdescent : baseEnd_942465 < baseStart_942465 := by decide
  rcases family_descends (prefixWord ++ tailWord_942465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942494 : List Nat := [4, 3, 1, 2, 1, 1, 2, 9]
def baseStart_942494 : Nat := 118140960795 + 942494 * 2 ^ 59
def prefixEnd_942494 : Nat := 4983230072969 + 3 ^ 40 * 942494 * 2
def baseEnd_942494 : Nat := 17924164295508915614465

theorem tailTrace_942494 : CollatzResearch.WordTrace tailWord_942494 prefixEnd_942494 17924164295508915614465 := by
  unfold tailWord_942494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296947530939084750652317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22917053498341785336812357 4296947530939084750652317)
  ·
    refine ⟨1611355324102156781494619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4296947530939084750652317 1611355324102156781494619)
    ·
      refine ⟨2417032986153235172241929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611355324102156781494619 2417032986153235172241929)
      ·
        refine ⟨1812774739614926379181447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2417032986153235172241929 1812774739614926379181447)
        ·
          refine ⟨2719162109422389568772171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812774739614926379181447 2719162109422389568772171)
          ·
            refine ⟨4078743164133584353158257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719162109422389568772171 4078743164133584353158257)
            ·
              refine ⟨3059057373100188264868693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4078743164133584353158257 3059057373100188264868693)
              ·
                refine ⟨17924164295508915614465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3059057373100188264868693 17924164295508915614465)
                ·
                  rfl

theorem cell23_942494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_942494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942494 prefixEnd_942494 := by exact prefixLift 942494
  have htrace : WordTrace (prefixWord ++ tailWord_942494) baseStart_942494 baseEnd_942494 := by
    simpa [prefixWord, tailWord_942494, baseEnd_942494] using wordTrace_append hprefix tailTrace_942494
  have hstable : (prefixWord ++ tailWord_942494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942494).length < 2 ^ (prefixWord ++ tailWord_942494).sum := by decide
  have hdescent : baseEnd_942494 < baseStart_942494 := by decide
  rcases family_descends (prefixWord ++ tailWord_942494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942516 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_942516 : Nat := 118140960795 + 942516 * 2 ^ 59
def prefixEnd_942516 : Nat := 4983230072969 + 3 ^ 40 * 942516 * 2
def baseEnd_942516 : Nat := 483963732553139635515455

theorem tailTrace_942516 : CollatzResearch.WordTrace tailWord_942516 prefixEnd_942516 483963732553139635515455 := by
  unfold tailWord_942516
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188191326716487881259701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22917588435621983841679601 17188191326716487881259701)
  ·
    refine ⟨1611392936879670738868097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17188191326716487881259701 1611392936879670738868097)
    ·
      refine ⟨1208544702659753054151073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1611392936879670738868097 1208544702659753054151073)
      ·
        refine ⟨906408526994814790613305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208544702659753054151073 906408526994814790613305)
        ·
          refine ⟨679806395246111092959979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906408526994814790613305 679806395246111092959979)
          ·
            refine ⟨1019709592869166639439969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679806395246111092959979 1019709592869166639439969)
            ·
              refine ⟨764782194651874979579977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019709592869166639439969 764782194651874979579977)
              ·
                refine ⟨573586645988906234684983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764782194651874979579977 573586645988906234684983)
                ·
                  refine ⟨860379968983359352027475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573586645988906234684983 860379968983359352027475)
                  ·
                    refine ⟨1290569953475039028041213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860379968983359352027475 1290569953475039028041213)
                    ·
                      refine ⟨483963732553139635515455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290569953475039028041213 483963732553139635515455)
                      ·
                        rfl

theorem cell23_942516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_942516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942516 prefixEnd_942516 := by exact prefixLift 942516
  have htrace : WordTrace (prefixWord ++ tailWord_942516) baseStart_942516 baseEnd_942516 := by
    simpa [prefixWord, tailWord_942516, baseEnd_942516] using wordTrace_append hprefix tailTrace_942516
  have hstable : (prefixWord ++ tailWord_942516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942516).length < 2 ^ (prefixWord ++ tailWord_942516).sum := by decide
  have hdescent : baseEnd_942516 < baseStart_942516 := by decide
  rcases family_descends (prefixWord ++ tailWord_942516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942521 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 3]
def baseStart_942521 : Nat := 118140960795 + 942521 * 2 ^ 59
def prefixEnd_942521 : Nat := 4983230072969 + 3 ^ 40 * 942521 * 2
def baseEnd_942521 : Nat := 483966299956412115952931

theorem tailTrace_942521 : CollatzResearch.WordTrace tailWord_942521 prefixEnd_942521 483966299956412115952931 := by
  unfold tailWord_942521
  simp only [CollatzResearch.WordTrace]
  refine ⟨34376565018414861616451417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22917710012276574410967611 34376565018414861616451417)
  ·
    refine ⟨25782423763811146212338563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34376565018414861616451417 25782423763811146212338563)
    ·
      refine ⟨38673635645716719318507845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25782423763811146212338563 38673635645716719318507845)
      ·
        refine ⟨7251306683571884872220221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38673635645716719318507845 7251306683571884872220221)
        ·
          refine ⟨2719240006339456827082583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7251306683571884872220221 2719240006339456827082583)
          ·
            refine ⟨4078860009509185240623875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719240006339456827082583 4078860009509185240623875)
            ·
              refine ⟨6118290014263777860935813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078860009509185240623875 6118290014263777860935813)
              ·
                refine ⟨1147179377674458348925465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6118290014263777860935813 1147179377674458348925465)
                ·
                  refine ⟨860384533255843761694099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147179377674458348925465 860384533255843761694099)
                  ·
                    refine ⟨1290576799883765642541149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860384533255843761694099 1290576799883765642541149)
                    ·
                      refine ⟨483966299956412115952931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290576799883765642541149 483966299956412115952931)
                      ·
                        rfl

theorem cell23_942521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_942521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942521 prefixEnd_942521 := by exact prefixLift 942521
  have htrace : WordTrace (prefixWord ++ tailWord_942521) baseStart_942521 baseEnd_942521 := by
    simpa [prefixWord, tailWord_942521, baseEnd_942521] using wordTrace_append hprefix tailTrace_942521
  have hstable : (prefixWord ++ tailWord_942521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942521).length < 2 ^ (prefixWord ++ tailWord_942521).sum := by decide
  have hdescent : baseEnd_942521 < baseStart_942521 := by decide
  rcases family_descends (prefixWord ++ tailWord_942521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942561 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_942561 : Nat := 118140960795 + 942561 * 2 ^ 59
def prefixEnd_942561 : Nat := 4983230072969 + 3 ^ 40 * 942561 * 2
def baseEnd_942561 : Nat := 483986839182591959452747

theorem tailTrace_942561 : CollatzResearch.WordTrace tailWord_942561 prefixEnd_942561 483986839182591959452747 := by
  unfold tailWord_942561
  simp only [CollatzResearch.WordTrace]
  refine ⟨34378023938269948447907537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22918682625513298965271691 34378023938269948447907537)
  ·
    refine ⟨25783517953702461335930653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34378023938269948447907537 25783517953702461335930653)
    ·
      refine ⟨9668819232638423000973995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25783517953702461335930653 9668819232638423000973995)
      ·
        refine ⟨14503228848957634501460993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9668819232638423000973995 14503228848957634501460993)
        ·
          refine ⟨10877421636718225876095745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14503228848957634501460993 10877421636718225876095745)
          ·
            refine ⟨8158066227538669407071809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10877421636718225876095745 8158066227538669407071809)
            ·
              refine ⟨6118549670654002055303857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158066227538669407071809 6118549670654002055303857)
              ·
                refine ⟨4588912252990501541477893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118549670654002055303857 4588912252990501541477893)
                ·
                  refine ⟨860421047435719039027105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4588912252990501541477893 860421047435719039027105)
                  ·
                    refine ⟨645315785576789279270329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 860421047435719039027105 645315785576789279270329)
                    ·
                      refine ⟨483986839182591959452747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645315785576789279270329 483986839182591959452747)
                      ·
                        rfl

theorem cell23_942561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_942561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942561 prefixEnd_942561 := by exact prefixLift 942561
  have htrace : WordTrace (prefixWord ++ tailWord_942561) baseStart_942561 baseEnd_942561 := by
    simpa [prefixWord, tailWord_942561, baseEnd_942561] using wordTrace_append hprefix tailTrace_942561
  have hstable : (prefixWord ++ tailWord_942561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942561).length < 2 ^ (prefixWord ++ tailWord_942561).sum := by decide
  have hdescent : baseEnd_942561 < baseStart_942561 := by decide
  rcases family_descends (prefixWord ++ tailWord_942561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942567 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 9]
def baseStart_942567 : Nat := 118140960795 + 942567 * 2 ^ 59
def prefixEnd_942567 : Nat := 4983230072969 + 3 ^ 40 * 942567 * 2
def baseEnd_942567 : Nat := 53776657785168770664191

theorem tailTrace_942567 : CollatzResearch.WordTrace tailWord_942567 prefixEnd_942567 53776657785168770664191 := by
  unfold tailWord_942567
  simp only [CollatzResearch.WordTrace]
  refine ⟨34378242776248211472625955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22918828517498807648417303 34378242776248211472625955)
  ·
    refine ⟨51567364164372317208938933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34378242776248211472625955 51567364164372317208938933)
    ·
      refine ⟨4834440390409904738338025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51567364164372317208938933 4834440390409904738338025)
      ·
        refine ⟨3625830292807428553753519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4834440390409904738338025 3625830292807428553753519)
        ·
          refine ⟨5438745439211142830630279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625830292807428553753519 5438745439211142830630279)
          ·
            refine ⟨8158118158816714245945419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438745439211142830630279 8158118158816714245945419)
            ·
              refine ⟨12237177238225071368918129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158118158816714245945419 12237177238225071368918129)
              ·
                refine ⟨9177882928668803526688597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12237177238225071368918129 9177882928668803526688597)
                ·
                  refine ⟨53776657785168770664191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9177882928668803526688597 53776657785168770664191)
                  ·
                    rfl

theorem cell23_942567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 9].length) (baseStart_942567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942567 prefixEnd_942567 := by exact prefixLift 942567
  have htrace : WordTrace (prefixWord ++ tailWord_942567) baseStart_942567 baseEnd_942567 := by
    simpa [prefixWord, tailWord_942567, baseEnd_942567] using wordTrace_append hprefix tailTrace_942567
  have hstable : (prefixWord ++ tailWord_942567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942567).length < 2 ^ (prefixWord ++ tailWord_942567).sum := by decide
  have hdescent : baseEnd_942567 < baseStart_942567 := by decide
  rcases family_descends (prefixWord ++ tailWord_942567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942574 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_942574 : Nat := 118140960795 + 942574 * 2 ^ 59
def prefixEnd_942574 : Nat := 4983230072969 + 3 ^ 40 * 942574 * 2
def baseEnd_942574 : Nat := 483993514431100408590187

theorem tailTrace_942574 : CollatzResearch.WordTrace tailWord_942574 prefixEnd_942574 483993514431100408590187 := by
  unfold tailWord_942574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297312260902856458516347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22918998724815234445420517 4297312260902856458516347)
  ·
    refine ⟨6445968391354284687774521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4297312260902856458516347 6445968391354284687774521)
    ·
      refine ⟨4834476293515713515830891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6445968391354284687774521 4834476293515713515830891)
      ·
        refine ⟨7251714440273570273746337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834476293515713515830891 7251714440273570273746337)
        ·
          refine ⟨5438785830205177705309753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7251714440273570273746337 5438785830205177705309753)
          ·
            refine ⟨4079089372653883278982315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5438785830205177705309753 4079089372653883278982315)
            ·
              refine ⟨6118634058980824918473473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079089372653883278982315 6118634058980824918473473)
              ·
                refine ⟨4588975544235618688855105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118634058980824918473473 4588975544235618688855105)
                ·
                  refine ⟨3441731658176714016641329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588975544235618688855105 3441731658176714016641329)
                  ·
                    refine ⟨2581298743632535512480997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441731658176714016641329 2581298743632535512480997)
                    ·
                      refine ⟨483993514431100408590187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2581298743632535512480997 483993514431100408590187)
                      ·
                        rfl

theorem cell23_942574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_942574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942574 prefixEnd_942574 := by exact prefixLift 942574
  have htrace : WordTrace (prefixWord ++ tailWord_942574) baseStart_942574 baseEnd_942574 := by
    simpa [prefixWord, tailWord_942574, baseEnd_942574] using wordTrace_append hprefix tailTrace_942574
  have hstable : (prefixWord ++ tailWord_942574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942574).length < 2 ^ (prefixWord ++ tailWord_942574).sum := by decide
  have hdescent : baseEnd_942574 < baseStart_942574 := by decide
  rcases family_descends (prefixWord ++ tailWord_942574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942584 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 5]
def baseStart_942584 : Nat := 118140960795 + 942584 * 2 ^ 59
def prefixEnd_942584 : Nat := 4983230072969 + 3 ^ 40 * 942584 * 2
def baseEnd_942584 : Nat := 53777627693071707718349

theorem tailTrace_942584 : CollatzResearch.WordTrace tailWord_942584 prefixEnd_942584 53777627693071707718349 := by
  unfold tailWord_942584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17189431408593311687997403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22919241878124415583996537 17189431408593311687997403)
  ·
    refine ⟨25784147112889967531996105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17189431408593311687997403 25784147112889967531996105)
    ·
      refine ⟨19338110334667475648997079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25784147112889967531996105 19338110334667475648997079)
      ·
        refine ⟨29007165502001213473495619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19338110334667475648997079 29007165502001213473495619)
        ·
          refine ⟨43510748253001820210243429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29007165502001213473495619 43510748253001820210243429)
          ·
            refine ⟨8158265297437841289420643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43510748253001820210243429 8158265297437841289420643)
            ·
              refine ⟨12237397946156761934130965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158265297437841289420643 12237397946156761934130965)
              ·
                refine ⟨573628028726098215662389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12237397946156761934130965 573628028726098215662389)
                ·
                  refine ⟨53777627693071707718349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573628028726098215662389 53777627693071707718349)
                  ·
                    rfl

theorem cell23_942584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 5].length) (baseStart_942584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942584 prefixEnd_942584 := by exact prefixLift 942584
  have htrace : WordTrace (prefixWord ++ tailWord_942584) baseStart_942584 baseEnd_942584 := by
    simpa [prefixWord, tailWord_942584, baseEnd_942584] using wordTrace_append hprefix tailTrace_942584
  have hstable : (prefixWord ++ tailWord_942584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942584).length < 2 ^ (prefixWord ++ tailWord_942584).sum := by decide
  have hdescent : baseEnd_942584 < baseStart_942584 := by decide
  rcases family_descends (prefixWord ++ tailWord_942584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942597 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_942597 : Nat := 118140960795 + 942597 * 2 ^ 59
def prefixEnd_942597 : Nat := 4983230072969 + 3 ^ 40 * 942597 * 2
def baseEnd_942597 : Nat := 161335108162051272867527

theorem tailTrace_942597 : CollatzResearch.WordTrace tailWord_942597 prefixEnd_942597 161335108162051272867527 := by
  unfold tailWord_942597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34379336966139526596218045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22919557977426351064145363 34379336966139526596218045)
  ·
    refine ⟨12892251362302322473581767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34379336966139526596218045 12892251362302322473581767)
    ·
      refine ⟨19338377043453483710372651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892251362302322473581767 19338377043453483710372651)
      ·
        refine ⟨29007565565180225565558977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19338377043453483710372651 29007565565180225565558977)
        ·
          refine ⟨21755674173885169174169233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29007565565180225565558977 21755674173885169174169233)
          ·
            refine ⟨16316755630413876880626925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21755674173885169174169233 16316755630413876880626925)
            ·
              refine ⟨6118783361405203830235097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16316755630413876880626925 6118783361405203830235097)
              ·
                refine ⟨4589087521053902872676323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118783361405203830235097 4589087521053902872676323)
                ·
                  refine ⟨6883631281580854309014485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589087521053902872676323 6883631281580854309014485)
                  ·
                    refine ⟨161335108162051272867527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6883631281580854309014485 161335108162051272867527)
                    ·
                      rfl

theorem cell23_942597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_942597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942597 prefixEnd_942597 := by exact prefixLift 942597
  have htrace : WordTrace (prefixWord ++ tailWord_942597) baseStart_942597 baseEnd_942597 := by
    simpa [prefixWord, tailWord_942597, baseEnd_942597] using wordTrace_append hprefix tailTrace_942597
  have hstable : (prefixWord ++ tailWord_942597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942597).length < 2 ^ (prefixWord ++ tailWord_942597).sum := by decide
  have hdescent : baseEnd_942597 < baseStart_942597 := by decide
  rcases family_descends (prefixWord ++ tailWord_942597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942686 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_942686 : Nat := 118140960795 + 942686 * 2 ^ 59
def prefixEnd_942686 : Nat := 4983230072969 + 3 ^ 40 * 942686 * 2
def baseEnd_942686 : Nat := 53783447140489330043297

theorem tailTrace_942686 : CollatzResearch.WordTrace tailWord_942686 prefixEnd_942686 53783447140489330043297 := by
  unfold tailWord_942686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297822882852136849525989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22921722041878063197471941 4297822882852136849525989)
  ·
    refine ⟨805841790534775659286123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4297822882852136849525989 805841790534775659286123)
    ·
      refine ⟨1208762685802163488929185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805841790534775659286123 1208762685802163488929185)
      ·
        refine ⟨906572014351622616696889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208762685802163488929185 906572014351622616696889)
        ·
          refine ⟨679929010763716962522667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906572014351622616696889 679929010763716962522667)
          ·
            refine ⟨1019893516145575443784001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679929010763716962522667 1019893516145575443784001)
            ·
              refine ⟨764920137109181582838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019893516145575443784001 764920137109181582838001)
              ·
                refine ⟨573690102831886187128501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764920137109181582838001 573690102831886187128501)
                ·
                  refine ⟨53783447140489330043297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573690102831886187128501 53783447140489330043297)
                  ·
                    rfl

theorem cell23_942686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_942686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942686 prefixEnd_942686 := by exact prefixLift 942686
  have htrace : WordTrace (prefixWord ++ tailWord_942686) baseStart_942686 baseEnd_942686 := by
    simpa [prefixWord, tailWord_942686, baseEnd_942686] using wordTrace_append hprefix tailTrace_942686
  have hstable : (prefixWord ++ tailWord_942686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942686).length < 2 ^ (prefixWord ++ tailWord_942686).sum := by decide
  have hdescent : baseEnd_942686 < baseStart_942686 := by decide
  rcases family_descends (prefixWord ++ tailWord_942686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942711 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_942711 : Nat := 118140960795 + 942711 * 2 ^ 59
def prefixEnd_942711 : Nat := 4983230072969 + 3 ^ 40 * 942711 * 2
def baseEnd_942711 : Nat := 484063861280766372577057

theorem tailTrace_942711 : CollatzResearch.WordTrace tailWord_942711 prefixEnd_942711 484063861280766372577057 := by
  unfold tailWord_942711
  simp only [CollatzResearch.WordTrace]
  refine ⟨34383494887726524065867987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22922329925151016043911991 34383494887726524065867987)
  ·
    refine ⟨51575242331589786098801981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34383494887726524065867987 51575242331589786098801981)
    ·
      refine ⟨19340715874346169787050743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51575242331589786098801981 19340715874346169787050743)
      ·
        refine ⟨29011073811519254680576115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19340715874346169787050743 29011073811519254680576115)
        ·
          refine ⟨43516610717278882020864173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29011073811519254680576115 43516610717278882020864173)
          ·
            refine ⟨16318729018979580757824065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43516610717278882020864173 16318729018979580757824065)
            ·
              refine ⟨12239046764234685568368049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16318729018979580757824065 12239046764234685568368049)
              ·
                refine ⟨9179285073176014176276037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239046764234685568368049 9179285073176014176276037)
                ·
                  refine ⟨1721115951220502658051757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9179285073176014176276037 1721115951220502658051757)
                  ·
                    refine ⟨645418481707688496769409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721115951220502658051757 645418481707688496769409)
                    ·
                      refine ⟨484063861280766372577057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645418481707688496769409 484063861280766372577057)
                      ·
                        rfl

theorem cell23_942711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_942711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942711 prefixEnd_942711 := by exact prefixLift 942711
  have htrace : WordTrace (prefixWord ++ tailWord_942711) baseStart_942711 baseEnd_942711 := by
    simpa [prefixWord, tailWord_942711, baseEnd_942711] using wordTrace_append hprefix tailTrace_942711
  have hstable : (prefixWord ++ tailWord_942711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942711).length < 2 ^ (prefixWord ++ tailWord_942711).sum := by decide
  have hdescent : baseEnd_942711 < baseStart_942711 := by decide
  rcases family_descends (prefixWord ++ tailWord_942711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942721 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_942721 : Nat := 118140960795 + 942721 * 2 ^ 59
def prefixEnd_942721 : Nat := 4983230072969 + 3 ^ 40 * 942721 * 2
def baseEnd_942721 : Nat := 161356332029103777817337

theorem tailTrace_942721 : CollatzResearch.WordTrace tailWord_942721 prefixEnd_942721 161356332029103777817337 := by
  unfold tailWord_942721
  simp only [CollatzResearch.WordTrace]
  refine ⟨34383859617690295773732017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22922573078460197182488011 34383859617690295773732017)
  ·
    refine ⟨25787894713267721830299013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34383859617690295773732017 25787894713267721830299013)
    ·
      refine ⟨4835230258737697843181065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25787894713267721830299013 4835230258737697843181065)
      ·
        refine ⟨3626422694053273382385799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835230258737697843181065 3626422694053273382385799)
        ·
          refine ⟨5439634041079910073578699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626422694053273382385799 5439634041079910073578699)
          ·
            refine ⟨8159451061619865110368049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439634041079910073578699 8159451061619865110368049)
            ·
              refine ⟨6119588296214898832776037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8159451061619865110368049 6119588296214898832776037)
              ·
                refine ⟨1147422805540293531145507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6119588296214898832776037 1147422805540293531145507)
                ·
                  refine ⟨1721134208310440296718261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147422805540293531145507 1721134208310440296718261)
                  ·
                    refine ⟨161356332029103777817337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1721134208310440296718261 161356332029103777817337)
                    ·
                      rfl

theorem cell23_942721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_942721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942721 prefixEnd_942721 := by exact prefixLift 942721
  have htrace : WordTrace (prefixWord ++ tailWord_942721) baseStart_942721 baseEnd_942721 := by
    simpa [prefixWord, tailWord_942721, baseEnd_942721] using wordTrace_append hprefix tailTrace_942721
  have hstable : (prefixWord ++ tailWord_942721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942721).length < 2 ^ (prefixWord ++ tailWord_942721).sum := by decide
  have hdescent : baseEnd_942721 < baseStart_942721 := by decide
  rcases family_descends (prefixWord ++ tailWord_942721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942722 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_942722 : Nat := 118140960795 + 942722 * 2 ^ 59
def prefixEnd_942722 : Nat := 4983230072969 + 3 ^ 40 * 942722 * 2
def baseEnd_942722 : Nat := 484069509567965829539507

theorem tailTrace_942722 : CollatzResearch.WordTrace tailWord_942722 prefixEnd_942722 484069509567965829539507 := by
  unfold tailWord_942722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595974022671668236129605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22922597393791115296345613 8595974022671668236129605)
  ·
    refine ⟨1611745129250937794274301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8595974022671668236129605 1611745129250937794274301)
    ·
      refine ⟨604404423469101672852863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1611745129250937794274301 604404423469101672852863)
      ·
        refine ⟨906606635203652509279295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604404423469101672852863 906606635203652509279295)
        ·
          refine ⟨1359909952805478763918943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906606635203652509279295 1359909952805478763918943)
          ·
            refine ⟨2039864929208218145878415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359909952805478763918943 2039864929208218145878415)
            ·
              refine ⟨3059797393812327218817623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039864929208218145878415 3059797393812327218817623)
              ·
                refine ⟨4589696090718490828226435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059797393812327218817623 4589696090718490828226435)
                ·
                  refine ⟨6884544136077736242339653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589696090718490828226435 6884544136077736242339653)
                  ·
                    refine ⟨1290852025514575545438685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884544136077736242339653 1290852025514575545438685)
                    ·
                      refine ⟨484069509567965829539507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290852025514575545438685 484069509567965829539507)
                      ·
                        rfl

theorem cell23_942722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_942722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942722 prefixEnd_942722 := by exact prefixLift 942722
  have htrace : WordTrace (prefixWord ++ tailWord_942722) baseStart_942722 baseEnd_942722 := by
    simpa [prefixWord, tailWord_942722, baseEnd_942722] using wordTrace_append hprefix tailTrace_942722
  have hstable : (prefixWord ++ tailWord_942722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942722).length < 2 ^ (prefixWord ++ tailWord_942722).sum := by decide
  have hdescent : baseEnd_942722 < baseStart_942722 := by decide
  rcases family_descends (prefixWord ++ tailWord_942722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942738 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_942738 : Nat := 118140960795 + 942738 * 2 ^ 59
def prefixEnd_942738 : Nat := 4983230072969 + 3 ^ 40 * 942738 * 2
def baseEnd_942738 : Nat := 161359241752812588979811

theorem tailTrace_942738 : CollatzResearch.WordTrace tailWord_942738 prefixEnd_942738 161359241752812588979811 := by
  unfold tailWord_942738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596119914657176919275217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22922986439085805118067245 8596119914657176919275217)
  ·
    refine ⟨6447089935992882689456413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8596119914657176919275217 6447089935992882689456413)
    ·
      refine ⟨2417658725997331008546155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6447089935992882689456413 2417658725997331008546155)
      ·
        refine ⟨3626488088995996512819233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417658725997331008546155 3626488088995996512819233)
        ·
          refine ⟨2719866066746997384614425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3626488088995996512819233 2719866066746997384614425)
          ·
            refine ⟨2039899550060248038460819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719866066746997384614425 2039899550060248038460819)
            ·
              refine ⟨3059849325090372057691229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039899550060248038460819 3059849325090372057691229)
              ·
                refine ⟨1147443496908889521634211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059849325090372057691229 1147443496908889521634211)
                ·
                  refine ⟨1721165245363334282451317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147443496908889521634211 1721165245363334282451317)
                  ·
                    refine ⟨161359241752812588979811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1721165245363334282451317 161359241752812588979811)
                    ·
                      rfl

theorem cell23_942738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_942738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942738 prefixEnd_942738 := by exact prefixLift 942738
  have htrace : WordTrace (prefixWord ++ tailWord_942738) baseStart_942738 baseEnd_942738 := by
    simpa [prefixWord, tailWord_942738, baseEnd_942738] using wordTrace_append hprefix tailTrace_942738
  have hstable : (prefixWord ++ tailWord_942738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942738).length < 2 ^ (prefixWord ++ tailWord_942738).sum := by decide
  have hdescent : baseEnd_942738 < baseStart_942738 := by decide
  rcases family_descends (prefixWord ++ tailWord_942738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942771 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4]
def baseStart_942771 : Nat := 118140960795 + 942771 * 2 ^ 59
def prefixEnd_942771 : Nat := 4983230072969 + 3 ^ 40 * 942771 * 2
def baseEnd_942771 : Nat := 484094670120036137826781

theorem tailTrace_942771 : CollatzResearch.WordTrace tailWord_942771 prefixEnd_942771 484094670120036137826781 := by
  unfold tailWord_942771
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385683267509154313052167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22923788845006102875368111 34385683267509154313052167)
  ·
    refine ⟨51578524901263731469578251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34385683267509154313052167 51578524901263731469578251)
    ·
      refine ⟨77367787351895597204367377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51578524901263731469578251 77367787351895597204367377)
      ·
        refine ⟨58025840513921697903275533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77367787351895597204367377 58025840513921697903275533)
        ·
          refine ⟨21759690192720636713728325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58025840513921697903275533 21759690192720636713728325)
          ·
            refine ⟨4079941911135119383824061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21759690192720636713728325 4079941911135119383824061)
            ·
              refine ⟨1529978216675669768934023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4079941911135119383824061 1529978216675669768934023)
              ·
                refine ⟨2294967325013504653401035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529978216675669768934023 2294967325013504653401035)
                ·
                  refine ⟨3442450987520256980101553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294967325013504653401035 3442450987520256980101553)
                  ·
                    refine ⟨2581838240640192735076165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3442450987520256980101553 2581838240640192735076165)
                    ·
                      refine ⟨484094670120036137826781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2581838240640192735076165 484094670120036137826781)
                      ·
                        rfl

theorem cell23_942771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_942771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942771 prefixEnd_942771 := by exact prefixLift 942771
  have htrace : WordTrace (prefixWord ++ tailWord_942771) baseStart_942771 baseEnd_942771 := by
    simpa [prefixWord, tailWord_942771, baseEnd_942771] using wordTrace_append hprefix tailTrace_942771
  have hstable : (prefixWord ++ tailWord_942771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942771).length < 2 ^ (prefixWord ++ tailWord_942771).sum := by decide
  have hdescent : baseEnd_942771 < baseStart_942771 := by decide
  rcases family_descends (prefixWord ++ tailWord_942771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942778 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_942778 : Nat := 118140960795 + 942778 * 2 ^ 59
def prefixEnd_942778 : Nat := 4983230072969 + 3 ^ 40 * 942778 * 2
def baseEnd_942778 : Nat := 484098264484617610439249

theorem tailTrace_942778 : CollatzResearch.WordTrace tailWord_942778 prefixEnd_942778 484098264484617610439249 := by
  unfold tailWord_942778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596484644620948627139247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22923959052322529672371325 8596484644620948627139247)
  ·
    refine ⟨12894726966931422940708871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8596484644620948627139247 12894726966931422940708871)
    ·
      refine ⟨19342090450397134411063307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12894726966931422940708871 19342090450397134411063307)
      ·
        refine ⟨29013135675595701616594961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19342090450397134411063307 29013135675595701616594961)
        ·
          refine ⟨21759851756696776212446221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29013135675595701616594961 21759851756696776212446221)
          ·
            refine ⟨8159944408761291079667333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21759851756696776212446221 8159944408761291079667333)
            ·
              refine ⟨1529989576642742077437625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8159944408761291079667333 1529989576642742077437625)
              ·
                refine ⟨1147492182482056558078219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529989576642742077437625 1147492182482056558078219)
                ·
                  refine ⟨1721238273723084837117329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147492182482056558078219 1721238273723084837117329)
                  ·
                    refine ⟨1290928705292313627837997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721238273723084837117329 1290928705292313627837997)
                    ·
                      refine ⟨484098264484617610439249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290928705292313627837997 484098264484617610439249)
                      ·
                        rfl

theorem cell23_942778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_942778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942778 prefixEnd_942778 := by exact prefixLift 942778
  have htrace : WordTrace (prefixWord ++ tailWord_942778) baseStart_942778 baseEnd_942778 := by
    simpa [prefixWord, tailWord_942778, baseEnd_942778] using wordTrace_append hprefix tailTrace_942778
  have hstable : (prefixWord ++ tailWord_942778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942778).length < 2 ^ (prefixWord ++ tailWord_942778).sum := by decide
  have hdescent : baseEnd_942778 < baseStart_942778 := by decide
  rcases family_descends (prefixWord ++ tailWord_942778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942781 : List Nat := [1, 4, 1, 2, 1, 3, 4, 7]
def baseStart_942781 : Nat := 118140960795 + 942781 * 2 ^ 59
def prefixEnd_942781 : Nat := 4983230072969 + 3 ^ 40 * 942781 * 2
def baseEnd_942781 : Nat := 17929622404688188840805

theorem tailTrace_942781 : CollatzResearch.WordTrace tailWord_942781 prefixEnd_942781 17929622404688188840805 := by
  unfold tailWord_942781
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386047997472926020916197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22924031998315284013944131 34386047997472926020916197)
  ·
    refine ⟨6447383999526173628921787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34386047997472926020916197 6447383999526173628921787)
    ·
      refine ⟨9671075999289260443382681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447383999526173628921787 9671075999289260443382681)
      ·
        refine ⟨7253306999466945332537011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9671075999289260443382681 7253306999466945332537011)
        ·
          refine ⟨10879960499200417998805517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253306999466945332537011 10879960499200417998805517)
          ·
            refine ⟨4079985187200156749552069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10879960499200417998805517 4079985187200156749552069)
            ·
              refine ⟨764997222600029390541013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4079985187200156749552069 764997222600029390541013)
              ·
                refine ⟨17929622404688188840805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 764997222600029390541013 17929622404688188840805)
                ·
                  rfl

theorem cell23_942781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 7].length) (baseStart_942781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942781 prefixEnd_942781 := by exact prefixLift 942781
  have htrace : WordTrace (prefixWord ++ tailWord_942781) baseStart_942781 baseEnd_942781 := by
    simpa [prefixWord, tailWord_942781, baseEnd_942781] using wordTrace_append hprefix tailTrace_942781
  have hstable : (prefixWord ++ tailWord_942781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942781).length < 2 ^ (prefixWord ++ tailWord_942781).sum := by decide
  have hdescent : baseEnd_942781 < baseStart_942781 := by decide
  rcases family_descends (prefixWord ++ tailWord_942781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942792 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_942792 : Nat := 118140960795 + 942792 * 2 ^ 59
def prefixEnd_942792 : Nat := 4983230072969 + 3 ^ 40 * 942792 * 2
def baseEnd_942792 : Nat := 484105453213780555664185

theorem tailTrace_942792 : CollatzResearch.WordTrace tailWord_942792 prefixEnd_942792 484105453213780555664185 := by
  unfold tailWord_942792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193224600216537449783315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22924299466955383266377753 17193224600216537449783315)
  ·
    refine ⟨25789836900324806174674973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17193224600216537449783315 25789836900324806174674973)
    ·
      refine ⟨9671188837621802315503115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25789836900324806174674973 9671188837621802315503115)
      ·
        refine ⟨14506783256432703473254673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9671188837621802315503115 14506783256432703473254673)
        ·
          refine ⟨10880087442324527604941005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14506783256432703473254673 10880087442324527604941005)
          ·
            refine ⟨4080032790871697851852877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10880087442324527604941005 4080032790871697851852877)
            ·
              refine ⟨1530012296576886694444829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4080032790871697851852877 1530012296576886694444829)
              ·
                refine ⟨573754611216332510416811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530012296576886694444829 573754611216332510416811)
                ·
                  refine ⟨860631916824498765625217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573754611216332510416811 860631916824498765625217)
                  ·
                    refine ⟨645473937618374074218913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 860631916824498765625217 645473937618374074218913)
                    ·
                      refine ⟨484105453213780555664185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645473937618374074218913 484105453213780555664185)
                      ·
                        rfl

theorem cell23_942792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_942792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942792 prefixEnd_942792 := by exact prefixLift 942792
  have htrace : WordTrace (prefixWord ++ tailWord_942792) baseStart_942792 baseEnd_942792 := by
    simpa [prefixWord, tailWord_942792, baseEnd_942792] using wordTrace_append hprefix tailTrace_942792
  have hstable : (prefixWord ++ tailWord_942792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942792).length < 2 ^ (prefixWord ++ tailWord_942792).sum := by decide
  have hdescent : baseEnd_942792 < baseStart_942792 := by decide
  rcases family_descends (prefixWord ++ tailWord_942792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942808 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_942808 : Nat := 118140960795 + 942808 * 2 ^ 59
def prefixEnd_942808 : Nat := 4983230072969 + 3 ^ 40 * 942808 * 2
def baseEnd_942808 : Nat := 484113668904252493064111

theorem tailTrace_942808 : CollatzResearch.WordTrace tailWord_942808 prefixEnd_942808 484113668904252493064111 := by
  unfold tailWord_942808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193516384187554816074539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22924688512250073088099385 17193516384187554816074539)
  ·
    refine ⟨25790274576281332224111809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17193516384187554816074539 25790274576281332224111809)
    ·
      refine ⟨19342705932210999168083857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25790274576281332224111809 19342705932210999168083857)
      ·
        refine ⟨14507029449158249376062893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19342705932210999168083857 14507029449158249376062893)
        ·
          refine ⟨5440136043434343516023585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14507029449158249376062893 5440136043434343516023585)
          ·
            refine ⟨4080102032575757637017689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5440136043434343516023585 4080102032575757637017689)
            ·
              refine ⟨3060076524431818227763267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4080102032575757637017689 3060076524431818227763267)
              ·
                refine ⟨4590114786647727341644901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060076524431818227763267 4590114786647727341644901)
                ·
                  refine ⟨860646522496448876558419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4590114786647727341644901 860646522496448876558419)
                  ·
                    refine ⟨1290969783744673314837629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860646522496448876558419 1290969783744673314837629)
                    ·
                      refine ⟨484113668904252493064111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290969783744673314837629 484113668904252493064111)
                      ·
                        rfl

theorem cell23_942808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_942808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942808 prefixEnd_942808 := by exact prefixLift 942808
  have htrace : WordTrace (prefixWord ++ tailWord_942808) baseStart_942808 baseEnd_942808 := by
    simpa [prefixWord, tailWord_942808, baseEnd_942808] using wordTrace_append hprefix tailTrace_942808
  have hstable : (prefixWord ++ tailWord_942808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942808).length < 2 ^ (prefixWord ++ tailWord_942808).sum := by decide
  have hdescent : baseEnd_942808 < baseStart_942808 := by decide
  rcases family_descends (prefixWord ++ tailWord_942808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942825 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 2, 1, 3]
def baseStart_942825 : Nat := 118140960795 + 942825 * 2 ^ 59
def prefixEnd_942825 : Nat := 4983230072969 + 3 ^ 40 * 942825 * 2
def baseEnd_942825 : Nat := 484122398075378926551533

theorem tailTrace_942825 : CollatzResearch.WordTrace tailWord_942825 prefixEnd_942825 484122398075378926551533 := by
  unfold tailWord_942825
  simp only [CollatzResearch.WordTrace]
  refine ⟨34387652809313521535517929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22925101872875681023678619 34387652809313521535517929)
  ·
    refine ⟨25790739606985141151638447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34387652809313521535517929 25790739606985141151638447)
    ·
      refine ⟨38686109410477711727457671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25790739606985141151638447 38686109410477711727457671)
      ·
        refine ⟨58029164115716567591186507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38686109410477711727457671 58029164115716567591186507)
        ·
          refine ⟨87043746173574851386779761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58029164115716567591186507 87043746173574851386779761)
          ·
            refine ⟨65282809630181138540084821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87043746173574851386779761 65282809630181138540084821)
            ·
              refine ⟨765032925353685217266619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 65282809630181138540084821 765032925353685217266619)
              ·
                refine ⟨1147549388030527825899929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765032925353685217266619 1147549388030527825899929)
                ·
                  refine ⟨860662041022895869424947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147549388030527825899929 860662041022895869424947)
                  ·
                    refine ⟨1290993061534343804137421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860662041022895869424947 1290993061534343804137421)
                    ·
                      refine ⟨484122398075378926551533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1290993061534343804137421 484122398075378926551533)
                      ·
                        rfl

theorem cell23_942825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 1, 3].length) (baseStart_942825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942825 prefixEnd_942825 := by exact prefixLift 942825
  have htrace : WordTrace (prefixWord ++ tailWord_942825) baseStart_942825 baseEnd_942825 := by
    simpa [prefixWord, tailWord_942825, baseEnd_942825] using wordTrace_append hprefix tailTrace_942825
  have hstable : (prefixWord ++ tailWord_942825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942825).length < 2 ^ (prefixWord ++ tailWord_942825).sum := by decide
  have hdescent : baseEnd_942825 < baseStart_942825 := by decide
  rcases family_descends (prefixWord ++ tailWord_942825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942852 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_942852 : Nat := 118140960795 + 942852 * 2 ^ 59
def prefixEnd_942852 : Nat := 4983230072969 + 3 ^ 40 * 942852 * 2
def baseEnd_942852 : Nat := 484136262053050320913909

theorem tailTrace_942852 : CollatzResearch.WordTrace tailWord_942852 prefixEnd_942852 484136262053050320913909 := by
  unfold tailWord_942852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194318790107852573375405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22925758386810470097833873 17194318790107852573375405)
  ·
    refine ⟨6447869546290444715015777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17194318790107852573375405 6447869546290444715015777)
    ·
      refine ⟨4835902159717833536261833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6447869546290444715015777 4835902159717833536261833)
      ·
        refine ⟨3626926619788375152196375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835902159717833536261833 3626926619788375152196375)
        ·
          refine ⟨5440389929682562728294563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626926619788375152196375 5440389929682562728294563)
          ·
            refine ⟨8160584894523844092441845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440389929682562728294563 8160584894523844092441845)
            ·
              refine ⟨765054833861610383666423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8160584894523844092441845 765054833861610383666423)
              ·
                refine ⟨1147582250792415575499635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765054833861610383666423 1147582250792415575499635)
                ·
                  refine ⟨1721373376188623363249453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147582250792415575499635 1721373376188623363249453)
                  ·
                    refine ⟨645515016070733761218545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721373376188623363249453 645515016070733761218545)
                    ·
                      refine ⟨484136262053050320913909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645515016070733761218545 484136262053050320913909)
                      ·
                        rfl

theorem cell23_942852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_942852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942852 prefixEnd_942852 := by exact prefixLift 942852
  have htrace : WordTrace (prefixWord ++ tailWord_942852) baseStart_942852 baseEnd_942852 := by
    simpa [prefixWord, tailWord_942852, baseEnd_942852] using wordTrace_append hprefix tailTrace_942852
  have hstable : (prefixWord ++ tailWord_942852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942852).length < 2 ^ (prefixWord ++ tailWord_942852).sum := by decide
  have hdescent : baseEnd_942852 < baseStart_942852 := by decide
  rcases family_descends (prefixWord ++ tailWord_942852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942865 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_942865 : Nat := 118140960795 + 942865 * 2 ^ 59
def prefixEnd_942865 : Nat := 4983230072969 + 3 ^ 40 * 942865 * 2
def baseEnd_942865 : Nat := 484142937301558770051349

theorem tailTrace_942865 : CollatzResearch.WordTrace tailWord_942865 prefixEnd_942865 484142937301558770051349 := by
  unfold tailWord_942865
  simp only [CollatzResearch.WordTrace]
  refine ⟨34389111729168608366974049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22926074486112405577982699 34389111729168608366974049)
  ·
    refine ⟨25791833796876456275230537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34389111729168608366974049 25791833796876456275230537)
    ·
      refine ⟨19343875347657342206422903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25791833796876456275230537 19343875347657342206422903)
      ·
        refine ⟨29015813021486013309634355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19343875347657342206422903 29015813021486013309634355)
        ·
          refine ⟨43523719532229019964451533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29015813021486013309634355 43523719532229019964451533)
          ·
            refine ⟨16321394824585882486669325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43523719532229019964451533 16321394824585882486669325)
            ·
              refine ⟨6120523059219705932500997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16321394824585882486669325 6120523059219705932500997)
              ·
                refine ⟨1147598073603694862343937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6120523059219705932500997 1147598073603694862343937)
                ·
                  refine ⟨860698555202771146757953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147598073603694862343937 860698555202771146757953)
                  ·
                    refine ⟨645523916402078360068465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 860698555202771146757953 645523916402078360068465)
                    ·
                      refine ⟨484142937301558770051349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645523916402078360068465 484142937301558770051349)
                      ·
                        rfl

theorem cell23_942865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_942865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942865 prefixEnd_942865 := by exact prefixLift 942865
  have htrace : WordTrace (prefixWord ++ tailWord_942865) baseStart_942865 baseEnd_942865 := by
    simpa [prefixWord, tailWord_942865, baseEnd_942865] using wordTrace_append hprefix tailTrace_942865
  have hstable : (prefixWord ++ tailWord_942865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942865).length < 2 ^ (prefixWord ++ tailWord_942865).sum := by decide
  have hdescent : baseEnd_942865 < baseStart_942865 := by decide
  rcases family_descends (prefixWord ++ tailWord_942865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942882 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_942882 : Nat := 118140960795 + 942882 * 2 ^ 59
def prefixEnd_942882 : Nat := 4983230072969 + 3 ^ 40 * 942882 * 2
def baseEnd_942882 : Nat := 484151666472685203538771

theorem tailTrace_942882 : CollatzResearch.WordTrace tailWord_942882 prefixEnd_942882 484151666472685203538771 := by
  unfold tailWord_942882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8597432942526755067585725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22926487846738013513561933 8597432942526755067585725)
  ·
    refine ⟨3224037353447533150344647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8597432942526755067585725 3224037353447533150344647)
    ·
      refine ⟨4836056030171299725516971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224037353447533150344647 4836056030171299725516971)
      ·
        refine ⟨7254084045256949588275457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836056030171299725516971 7254084045256949588275457)
        ·
          refine ⟨5440563033942712191206593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7254084045256949588275457 5440563033942712191206593)
          ·
            refine ⟨4080422275457034143404945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5440563033942712191206593 4080422275457034143404945)
            ·
              refine ⟨3060316706592775607553709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4080422275457034143404945 3060316706592775607553709)
              ·
                refine ⟨1147618764972290852832641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060316706592775607553709 1147618764972290852832641)
                ·
                  refine ⟨860714073729218139624481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147618764972290852832641 860714073729218139624481)
                  ·
                    refine ⟨645535555296913604718361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 860714073729218139624481 645535555296913604718361)
                    ·
                      refine ⟨484151666472685203538771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645535555296913604718361 484151666472685203538771)
                      ·
                        rfl

theorem cell23_942882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_942882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942882 prefixEnd_942882 := by exact prefixLift 942882
  have htrace : WordTrace (prefixWord ++ tailWord_942882) baseStart_942882 baseEnd_942882 := by
    simpa [prefixWord, tailWord_942882, baseEnd_942882] using wordTrace_append hprefix tailTrace_942882
  have hstable : (prefixWord ++ tailWord_942882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942882).length < 2 ^ (prefixWord ++ tailWord_942882).sum := by decide
  have hdescent : baseEnd_942882 < baseStart_942882 := by decide
  rcases family_descends (prefixWord ++ tailWord_942882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942961 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 8]
def baseStart_942961 : Nat := 118140960795 + 942961 * 2 ^ 59
def prefixEnd_942961 : Nat := 4983230072969 + 3 ^ 40 * 942961 * 2
def baseEnd_942961 : Nat := 53799136827154488272323

theorem tailTrace_942961 : CollatzResearch.WordTrace tailWord_942961 prefixEnd_942961 53799136827154488272323 := by
  unfold tailWord_942961
  simp only [CollatzResearch.WordTrace]
  refine ⟨34392613136820816762468737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928408757880544508312491 34392613136820816762468737)
  ·
    refine ⟨25794459852615612571851553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34392613136820816762468737 25794459852615612571851553)
    ·
      refine ⟨19345844889461709428888665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25794459852615612571851553 19345844889461709428888665)
      ·
        refine ⟨14509383667096282071666499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19345844889461709428888665 14509383667096282071666499)
        ·
          refine ⟨21764075500644423107499749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14509383667096282071666499 21764075500644423107499749)
          ·
            refine ⟨4080764156370829332656203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21764075500644423107499749 4080764156370829332656203)
            ·
              refine ⟨6121146234556243998984305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080764156370829332656203 6121146234556243998984305)
              ·
                refine ⟨4590859675917182999238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6121146234556243998984305 4590859675917182999238229)
                ·
                  refine ⟨53799136827154488272323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4590859675917182999238229 53799136827154488272323)
                  ·
                    rfl

theorem cell23_942961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_942961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_942961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_942961 prefixEnd_942961 := by exact prefixLift 942961
  have htrace : WordTrace (prefixWord ++ tailWord_942961) baseStart_942961 baseEnd_942961 := by
    simpa [prefixWord, tailWord_942961, baseEnd_942961] using wordTrace_append hprefix tailTrace_942961
  have hstable : (prefixWord ++ tailWord_942961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942961).length < 2 ^ (prefixWord ++ tailWord_942961).sum := by decide
  have hdescent : baseEnd_942961 < baseStart_942961 := by decide
  rcases family_descends (prefixWord ++ tailWord_942961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943005 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_943005 : Nat := 118140960795 + 943005 * 2 ^ 59
def prefixEnd_943005 : Nat := 4983230072969 + 3 ^ 40 * 943005 * 2
def baseEnd_943005 : Nat := 484214824593188222300705

theorem tailTrace_943005 : CollatzResearch.WordTrace tailWord_943005 prefixEnd_943005 484214824593188222300705 := by
  unfold tailWord_943005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34394217948661412277070469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22929478632440941518046979 34394217948661412277070469)
  ·
    refine ⟨6448915865374014801950713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34394217948661412277070469 6448915865374014801950713)
    ·
      refine ⟨4836686899030511101463035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6448915865374014801950713 4836686899030511101463035)
      ·
        refine ⟨7255030348545766652194553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836686899030511101463035 7255030348545766652194553)
        ·
          refine ⟨5441272761409324989145915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255030348545766652194553 5441272761409324989145915)
          ·
            refine ⟨8161909142113987483718873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441272761409324989145915 8161909142113987483718873)
            ·
              refine ⟨6121431856585490612789155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161909142113987483718873 6121431856585490612789155)
              ·
                refine ⟨9182147784878235919183733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121431856585490612789155 9182147784878235919183733)
                ·
                  refine ⟨860826354832334617423475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9182147784878235919183733 860826354832334617423475)
                  ·
                    refine ⟨1291239532248501926135213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860826354832334617423475 1291239532248501926135213)
                    ·
                      refine ⟨484214824593188222300705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1291239532248501926135213 484214824593188222300705)
                      ·
                        rfl

theorem cell23_943005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_943005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943005 prefixEnd_943005 := by exact prefixLift 943005
  have htrace : WordTrace (prefixWord ++ tailWord_943005) baseStart_943005 baseEnd_943005 := by
    simpa [prefixWord, tailWord_943005, baseEnd_943005] using wordTrace_append hprefix tailTrace_943005
  have hstable : (prefixWord ++ tailWord_943005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943005).length < 2 ^ (prefixWord ++ tailWord_943005).sum := by decide
  have hdescent : baseEnd_943005 < baseStart_943005 := by decide
  rcases family_descends (prefixWord ++ tailWord_943005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943038 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_943038 : Nat := 118140960795 + 943038 * 2 ^ 59
def prefixEnd_943038 : Nat := 4983230072969 + 3 ^ 40 * 943038 * 2
def baseEnd_943038 : Nat := 161410589818262197729351

theorem tailTrace_943038 : CollatzResearch.WordTrace tailWord_943038 prefixEnd_943038 161410589818262197729351 := by
  unfold tailWord_943038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299427694692732364127721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22930281038361239275347845 4299427694692732364127721)
  ·
    refine ⟨3224570771019549273095791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4299427694692732364127721 3224570771019549273095791)
    ·
      refine ⟨4836856156529323909643687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224570771019549273095791 4836856156529323909643687)
      ·
        refine ⟨7255284234793985864465531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836856156529323909643687 7255284234793985864465531)
        ·
          refine ⟨10882926352190978796698297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255284234793985864465531 10882926352190978796698297)
          ·
            refine ⟨8162194764143234097523723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10882926352190978796698297 8162194764143234097523723)
            ·
              refine ⟨12243292146214851146285585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162194764143234097523723 12243292146214851146285585)
              ·
                refine ⟨9182469109661138359714189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243292146214851146285585 9182469109661138359714189)
                ·
                  refine ⟨3443425916122926884892821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9182469109661138359714189 3443425916122926884892821)
                  ·
                    refine ⟨161410589818262197729351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3443425916122926884892821 161410589818262197729351)
                    ·
                      rfl

theorem cell23_943038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_943038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943038 prefixEnd_943038 := by exact prefixLift 943038
  have htrace : WordTrace (prefixWord ++ tailWord_943038) baseStart_943038 baseEnd_943038 := by
    simpa [prefixWord, tailWord_943038, baseEnd_943038] using wordTrace_append hprefix tailTrace_943038
  have hstable : (prefixWord ++ tailWord_943038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943038).length < 2 ^ (prefixWord ++ tailWord_943038).sum := by decide
  have hdescent : baseEnd_943038 < baseStart_943038 := by decide
  rcases family_descends (prefixWord ++ tailWord_943038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943055 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 2, 4]
def baseStart_943055 : Nat := 118140960795 + 943055 * 2 ^ 59
def prefixEnd_943055 : Nat := 4983230072969 + 3 ^ 40 * 943055 * 2
def baseEnd_943055 : Nat := 161413499541971008891825

theorem tailTrace_943055 : CollatzResearch.WordTrace tailWord_943055 prefixEnd_943055 161413499541971008891825 := by
  unfold tailWord_943055
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396041598480270816390619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22930694398986847210927079 34396041598480270816390619)
  ·
    refine ⟨51594062397720406224585929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34396041598480270816390619 51594062397720406224585929)
    ·
      refine ⟨38695546798290304668439447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51594062397720406224585929 38695546798290304668439447)
      ·
        refine ⟨58043320197435457002659171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38695546798290304668439447 58043320197435457002659171)
        ·
          refine ⟨87064980296153185503988757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58043320197435457002659171 87064980296153185503988757)
          ·
            refine ⟨4081170951382180570499473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87064980296153185503988757 4081170951382180570499473)
            ·
              refine ⟨3060878213536635427874605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081170951382180570499473 3060878213536635427874605)
              ·
                refine ⟨1147829330076238285452977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060878213536635427874605 1147829330076238285452977)
                ·
                  refine ⟨860871997557178714089733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147829330076238285452977 860871997557178714089733)
                  ·
                    refine ⟨161413499541971008891825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 860871997557178714089733 161413499541971008891825)
                    ·
                      rfl

theorem cell23_943055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_943055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943055 prefixEnd_943055 := by exact prefixLift 943055
  have htrace : WordTrace (prefixWord ++ tailWord_943055) baseStart_943055 baseEnd_943055 := by
    simpa [prefixWord, tailWord_943055, baseEnd_943055] using wordTrace_append hprefix tailTrace_943055
  have hstable : (prefixWord ++ tailWord_943055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943055).length < 2 ^ (prefixWord ++ tailWord_943055).sum := by decide
  have hdescent : baseEnd_943055 < baseStart_943055 := by decide
  rcases family_descends (prefixWord ++ tailWord_943055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943062 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_943062 : Nat := 118140960795 + 943062 * 2 ^ 59
def prefixEnd_943062 : Nat := 4983230072969 + 3 ^ 40 * 943062 * 2
def baseEnd_943062 : Nat := 484244092990494499287943

theorem tailTrace_943062 : CollatzResearch.WordTrace tailWord_943062 prefixEnd_943062 484244092990494499287943 := by
  unfold tailWord_943062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149768556840931938243465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22930864606303274007930293 2149768556840931938243465)
  ·
    refine ⟨1612326417630698953682599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2149768556840931938243465 1612326417630698953682599)
    ·
      refine ⟨2418489626446048430523899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612326417630698953682599 2418489626446048430523899)
      ·
        refine ⟨3627734439669072645785849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418489626446048430523899 3627734439669072645785849)
        ·
          refine ⟨2720800829751804484339387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3627734439669072645785849 2720800829751804484339387)
          ·
            refine ⟨4081201244627706726509081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720800829751804484339387 4081201244627706726509081)
            ·
              refine ⟨3060900933470780044881811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081201244627706726509081 3060900933470780044881811)
              ·
                refine ⟨4591351400206170067322717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060900933470780044881811 4591351400206170067322717)
                ·
                  refine ⟨1721756775077313775246019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4591351400206170067322717 1721756775077313775246019)
                  ·
                    refine ⟨2582635162615970662869029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1721756775077313775246019 2582635162615970662869029)
                    ·
                      refine ⟨484244092990494499287943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2582635162615970662869029 484244092990494499287943)
                      ·
                        rfl

theorem cell23_943062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_943062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943062 prefixEnd_943062 := by exact prefixLift 943062
  have htrace : WordTrace (prefixWord ++ tailWord_943062) baseStart_943062 baseEnd_943062 := by
    simpa [prefixWord, tailWord_943062, baseEnd_943062] using wordTrace_append hprefix tailTrace_943062
  have hstable : (prefixWord ++ tailWord_943062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943062).length < 2 ^ (prefixWord ++ tailWord_943062).sum := by decide
  have hdescent : baseEnd_943062 < baseStart_943062 := by decide
  rcases family_descends (prefixWord ++ tailWord_943062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943065 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_943065 : Nat := 118140960795 + 943065 * 2 ^ 59
def prefixEnd_943065 : Nat := 4983230072969 + 3 ^ 40 * 943065 * 2
def baseEnd_943065 : Nat := 484245633432457987550429

theorem tailTrace_943065 : CollatzResearch.WordTrace tailWord_943065 prefixEnd_943065 484245633432457987550429 := by
  unfold tailWord_943065
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396406328444042524254649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22930937552296028349503099 34396406328444042524254649)
  ·
    refine ⟨25797304746333031893190987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34396406328444042524254649 25797304746333031893190987)
    ·
      refine ⟨38695957119499547839786481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25797304746333031893190987 38695957119499547839786481)
      ·
        refine ⟨29021967839624660879839861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38695957119499547839786481 29021967839624660879839861)
        ·
          refine ⟨2720809484964811957484987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29021967839624660879839861 2720809484964811957484987)
          ·
            refine ⟨4081214227447217936227481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720809484964811957484987 4081214227447217936227481)
            ·
              refine ⟨3060910670585413452170611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081214227447217936227481 3060910670585413452170611)
              ·
                refine ⟨4591366005878120178255917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060910670585413452170611 4591366005878120178255917)
                ·
                  refine ⟨1721762252204295066845969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4591366005878120178255917 1721762252204295066845969)
                  ·
                    refine ⟨1291321689153221300134477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721762252204295066845969 1291321689153221300134477)
                    ·
                      refine ⟨484245633432457987550429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1291321689153221300134477 484245633432457987550429)
                      ·
                        rfl

theorem cell23_943065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_943065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943065 prefixEnd_943065 := by exact prefixLift 943065
  have htrace : WordTrace (prefixWord ++ tailWord_943065) baseStart_943065 baseEnd_943065 := by
    simpa [prefixWord, tailWord_943065, baseEnd_943065] using wordTrace_append hprefix tailTrace_943065
  have hstable : (prefixWord ++ tailWord_943065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943065).length < 2 ^ (prefixWord ++ tailWord_943065).sum := by decide
  have hdescent : baseEnd_943065 < baseStart_943065 := by decide
  rcases family_descends (prefixWord ++ tailWord_943065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943079 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_943079 : Nat := 118140960795 + 943079 * 2 ^ 59
def prefixEnd_943079 : Nat := 4983230072969 + 3 ^ 40 * 943079 * 2
def baseEnd_943079 : Nat := 484252822161620932775365

theorem tailTrace_943079 : CollatzResearch.WordTrace tailWord_943079 prefixEnd_943079 484252822161620932775365 := by
  unfold tailWord_943079
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396916950393322915264291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22931277966928881943509527 34396916950393322915264291)
  ·
    refine ⟨51595375425589984372896437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34396916950393322915264291 51595375425589984372896437)
    ·
      refine ⟨4837066446149061034959041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51595375425589984372896437 4837066446149061034959041)
      ·
        refine ⟨3627799834611795776219281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837066446149061034959041 3627799834611795776219281)
        ·
          refine ⟨2720849875958846832164461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3627799834611795776219281 2720849875958846832164461)
          ·
            refine ⟨1020318703484567562061673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2720849875958846832164461 1020318703484567562061673)
            ·
              refine ⟨765239027613425671546255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020318703484567562061673 765239027613425671546255)
              ·
                refine ⟨1147858541420138507319383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765239027613425671546255 1147858541420138507319383)
                ·
                  refine ⟨1721787812130207760979075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147858541420138507319383 1721787812130207760979075)
                  ·
                    refine ⟨2582681718195311641468613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1721787812130207760979075 2582681718195311641468613)
                    ·
                      refine ⟨484252822161620932775365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2582681718195311641468613 484252822161620932775365)
                      ·
                        rfl

theorem cell23_943079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_943079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943079 prefixEnd_943079 := by exact prefixLift 943079
  have htrace : WordTrace (prefixWord ++ tailWord_943079) baseStart_943079 baseEnd_943079 := by
    simpa [prefixWord, tailWord_943079, baseEnd_943079] using wordTrace_append hprefix tailTrace_943079
  have hstable : (prefixWord ++ tailWord_943079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943079).length < 2 ^ (prefixWord ++ tailWord_943079).sum := by decide
  have hdescent : baseEnd_943079 < baseStart_943079 := by decide
  rcases family_descends (prefixWord ++ tailWord_943079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943082 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_943082 : Nat := 118140960795 + 943082 * 2 ^ 59
def prefixEnd_943082 : Nat := 4983230072969 + 3 ^ 40 * 943082 * 2
def baseEnd_943082 : Nat := 484254362603584421037851

theorem tailTrace_943082 : CollatzResearch.WordTrace tailWord_943082 prefixEnd_943082 484254362603584421037851 := by
  unfold tailWord_943082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599256592345613606905875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22931350912921636285082333 8599256592345613606905875)
  ·
    refine ⟨12898884888518420410358813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8599256592345613606905875 12898884888518420410358813)
    ·
      refine ⟨4837081833194407653884555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12898884888518420410358813 4837081833194407653884555)
      ·
        refine ⟨7255622749791611480826833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837081833194407653884555 7255622749791611480826833)
        ·
          refine ⟨5441717062343708610620125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255622749791611480826833 5441717062343708610620125)
          ·
            refine ⟨2040643898378890728982547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5441717062343708610620125 2040643898378890728982547)
            ·
              refine ⟨3060965847568336093473821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040643898378890728982547 3060965847568336093473821)
              ·
                refine ⟨1147862192838126035052683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060965847568336093473821 1147862192838126035052683)
                ·
                  refine ⟨1721793289257189052579025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147862192838126035052683 1721793289257189052579025)
                  ·
                    refine ⟨1291344966942891789434269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721793289257189052579025 1291344966942891789434269)
                    ·
                      refine ⟨484254362603584421037851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1291344966942891789434269 484254362603584421037851)
                      ·
                        rfl

theorem cell23_943082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_943082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943082 prefixEnd_943082 := by exact prefixLift 943082
  have htrace : WordTrace (prefixWord ++ tailWord_943082) baseStart_943082 baseEnd_943082 := by
    simpa [prefixWord, tailWord_943082, baseEnd_943082] using wordTrace_append hprefix tailTrace_943082
  have hstable : (prefixWord ++ tailWord_943082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943082).length < 2 ^ (prefixWord ++ tailWord_943082).sum := by decide
  have hdescent : baseEnd_943082 < baseStart_943082 := by decide
  rcases family_descends (prefixWord ++ tailWord_943082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943106 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_943106 : Nat := 118140960795 + 943106 * 2 ^ 59
def prefixEnd_943106 : Nat := 4983230072969 + 3 ^ 40 * 943106 * 2
def baseEnd_943106 : Nat := 161422228713097442379247

theorem tailTrace_943106 : CollatzResearch.WordTrace tailWord_943106 prefixEnd_943106 161422228713097442379247 := by
  unfold tailWord_943106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599475430323876631624293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22931934480863671017664781 8599475430323876631624293)
  ·
    refine ⟨1612401643185726868429555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8599475430323876631624293 1612401643185726868429555)
    ·
      refine ⟨2418602464778590302644333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612401643185726868429555 2418602464778590302644333)
      ·
        refine ⟨906975924291971363491625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2418602464778590302644333 906975924291971363491625)
        ·
          refine ⟨680231943218978522618719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906975924291971363491625 680231943218978522618719)
          ·
            refine ⟨1020347914828467783928079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680231943218978522618719 1020347914828467783928079)
            ·
              refine ⟨1530521872242701675892119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020347914828467783928079 1530521872242701675892119)
              ·
                refine ⟨2295782808364052513838179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530521872242701675892119 2295782808364052513838179)
                ·
                  refine ⟨3443674212546078770757269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295782808364052513838179 3443674212546078770757269)
                  ·
                    refine ⟨161422228713097442379247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3443674212546078770757269 161422228713097442379247)
                    ·
                      rfl

theorem cell23_943106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_943106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943106 prefixEnd_943106 := by exact prefixLift 943106
  have htrace : WordTrace (prefixWord ++ tailWord_943106) baseStart_943106 baseEnd_943106 := by
    simpa [prefixWord, tailWord_943106, baseEnd_943106] using wordTrace_append hprefix tailTrace_943106
  have hstable : (prefixWord ++ tailWord_943106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943106).length < 2 ^ (prefixWord ++ tailWord_943106).sum := by decide
  have hdescent : baseEnd_943106 < baseStart_943106 := by decide
  rcases family_descends (prefixWord ++ tailWord_943106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943112 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_943112 : Nat := 118140960795 + 943112 * 2 ^ 59
def prefixEnd_943112 : Nat := 4983230072969 + 3 ^ 40 * 943112 * 2
def baseEnd_943112 : Nat := 484269767023219303662713

theorem tailTrace_943112 : CollatzResearch.WordTrace tailWord_943112 prefixEnd_943112 484269767023219303662713 := by
  unfold tailWord_943112
  simp only [CollatzResearch.WordTrace]
  refine ⟨17199060279636884775607795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22932080372849179700810393 17199060279636884775607795)
  ·
    refine ⟨25798590419455327163411693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17199060279636884775607795 25798590419455327163411693)
    ·
      refine ⟨9674471407295747686279385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25798590419455327163411693 9674471407295747686279385)
      ·
        refine ⟨7255853555471810764709539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9674471407295747686279385 7255853555471810764709539)
        ·
          refine ⟨10883780333207716147064309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255853555471810764709539 10883780333207716147064309)
          ·
            refine ⟨1020354406238223388787279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10883780333207716147064309 1020354406238223388787279)
            ·
              refine ⟨1530531609357335083180919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020354406238223388787279 1530531609357335083180919)
              ·
                refine ⟨2295797414036002624771379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530531609357335083180919 2295797414036002624771379)
                ·
                  refine ⟨3443696121054003937157069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295797414036002624771379 3443696121054003937157069)
                  ·
                    refine ⟨1291386045395251476433901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443696121054003937157069 1291386045395251476433901)
                    ·
                      refine ⟨484269767023219303662713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1291386045395251476433901 484269767023219303662713)
                      ·
                        rfl

theorem cell23_943112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_943112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943112 prefixEnd_943112 := by exact prefixLift 943112
  have htrace : WordTrace (prefixWord ++ tailWord_943112) baseStart_943112 baseEnd_943112 := by
    simpa [prefixWord, tailWord_943112, baseEnd_943112] using wordTrace_append hprefix tailTrace_943112
  have hstable : (prefixWord ++ tailWord_943112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943112).length < 2 ^ (prefixWord ++ tailWord_943112).sum := by decide
  have hdescent : baseEnd_943112 < baseStart_943112 := by decide
  rcases family_descends (prefixWord ++ tailWord_943112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943152 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2]
def baseStart_943152 : Nat := 118140960795 + 943152 * 2 ^ 59
def prefixEnd_943152 : Nat := 4983230072969 + 3 ^ 40 * 943152 * 2
def baseEnd_943152 : Nat := 484290306249399147162529

theorem tailTrace_943152 : CollatzResearch.WordTrace tailWord_943152 prefixEnd_943152 484290306249399147162529 := by
  unfold tailWord_943152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17199789739564428191335855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22933052986085904255114473 17199789739564428191335855)
  ·
    refine ⟨25799684609346642287003783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17199789739564428191335855 25799684609346642287003783)
    ·
      refine ⟨38699526914019963430505675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25799684609346642287003783 38699526914019963430505675)
      ·
        refine ⟨58049290371029945145758513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38699526914019963430505675 58049290371029945145758513)
        ·
          refine ⟨43536967778272458859318885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58049290371029945145758513 43536967778272458859318885)
          ·
            refine ⟨8163181458426086036122291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43536967778272458859318885 8163181458426086036122291)
            ·
              refine ⟨12244772187639129054183437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163181458426086036122291 12244772187639129054183437)
              ·
                refine ⟨4591789570364673395318789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12244772187639129054183437 4591789570364673395318789)
                ·
                  refine ⟨860960544443376261622273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4591789570364673395318789 860960544443376261622273)
                  ·
                    refine ⟨645720408332532196216705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 860960544443376261622273 645720408332532196216705)
                    ·
                      refine ⟨484290306249399147162529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645720408332532196216705 484290306249399147162529)
                      ·
                        rfl

theorem cell23_943152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2].length) (baseStart_943152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943152 prefixEnd_943152 := by exact prefixLift 943152
  have htrace : WordTrace (prefixWord ++ tailWord_943152) baseStart_943152 baseEnd_943152 := by
    simpa [prefixWord, tailWord_943152, baseEnd_943152] using wordTrace_append hprefix tailTrace_943152
  have hstable : (prefixWord ++ tailWord_943152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943152).length < 2 ^ (prefixWord ++ tailWord_943152).sum := by decide
  have hdescent : baseEnd_943152 < baseStart_943152 := by decide
  rcases family_descends (prefixWord ++ tailWord_943152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943190 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_943190 : Nat := 118140960795 + 943190 * 2 ^ 59
def prefixEnd_943190 : Nat := 4983230072969 + 3 ^ 40 * 943190 * 2
def baseEnd_943190 : Nat := 484309818514269998487355

theorem tailTrace_943190 : CollatzResearch.WordTrace tailWord_943190 prefixEnd_943190 484309818514269998487355 := by
  unfold tailWord_943190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150060340811949304534689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22933976968660792581703349 2150060340811949304534689)
  ·
    refine ⟨1612545255608961978401017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2150060340811949304534689 1612545255608961978401017)
    ·
      refine ⟨1209408941706721483800763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612545255608961978401017 1209408941706721483800763)
      ·
        refine ⟨1814113412560082225701145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209408941706721483800763 1814113412560082225701145)
        ·
          refine ⟨1360585059420061669275859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814113412560082225701145 1360585059420061669275859)
          ·
            refine ⟨2040877589130092503913789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360585059420061669275859 2040877589130092503913789)
            ·
              refine ⟨765329095923784688967671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040877589130092503913789 765329095923784688967671)
              ·
                refine ⟨1147993643885677033451507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765329095923784688967671 1147993643885677033451507)
                ·
                  refine ⟨1721990465828515550177261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147993643885677033451507 1721990465828515550177261)
                  ·
                    refine ⟨645746424685693331316473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721990465828515550177261 645746424685693331316473)
                    ·
                      refine ⟨484309818514269998487355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645746424685693331316473 484309818514269998487355)
                      ·
                        rfl

theorem cell23_943190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_943190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943190 prefixEnd_943190 := by exact prefixLift 943190
  have htrace : WordTrace (prefixWord ++ tailWord_943190) baseStart_943190 baseEnd_943190 := by
    simpa [prefixWord, tailWord_943190, baseEnd_943190] using wordTrace_append hprefix tailTrace_943190
  have hstable : (prefixWord ++ tailWord_943190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943190).length < 2 ^ (prefixWord ++ tailWord_943190).sum := by decide
  have hdescent : baseEnd_943190 < baseStart_943190 := by decide
  rcases family_descends (prefixWord ++ tailWord_943190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943205 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_943205 : Nat := 118140960795 + 943205 * 2 ^ 59
def prefixEnd_943205 : Nat := 4983230072969 + 3 ^ 40 * 943205 * 2
def baseEnd_943205 : Nat := 161439173574695813266595

theorem tailTrace_943205 : CollatzResearch.WordTrace tailWord_943205 prefixEnd_943205 161439173574695813266595 := by
  unfold tailWord_943205
  simp only [CollatzResearch.WordTrace]
  refine ⟨34401512547936846434351069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22934341698624564289567379 34401512547936846434351069)
  ·
    refine ⟨12900567205476317412881651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34401512547936846434351069 12900567205476317412881651)
    ·
      refine ⟨19350850808214476119322477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12900567205476317412881651 19350850808214476119322477)
      ·
        refine ⟨7256569053080428544745929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19350850808214476119322477 7256569053080428544745929)
        ·
          refine ⟨5442426789810321408559447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7256569053080428544745929 5442426789810321408559447)
          ·
            refine ⟨8163640184715482112839171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442426789810321408559447 8163640184715482112839171)
            ·
              refine ⟨12245460277073223169258757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163640184715482112839171 12245460277073223169258757)
              ·
                refine ⟨2296023801951229344236017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12245460277073223169258757 2296023801951229344236017)
                ·
                  refine ⟨1722017851463422008177013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2296023801951229344236017 1722017851463422008177013)
                  ·
                    refine ⟨161439173574695813266595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1722017851463422008177013 161439173574695813266595)
                    ·
                      rfl

theorem cell23_943205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_943205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943205 prefixEnd_943205 := by exact prefixLift 943205
  have htrace : WordTrace (prefixWord ++ tailWord_943205) baseStart_943205 baseEnd_943205 := by
    simpa [prefixWord, tailWord_943205, baseEnd_943205] using wordTrace_append hprefix tailTrace_943205
  have hstable : (prefixWord ++ tailWord_943205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943205).length < 2 ^ (prefixWord ++ tailWord_943205).sum := by decide
  have hdescent : baseEnd_943205 < baseStart_943205 := by decide
  rcases family_descends (prefixWord ++ tailWord_943205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943209 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 5]
def baseStart_943209 : Nat := 118140960795 + 943209 * 2 ^ 59
def prefixEnd_943209 : Nat := 4983230072969 + 3 ^ 40 * 943209 * 2
def baseEnd_943209 : Nat := 53813286071856158238863

theorem tailTrace_943209 : CollatzResearch.WordTrace tailWord_943209 prefixEnd_943209 53813286071856158238863 := by
  unfold tailWord_943209
  simp only [CollatzResearch.WordTrace]
  refine ⟨34401658439922355117496681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22934438959948236744997787 34401658439922355117496681)
  ·
    refine ⟨25801243829941766338122511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34401658439922355117496681 25801243829941766338122511)
    ·
      refine ⟨38701865744912649507183767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25801243829941766338122511 38701865744912649507183767)
      ·
        refine ⟨58052798617368974260775651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38701865744912649507183767 58052798617368974260775651)
        ·
          refine ⟨87079197926053461391163477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58052798617368974260775651 87079197926053461391163477)
          ·
            refine ⟨1020459350695939000677697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 87079197926053461391163477 1020459350695939000677697)
            ·
              refine ⟨765344513021954250508273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020459350695939000677697 765344513021954250508273)
              ·
                refine ⟨574008384766465687881205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765344513021954250508273 574008384766465687881205)
                ·
                  refine ⟨53813286071856158238863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574008384766465687881205 53813286071856158238863)
                  ·
                    rfl

theorem cell23_943209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 5].length) (baseStart_943209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943209 prefixEnd_943209 := by exact prefixLift 943209
  have htrace : WordTrace (prefixWord ++ tailWord_943209) baseStart_943209 baseEnd_943209 := by
    simpa [prefixWord, tailWord_943209, baseEnd_943209] using wordTrace_append hprefix tailTrace_943209
  have hstable : (prefixWord ++ tailWord_943209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943209).length < 2 ^ (prefixWord ++ tailWord_943209).sum := by decide
  have hdescent : baseEnd_943209 < baseStart_943209 := by decide
  rcases family_descends (prefixWord ++ tailWord_943209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943242 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_943242 : Nat := 118140960795 + 943242 * 2 ^ 59
def prefixEnd_943242 : Nat := 4983230072969 + 3 ^ 40 * 943242 * 2
def baseEnd_943242 : Nat := 484336519508303795037115

theorem tailTrace_943242 : CollatzResearch.WordTrace tailWord_943242 prefixEnd_943242 484336519508303795037115 := by
  unfold tailWord_943242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600715512200700438361995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22935241365868534502298653 8600715512200700438361995)
  ·
    refine ⟨12901073268301050657542993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8600715512200700438361995 12901073268301050657542993)
    ·
      refine ⟨9675804951225787993157245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12901073268301050657542993 9675804951225787993157245)
      ·
        refine ⟨3628426856709670497433967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9675804951225787993157245 3628426856709670497433967)
        ·
          refine ⟨5442640285064505746150951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628426856709670497433967 5442640285064505746150951)
          ·
            refine ⟨8163960427596758619226427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442640285064505746150951 8163960427596758619226427)
            ·
              refine ⟨12245940641395137928839641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163960427596758619226427 12245940641395137928839641)
              ·
                refine ⟨9184455481046353446629731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12245940641395137928839641 9184455481046353446629731)
                ·
                  refine ⟨13776683221569530169944597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184455481046353446629731 13776683221569530169944597)
                  ·
                    refine ⟨645782026011071726716153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13776683221569530169944597 645782026011071726716153)
                    ·
                      refine ⟨484336519508303795037115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645782026011071726716153 484336519508303795037115)
                      ·
                        rfl

theorem cell23_943242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_943242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943242 prefixEnd_943242 := by exact prefixLift 943242
  have htrace : WordTrace (prefixWord ++ tailWord_943242) baseStart_943242 baseEnd_943242 := by
    simpa [prefixWord, tailWord_943242, baseEnd_943242] using wordTrace_append hprefix tailTrace_943242
  have hstable : (prefixWord ++ tailWord_943242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943242).length < 2 ^ (prefixWord ++ tailWord_943242).sum := by decide
  have hdescent : baseEnd_943242 < baseStart_943242 := by decide
  rcases family_descends (prefixWord ++ tailWord_943242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943255 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_943255 : Nat := 118140960795 + 943255 * 2 ^ 59
def prefixEnd_943255 : Nat := 4983230072969 + 3 ^ 40 * 943255 * 2
def baseEnd_943255 : Nat := 484343194756812244174555

theorem tailTrace_943255 : CollatzResearch.WordTrace tailWord_943255 prefixEnd_943255 484343194756812244174555 := by
  unfold tailWord_943255
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403336197755704973671219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22935557465170469982447479 34403336197755704973671219)
  ·
    refine ⟨51605004296633557460506829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34403336197755704973671219 51605004296633557460506829)
    ·
      refine ⟨19351876611237584047690061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51605004296633557460506829 19351876611237584047690061)
      ·
        refine ⟨7256953729214094017883773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19351876611237584047690061 7256953729214094017883773)
        ·
          refine ⟨2721357648455285256706415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7256953729214094017883773 2721357648455285256706415)
          ·
            refine ⟨4082036472682927885059623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721357648455285256706415 4082036472682927885059623)
            ·
              refine ⟨6123054709024391827589435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082036472682927885059623 6123054709024391827589435)
              ·
                refine ⟨9184582063536587741384153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123054709024391827589435 9184582063536587741384153)
                ·
                  refine ⟨6888436547652440806038115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184582063536587741384153 6888436547652440806038115)
                  ·
                    refine ⟨10332654821478661209057173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888436547652440806038115 10332654821478661209057173)
                    ·
                      refine ⟨484343194756812244174555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10332654821478661209057173 484343194756812244174555)
                      ·
                        rfl

theorem cell23_943255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_943255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943255 prefixEnd_943255 := by exact prefixLift 943255
  have htrace : WordTrace (prefixWord ++ tailWord_943255) baseStart_943255 baseEnd_943255 := by
    simpa [prefixWord, tailWord_943255, baseEnd_943255] using wordTrace_append hprefix tailTrace_943255
  have hstable : (prefixWord ++ tailWord_943255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943255).length < 2 ^ (prefixWord ++ tailWord_943255).sum := by decide
  have hdescent : baseEnd_943255 < baseStart_943255 := by decide
  rcases family_descends (prefixWord ++ tailWord_943255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943265 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 8]
def baseStart_943265 : Nat := 118140960795 + 943265 * 2 ^ 59
def prefixEnd_943265 : Nat := 4983230072969 + 3 ^ 40 * 943265 * 2
def baseEnd_943265 : Nat := 53816481062595245005501

theorem tailTrace_943265 : CollatzResearch.WordTrace tailWord_943265 prefixEnd_943265 53816481062595245005501 := by
  unfold tailWord_943265
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403700927719476681535249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22935800618479651121023499 34403700927719476681535249)
  ·
    refine ⟨25802775695789607511151437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34403700927719476681535249 25802775695789607511151437)
    ·
      refine ⟨9676040885921102816681789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25802775695789607511151437 9676040885921102816681789)
      ·
        refine ⟨3628515332220413556255671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9676040885921102816681789 3628515332220413556255671)
        ·
          refine ⟨5442772998330620334383507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628515332220413556255671 5442772998330620334383507)
          ·
            refine ⟨8164159497495930501575261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442772998330620334383507 8164159497495930501575261)
            ·
              refine ⟨3061559811560973938090723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8164159497495930501575261 3061559811560973938090723)
              ·
                refine ⟨4592339717341460907136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061559811560973938090723 4592339717341460907136085)
                ·
                  refine ⟨53816481062595245005501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4592339717341460907136085 53816481062595245005501)
                  ·
                    rfl

theorem cell23_943265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_943265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943265 prefixEnd_943265 := by exact prefixLift 943265
  have htrace : WordTrace (prefixWord ++ tailWord_943265) baseStart_943265 baseEnd_943265 := by
    simpa [prefixWord, tailWord_943265, baseEnd_943265] using wordTrace_append hprefix tailTrace_943265
  have hstable : (prefixWord ++ tailWord_943265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943265).length < 2 ^ (prefixWord ++ tailWord_943265).sum := by decide
  have hdescent : baseEnd_943265 < baseStart_943265 := by decide
  rcases family_descends (prefixWord ++ tailWord_943265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943269 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_943269 : Nat := 118140960795 + 943269 * 2 ^ 59
def prefixEnd_943269 : Nat := 4983230072969 + 3 ^ 40 * 943269 * 2
def baseEnd_943269 : Nat := 161450127828658396466497

theorem tailTrace_943269 : CollatzResearch.WordTrace tailWord_943269 prefixEnd_943269 161450127828658396466497 := by
  unfold tailWord_943269
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403846819704985364680861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22935897879803323576453907 34403846819704985364680861)
  ·
    refine ⟨12901442557389369511755323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34403846819704985364680861 12901442557389369511755323)
    ·
      refine ⟨19352163836084054267632985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901442557389369511755323 19352163836084054267632985)
      ·
        refine ⟨14514122877063040700724739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19352163836084054267632985 14514122877063040700724739)
        ·
          refine ⟨21771184315594561051087109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14514122877063040700724739 21771184315594561051087109)
          ·
            refine ⟨4082097059173980197078833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21771184315594561051087109 4082097059173980197078833)
            ·
              refine ⟨3061572794380485147809125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082097059173980197078833 3061572794380485147809125)
              ·
                refine ⟨574044898946340965214211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061572794380485147809125 574044898946340965214211)
                ·
                  refine ⟨861067348419511447821317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574044898946340965214211 861067348419511447821317)
                  ·
                    refine ⟨161450127828658396466497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861067348419511447821317 161450127828658396466497)
                    ·
                      rfl

theorem cell23_943269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_943269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943269 prefixEnd_943269 := by exact prefixLift 943269
  have htrace : WordTrace (prefixWord ++ tailWord_943269) baseStart_943269 baseEnd_943269 := by
    simpa [prefixWord, tailWord_943269, baseEnd_943269] using wordTrace_append hprefix tailTrace_943269
  have hstable : (prefixWord ++ tailWord_943269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943269).length < 2 ^ (prefixWord ++ tailWord_943269).sum := by decide
  have hdescent : baseEnd_943269 < baseStart_943269 := by decide
  rcases family_descends (prefixWord ++ tailWord_943269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943295 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 3, 5]
def baseStart_943295 : Nat := 118140960795 + 943295 * 2 ^ 59
def prefixEnd_943295 : Nat := 4983230072969 + 3 ^ 40 * 943295 * 2
def baseEnd_943295 : Nat := 161454577994330695891457

theorem tailTrace_943295 : CollatzResearch.WordTrace tailWord_943295 prefixEnd_943295 161454577994330695891457 := by
  unfold tailWord_943295
  simp only [CollatzResearch.WordTrace]
  refine ⟨34404795117610791805127339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22936530078407194536751559 34404795117610791805127339)
  ·
    refine ⟨51607192676416187707691009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34404795117610791805127339 51607192676416187707691009)
    ·
      refine ⟨38705394507312140780768257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51607192676416187707691009 38705394507312140780768257)
      ·
        refine ⟨29029045880484105585576193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38705394507312140780768257 29029045880484105585576193)
        ·
          refine ⟨21771784410363079189182145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29029045880484105585576193 21771784410363079189182145)
          ·
            refine ⟨16328838307772309391886609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21771784410363079189182145 16328838307772309391886609)
            ·
              refine ⟨12246628730829232043914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16328838307772309391886609 12246628730829232043914957)
              ·
                refine ⟨4592485774060962016468109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12246628730829232043914957 4592485774060962016468109)
                ·
                  refine ⟨1722182165272860756175541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4592485774060962016468109 1722182165272860756175541)
                  ·
                    refine ⟨161454577994330695891457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1722182165272860756175541 161454577994330695891457)
                    ·
                      rfl

theorem cell23_943295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_943295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943295 prefixEnd_943295 := by exact prefixLift 943295
  have htrace : WordTrace (prefixWord ++ tailWord_943295) baseStart_943295 baseEnd_943295 := by
    simpa [prefixWord, tailWord_943295, baseEnd_943295] using wordTrace_append hprefix tailTrace_943295
  have hstable : (prefixWord ++ tailWord_943295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943295).length < 2 ^ (prefixWord ++ tailWord_943295).sum := by decide
  have hdescent : baseEnd_943295 < baseStart_943295 := by decide
  rcases family_descends (prefixWord ++ tailWord_943295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943346 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_943346 : Nat := 118140960795 + 943346 * 2 ^ 59
def prefixEnd_943346 : Nat := 4983230072969 + 3 ^ 40 * 943346 * 2
def baseEnd_943346 : Nat := 161463307165457129378879

theorem tailTrace_943346 : CollatzResearch.WordTrace tailWord_943346 prefixEnd_943346 161463307165457129378879 := by
  unfold tailWord_943346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601663810106506878808473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22937770160284018343489261 8601663810106506878808473)
  ·
    refine ⟨6451247857579880159106355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8601663810106506878808473 6451247857579880159106355)
    ·
      refine ⟨9676871786369820238659533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6451247857579880159106355 9676871786369820238659533)
      ·
        refine ⟨3628826919888682589497325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9676871786369820238659533 3628826919888682589497325)
        ·
          refine ⟨1360810094958255971061497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3628826919888682589497325 1360810094958255971061497)
          ·
            refine ⟨1020607571218691978296123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360810094958255971061497 1020607571218691978296123)
            ·
              refine ⟨1530911356828037967444185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020607571218691978296123 1530911356828037967444185)
              ·
                refine ⟨1148183517621028475583139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530911356828037967444185 1148183517621028475583139)
                ·
                  refine ⟨1722275276431542713374709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148183517621028475583139 1722275276431542713374709)
                  ·
                    refine ⟨161463307165457129378879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1722275276431542713374709 161463307165457129378879)
                    ·
                      rfl

theorem cell23_943346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_943346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943346 prefixEnd_943346 := by exact prefixLift 943346
  have htrace : WordTrace (prefixWord ++ tailWord_943346) baseStart_943346 baseEnd_943346 := by
    simpa [prefixWord, tailWord_943346, baseEnd_943346] using wordTrace_append hprefix tailTrace_943346
  have hstable : (prefixWord ++ tailWord_943346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943346).length < 2 ^ (prefixWord ++ tailWord_943346).sum := by decide
  have hdescent : baseEnd_943346 < baseStart_943346 := by decide
  rcases family_descends (prefixWord ++ tailWord_943346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943383 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 1, 2, 2]
def baseStart_943383 : Nat := 118140960795 + 943383 * 2 ^ 59
def prefixEnd_943383 : Nat := 4983230072969 + 3 ^ 40 * 943383 * 2
def baseEnd_943383 : Nat := 484408920280587743373967

theorem tailTrace_943383 : CollatzResearch.WordTrace tailWord_943383 prefixEnd_943383 484408920280587743373967 := by
  unfold tailWord_943383
  simp only [CollatzResearch.WordTrace]
  refine ⟨34408004741291982834330803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22938669827527988556220535 34408004741291982834330803)
  ·
    refine ⟨51612007111937974251496205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34408004741291982834330803 51612007111937974251496205)
    ·
      refine ⟨19354502666976740344311077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51612007111937974251496205 19354502666976740344311077)
      ·
        refine ⟨3628969250058138814558327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19354502666976740344311077 3628969250058138814558327)
        ·
          refine ⟨5443453875087208221837491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628969250058138814558327 5443453875087208221837491)
          ·
            refine ⟨8165180812630812332756237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443453875087208221837491 8165180812630812332756237)
            ·
              refine ⟨3061942804736554624783589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8165180812630812332756237 3061942804736554624783589)
              ·
                refine ⟨574114275888103992146923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061942804736554624783589 574114275888103992146923)
                ·
                  refine ⟨861171413832155988220385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574114275888103992146923 861171413832155988220385)
                  ·
                    refine ⟨645878560374116991165289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861171413832155988220385 645878560374116991165289)
                    ·
                      refine ⟨484408920280587743373967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645878560374116991165289 484408920280587743373967)
                      ·
                        rfl

theorem cell23_943383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_943383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943383 prefixEnd_943383 := by exact prefixLift 943383
  have htrace : WordTrace (prefixWord ++ tailWord_943383) baseStart_943383 baseEnd_943383 := by
    simpa [prefixWord, tailWord_943383, baseEnd_943383] using wordTrace_append hprefix tailTrace_943383
  have hstable : (prefixWord ++ tailWord_943383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943383).length < 2 ^ (prefixWord ++ tailWord_943383).sum := by decide
  have hdescent : baseEnd_943383 < baseStart_943383 := by decide
  rcases family_descends (prefixWord ++ tailWord_943383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943389 : List Nat := [1, 4, 2, 3, 1, 3, 1, 8]
def baseStart_943389 : Nat := 118140960795 + 943389 * 2 ^ 59
def prefixEnd_943389 : Nat := 4983230072969 + 3 ^ 40 * 943389 * 2
def baseEnd_943389 : Nat := 17941185228315359996257

theorem tailTrace_943389 : CollatzResearch.WordTrace tailWord_943389 prefixEnd_943389 17941185228315359996257 := by
  unfold tailWord_943389
  simp only [CollatzResearch.WordTrace]
  refine ⟨34408223579270245859049221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22938815719513497239366147 34408223579270245859049221)
  ·
    refine ⟨6451541921113171098571729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34408223579270245859049221 6451541921113171098571729)
    ·
      refine ⟨4838656440834878323928797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6451541921113171098571729 4838656440834878323928797)
      ·
        refine ⟨1814496165313079371473299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4838656440834878323928797 1814496165313079371473299)
        ·
          refine ⟨2721744247969619057209949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814496165313079371473299 2721744247969619057209949)
          ·
            refine ⟨1020654092988607146453731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2721744247969619057209949 1020654092988607146453731)
            ·
              refine ⟨1530981139482910719680597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020654092988607146453731 1530981139482910719680597)
              ·
                refine ⟨17941185228315359996257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1530981139482910719680597 17941185228315359996257)
                ·
                  rfl

theorem cell23_943389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 8].length) (baseStart_943389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943389 prefixEnd_943389 := by exact prefixLift 943389
  have htrace : WordTrace (prefixWord ++ tailWord_943389) baseStart_943389 baseEnd_943389 := by
    simpa [prefixWord, tailWord_943389, baseEnd_943389] using wordTrace_append hprefix tailTrace_943389
  have hstable : (prefixWord ++ tailWord_943389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943389).length < 2 ^ (prefixWord ++ tailWord_943389).sum := by decide
  have hdescent : baseEnd_943389 < baseStart_943389 := by decide
  rcases family_descends (prefixWord ++ tailWord_943389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943442 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_943442 : Nat := 118140960795 + 943442 * 2 ^ 59
def prefixEnd_943442 : Nat := 4983230072969 + 3 ^ 40 * 943442 * 2
def baseEnd_943442 : Nat := 484439215639203012536195

theorem tailTrace_943442 : CollatzResearch.WordTrace tailWord_943442 prefixEnd_943442 484439215639203012536195 := by
  unfold tailWord_943442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8602539162019558977682145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22940104432052157273819053 8602539162019558977682145)
  ·
    refine ⟨6451904371514669233261609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8602539162019558977682145 6451904371514669233261609)
    ·
      refine ⟨4838928278636001924946207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6451904371514669233261609 4838928278636001924946207)
      ·
        refine ⟨7258392417954002887419311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4838928278636001924946207 7258392417954002887419311)
        ·
          refine ⟨10887588626931004331128967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7258392417954002887419311 10887588626931004331128967)
          ·
            refine ⟨16331382940396506496693451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10887588626931004331128967 16331382940396506496693451)
            ·
              refine ⟨24497074410594759745040177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16331382940396506496693451 24497074410594759745040177)
              ·
                refine ⟨18372805807946069808780133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24497074410594759745040177 18372805807946069808780133)
                ·
                  refine ⟨3444901088989888089146275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18372805807946069808780133 3444901088989888089146275)
                  ·
                    refine ⟨5167351633484832133719413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3444901088989888089146275 5167351633484832133719413)
                    ·
                      refine ⟨484439215639203012536195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5167351633484832133719413 484439215639203012536195)
                      ·
                        rfl

theorem cell23_943442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_943442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943442 prefixEnd_943442 := by exact prefixLift 943442
  have htrace : WordTrace (prefixWord ++ tailWord_943442) baseStart_943442 baseEnd_943442 := by
    simpa [prefixWord, tailWord_943442, baseEnd_943442] using wordTrace_append hprefix tailTrace_943442
  have hstable : (prefixWord ++ tailWord_943442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943442).length < 2 ^ (prefixWord ++ tailWord_943442).sum := by decide
  have hdescent : baseEnd_943442 < baseStart_943442 := by decide
  rcases family_descends (prefixWord ++ tailWord_943442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943456 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2]
def baseStart_943456 : Nat := 118140960795 + 943456 * 2 ^ 59
def prefixEnd_943456 : Nat := 4983230072969 + 3 ^ 40 * 943456 * 2
def baseEnd_943456 : Nat := 484446404368365957761131

theorem tailTrace_943456 : CollatzResearch.WordTrace tailWord_943456 prefixEnd_943456 484446404368365957761131 := by
  unfold tailWord_943456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17205333635013758150869111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22940444846685010867825481 17205333635013758150869111)
  ·
    refine ⟨25808000452520637226303667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17205333635013758150869111 25808000452520637226303667)
    ·
      refine ⟨38712000678780955839455501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25808000452520637226303667 38712000678780955839455501)
      ·
        refine ⟨14517000254542858439795813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38712000678780955839455501 14517000254542858439795813)
        ·
          refine ⟨2721937547726785957461715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14517000254542858439795813 2721937547726785957461715)
          ·
            refine ⟨4082906321590178936192573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721937547726785957461715 4082906321590178936192573)
            ·
              refine ⟨1531089870596317101072215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4082906321590178936192573 1531089870596317101072215)
              ·
                refine ⟨2296634805894475651608323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531089870596317101072215 2296634805894475651608323)
                ·
                  refine ⟨3444952208841713477412485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296634805894475651608323 3444952208841713477412485)
                  ·
                    refine ⟨645928539157821277014841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444952208841713477412485 645928539157821277014841)
                    ·
                      refine ⟨484446404368365957761131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645928539157821277014841 484446404368365957761131)
                      ·
                        rfl

theorem cell23_943456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_943456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943456 prefixEnd_943456 := by exact prefixLift 943456
  have htrace : WordTrace (prefixWord ++ tailWord_943456) baseStart_943456 baseEnd_943456 := by
    simpa [prefixWord, tailWord_943456, baseEnd_943456] using wordTrace_append hprefix tailTrace_943456
  have hstable : (prefixWord ++ tailWord_943456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943456).length < 2 ^ (prefixWord ++ tailWord_943456).sum := by decide
  have hdescent : baseEnd_943456 < baseStart_943456 := by decide
  rcases family_descends (prefixWord ++ tailWord_943456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943490 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_943490 : Nat := 118140960795 + 943490 * 2 ^ 59
def prefixEnd_943490 : Nat := 4983230072969 + 3 ^ 40 * 943490 * 2
def baseEnd_943490 : Nat := 484463862710618824735975

theorem tailTrace_943490 : CollatzResearch.WordTrace tailWord_943490 prefixEnd_943490 484463862710618824735975 := by
  unfold tailWord_943490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8602976837976085027118981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22941271567936226738983949 8602976837976085027118981)
  ·
    refine ⟨1613058157120515942584809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8602976837976085027118981 1613058157120515942584809)
    ·
      refine ⟨1209793617840386956938607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1613058157120515942584809 1209793617840386956938607)
      ·
        refine ⟨1814690426760580435407911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209793617840386956938607 1814690426760580435407911)
        ·
          refine ⟨2722035640140870653111867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814690426760580435407911 2722035640140870653111867)
          ·
            refine ⟨4083053460211305979667801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722035640140870653111867 4083053460211305979667801)
            ·
              refine ⟨3062290095158479484750851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083053460211305979667801 3062290095158479484750851)
              ·
                refine ⟨4593435142737719227126277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062290095158479484750851 4593435142737719227126277)
                ·
                  refine ⟨861269089263322355086177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4593435142737719227126277 861269089263322355086177)
                  ·
                    refine ⟨645951816947491766314633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861269089263322355086177 645951816947491766314633)
                    ·
                      refine ⟨484463862710618824735975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645951816947491766314633 484463862710618824735975)
                      ·
                        rfl

theorem cell23_943490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_943490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943490 prefixEnd_943490 := by exact prefixLift 943490
  have htrace : WordTrace (prefixWord ++ tailWord_943490) baseStart_943490 baseEnd_943490 := by
    simpa [prefixWord, tailWord_943490, baseEnd_943490] using wordTrace_append hprefix tailTrace_943490
  have hstable : (prefixWord ++ tailWord_943490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943490).length < 2 ^ (prefixWord ++ tailWord_943490).sum := by decide
  have hdescent : baseEnd_943490 < baseStart_943490 := by decide
  rcases family_descends (prefixWord ++ tailWord_943490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943499 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 5, 2]
def baseStart_943499 : Nat := 118140960795 + 943499 * 2 ^ 59
def prefixEnd_943499 : Nat := 4983230072969 + 3 ^ 40 * 943499 * 2
def baseEnd_943499 : Nat := 484468484036509289523433

theorem tailTrace_943499 : CollatzResearch.WordTrace tailWord_943499 prefixEnd_943499 484468484036509289523433 := by
  unfold tailWord_943499
  simp only [CollatzResearch.WordTrace]
  refine ⟨34412235608871734645553551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22941490405914489763702367 34412235608871734645553551)
  ·
    refine ⟨51618353413307601968330327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34412235608871734645553551 51618353413307601968330327)
    ·
      refine ⟨77427530119961402952495491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51618353413307601968330327 77427530119961402952495491)
      ·
        refine ⟨116141295179942104428743237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77427530119961402952495491 116141295179942104428743237)
        ·
          refine ⟨21776492846239144580389357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116141295179942104428743237 21776492846239144580389357)
          ·
            refine ⟨8166184817339679217646009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21776492846239144580389357 8166184817339679217646009)
            ·
              refine ⟨6124638613004759413234507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8166184817339679217646009 6124638613004759413234507)
              ·
                refine ⟨9186957919507139119851761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6124638613004759413234507 9186957919507139119851761)
                ·
                  refine ⟨6890218439630354339888821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9186957919507139119851761 6890218439630354339888821)
                  ·
                    refine ⟨645957978715345719364577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6890218439630354339888821 645957978715345719364577)
                    ·
                      refine ⟨484468484036509289523433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645957978715345719364577 484468484036509289523433)
                      ·
                        rfl

theorem cell23_943499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5, 2].length) (baseStart_943499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943499 prefixEnd_943499 := by exact prefixLift 943499
  have htrace : WordTrace (prefixWord ++ tailWord_943499) baseStart_943499 baseEnd_943499 := by
    simpa [prefixWord, tailWord_943499, baseEnd_943499] using wordTrace_append hprefix tailTrace_943499
  have hstable : (prefixWord ++ tailWord_943499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943499).length < 2 ^ (prefixWord ++ tailWord_943499).sum := by decide
  have hdescent : baseEnd_943499 < baseStart_943499 := by decide
  rcases family_descends (prefixWord ++ tailWord_943499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943529 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 6, 4, 2]
def baseStart_943529 : Nat := 118140960795 + 943529 * 2 ^ 59
def prefixEnd_943529 : Nat := 4983230072969 + 3 ^ 40 * 943529 * 2
def baseEnd_943529 : Nat := 484483888456144172148295

theorem tailTrace_943529 : CollatzResearch.WordTrace tailWord_943529 prefixEnd_943529 484483888456144172148295 := by
  unfold tailWord_943529
  simp only [CollatzResearch.WordTrace]
  refine ⟨34413329798763049769145641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22942219865842033179430427 34413329798763049769145641)
  ·
    refine ⟨25809997349072287326859231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34413329798763049769145641 25809997349072287326859231)
    ·
      refine ⟨38714996023608430990288847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25809997349072287326859231 38714996023608430990288847)
      ·
        refine ⟨58072494035412646485433271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38714996023608430990288847 58072494035412646485433271)
        ·
          refine ⟨87108741053118969728149907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58072494035412646485433271 87108741053118969728149907)
          ·
            refine ⟨130663111579678454592224861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87108741053118969728149907 130663111579678454592224861)
            ·
              refine ⟨48998666842379420472084323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130663111579678454592224861 48998666842379420472084323)
              ·
                refine ⟨73498000263569130708126485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48998666842379420472084323 73498000263569130708126485)
                ·
                  refine ⟨3445218762354803001943429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73498000263569130708126485 3445218762354803001943429)
                  ·
                    refine ⟨645978517941525562864393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445218762354803001943429 645978517941525562864393)
                    ·
                      refine ⟨484483888456144172148295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 645978517941525562864393 484483888456144172148295)
                      ·
                        rfl

theorem cell23_943529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4, 2].length) (baseStart_943529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943529 prefixEnd_943529 := by exact prefixLift 943529
  have htrace : WordTrace (prefixWord ++ tailWord_943529) baseStart_943529 baseEnd_943529 := by
    simpa [prefixWord, tailWord_943529, baseEnd_943529] using wordTrace_append hprefix tailTrace_943529
  have hstable : (prefixWord ++ tailWord_943529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943529).length < 2 ^ (prefixWord ++ tailWord_943529).sum := by decide
  have hdescent : baseEnd_943529 < baseStart_943529 := by decide
  rcases family_descends (prefixWord ++ tailWord_943529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943552 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 8]
def baseStart_943552 : Nat := 118140960795 + 943552 * 2 ^ 59
def prefixEnd_943552 : Nat := 4983230072969 + 3 ^ 40 * 943552 * 2
def baseEnd_943552 : Nat := 53832855390133064684521

theorem tailTrace_943552 : CollatzResearch.WordTrace tailWord_943552 prefixEnd_943552 53832855390133064684521 := by
  unfold tailWord_943552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207084338839862348616455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22942779118453149798155273 17207084338839862348616455)
  ·
    refine ⟨25810626508259793522924683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17207084338839862348616455 25810626508259793522924683)
    ·
      refine ⟨38715939762389690284387025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25810626508259793522924683 38715939762389690284387025)
      ·
        refine ⟨29036954821792267713290269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38715939762389690284387025 29036954821792267713290269)
        ·
          refine ⟨10888858058172100392483851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29036954821792267713290269 10888858058172100392483851)
          ·
            refine ⟨16333287087258150588725777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10888858058172100392483851 16333287087258150588725777)
            ·
              refine ⟨12249965315443612941544333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16333287087258150588725777 12249965315443612941544333)
              ·
                refine ⟨4593736993291354853079125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12249965315443612941544333 4593736993291354853079125)
                ·
                  refine ⟨53832855390133064684521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4593736993291354853079125 53832855390133064684521)
                  ·
                    rfl

theorem cell23_943552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_943552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943552 prefixEnd_943552 := by exact prefixLift 943552
  have htrace : WordTrace (prefixWord ++ tailWord_943552) baseStart_943552 baseEnd_943552 := by
    simpa [prefixWord, tailWord_943552, baseEnd_943552] using wordTrace_append hprefix tailTrace_943552
  have hstable : (prefixWord ++ tailWord_943552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943552).length < 2 ^ (prefixWord ++ tailWord_943552).sum := by decide
  have hdescent : baseEnd_943552 < baseStart_943552 := by decide
  rcases family_descends (prefixWord ++ tailWord_943552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943613 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_943613 : Nat := 118140960795 + 943613 * 2 ^ 59
def prefixEnd_943613 : Nat := 4983230072969 + 3 ^ 40 * 943613 * 2
def baseEnd_943613 : Nat := 484527020831121843497909

theorem tailTrace_943613 : CollatzResearch.WordTrace tailWord_943613 prefixEnd_943613 484527020831121843497909 := by
  unfold tailWord_943613
  simp only [CollatzResearch.WordTrace]
  refine ⟨34416393530458732115203493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22944262353639154743468995 34416393530458732115203493)
  ·
    refine ⟨6453073786961012271600655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34416393530458732115203493 6453073786961012271600655)
    ·
      refine ⟨9679610680441518407400983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453073786961012271600655 9679610680441518407400983)
      ·
        refine ⟨14519416020662277611101475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679610680441518407400983 14519416020662277611101475)
        ·
          refine ⟨21779124030993416416652213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519416020662277611101475 21779124030993416416652213)
          ·
            refine ⟨2041792877905632789061145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21779124030993416416652213 2041792877905632789061145)
            ·
              refine ⟨1531344658429224591795859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041792877905632789061145 1531344658429224591795859)
              ·
                refine ⟨2297016987643836887693789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531344658429224591795859 2297016987643836887693789)
                ·
                  refine ⟨861381370366438832885171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2297016987643836887693789 861381370366438832885171)
                  ·
                    refine ⟨1292072055549658249327757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 861381370366438832885171 1292072055549658249327757)
                    ·
                      refine ⟨484527020831121843497909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292072055549658249327757 484527020831121843497909)
                      ·
                        rfl

theorem cell23_943613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_943613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943613 prefixEnd_943613 := by exact prefixLift 943613
  have htrace : WordTrace (prefixWord ++ tailWord_943613) baseStart_943613 baseEnd_943613 := by
    simpa [prefixWord, tailWord_943613, baseEnd_943613] using wordTrace_append hprefix tailTrace_943613
  have hstable : (prefixWord ++ tailWord_943613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943613).length < 2 ^ (prefixWord ++ tailWord_943613).sum := by decide
  have hdescent : baseEnd_943613 < baseStart_943613 := by decide
  rcases family_descends (prefixWord ++ tailWord_943613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943619 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4]
def baseStart_943619 : Nat := 118140960795 + 943619 * 2 ^ 59
def prefixEnd_943619 : Nat := 4983230072969 + 3 ^ 40 * 943619 * 2
def baseEnd_943619 : Nat := 484530101715048820022881

theorem tailTrace_943619 : CollatzResearch.WordTrace tailWord_943619 prefixEnd_943619 484530101715048820022881 := by
  unfold tailWord_943619
  simp only [CollatzResearch.WordTrace]
  refine ⟨34416612368436995139921911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22944408245624663426614607 34416612368436995139921911)
  ·
    refine ⟨51624918552655492709882867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34416612368436995139921911 51624918552655492709882867)
    ·
      refine ⟨77437377828983239064824301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51624918552655492709882867 77437377828983239064824301)
      ·
        refine ⟨29039016685868714649309113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77437377828983239064824301 29039016685868714649309113)
        ·
          refine ⟨21779262514401535986981835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29039016685868714649309113 21779262514401535986981835)
          ·
            refine ⟨32668893771602303980472753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779262514401535986981835 32668893771602303980472753)
            ·
              refine ⟨24501670328701727985354565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32668893771602303980472753 24501670328701727985354565)
              ·
                refine ⟨4594063186631573997253981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24501670328701727985354565 4594063186631573997253981)
                ·
                  refine ⟨1722773694986840248970243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4594063186631573997253981 1722773694986840248970243)
                  ·
                    refine ⟨2584160542480260373455365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722773694986840248970243 2584160542480260373455365)
                    ·
                      refine ⟨484530101715048820022881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2584160542480260373455365 484530101715048820022881)
                      ·
                        rfl

theorem cell23_943619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_943619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943619 prefixEnd_943619 := by exact prefixLift 943619
  have htrace : WordTrace (prefixWord ++ tailWord_943619) baseStart_943619 baseEnd_943619 := by
    simpa [prefixWord, tailWord_943619, baseEnd_943619] using wordTrace_append hprefix tailTrace_943619
  have hstable : (prefixWord ++ tailWord_943619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943619).length < 2 ^ (prefixWord ++ tailWord_943619).sum := by decide
  have hdescent : baseEnd_943619 < baseStart_943619 := by decide
  rcases family_descends (prefixWord ++ tailWord_943619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943676 : List Nat := [2, 2, 2, 2, 4, 1, 2, 8]
def baseStart_943676 : Nat := 118140960795 + 943676 * 2 ^ 59
def prefixEnd_943676 : Nat := 4983230072969 + 3 ^ 40 * 943676 * 2
def baseEnd_943676 : Nat := 17946643337494633222597

theorem tailTrace_943676 : CollatzResearch.WordTrace tailWord_943676 prefixEnd_943676 17946643337494633222597 := by
  unfold tailWord_943676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209345664615246937373441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22945794219486995916497921 17209345664615246937373441)
  ·
    refine ⟨12907009248461435203030081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17209345664615246937373441 12907009248461435203030081)
    ·
      refine ⟨9680256936346076402272561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12907009248461435203030081 9680256936346076402272561)
      ·
        refine ⟨7260192702259557301704421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9680256936346076402272561 7260192702259557301704421)
        ·
          refine ⟨1361286131673666994069579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7260192702259557301704421 1361286131673666994069579)
          ·
            refine ⟨2041929197510500491104369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361286131673666994069579 2041929197510500491104369)
            ·
              refine ⟨1531446898132875368328277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041929197510500491104369 1531446898132875368328277)
              ·
                refine ⟨17946643337494633222597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1531446898132875368328277 17946643337494633222597)
                ·
                  rfl

theorem cell23_943676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 8].length) (baseStart_943676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943676 prefixEnd_943676 := by exact prefixLift 943676
  have htrace : WordTrace (prefixWord ++ tailWord_943676) baseStart_943676 baseEnd_943676 := by
    simpa [prefixWord, tailWord_943676, baseEnd_943676] using wordTrace_append hprefix tailTrace_943676
  have hstable : (prefixWord ++ tailWord_943676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943676).length < 2 ^ (prefixWord ++ tailWord_943676).sum := by decide
  have hdescent : baseEnd_943676 < baseStart_943676 := by decide
  rcases family_descends (prefixWord ++ tailWord_943676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943720 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_943720 : Nat := 118140960795 + 943720 * 2 ^ 59
def prefixEnd_943720 : Nat := 4983230072969 + 3 ^ 40 * 943720 * 2
def baseEnd_943720 : Nat := 484581963261152924859917

theorem tailTrace_943720 : CollatzResearch.WordTrace tailWord_943720 prefixEnd_943720 484581963261152924859917 := by
  unfold tailWord_943720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17210148070535544694674307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22946864094047392926232409 17210148070535544694674307)
  ·
    refine ⟨25815222105803317042011461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17210148070535544694674307 25815222105803317042011461)
    ·
      refine ⟨4840354144838121945377149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25815222105803317042011461 4840354144838121945377149)
      ·
        refine ⟨1815132804314295729516431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4840354144838121945377149 1815132804314295729516431)
        ·
          refine ⟨2722699206471443594274647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815132804314295729516431 2722699206471443594274647)
          ·
            refine ⟨4084048809707165391411971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722699206471443594274647 4084048809707165391411971)
            ·
              refine ⟨6126073214560748087117957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084048809707165391411971 6126073214560748087117957)
              ·
                refine ⟨1148638727730140266334617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6126073214560748087117957 1148638727730140266334617)
                ·
                  refine ⟨861479045797605199750963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1148638727730140266334617 861479045797605199750963)
                  ·
                    refine ⟨1292218568696407799626445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 861479045797605199750963 1292218568696407799626445)
                    ·
                      refine ⟨484581963261152924859917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292218568696407799626445 484581963261152924859917)
                      ·
                        rfl

theorem cell23_943720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_943720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943720 prefixEnd_943720 := by exact prefixLift 943720
  have htrace : WordTrace (prefixWord ++ tailWord_943720) baseStart_943720 baseEnd_943720 := by
    simpa [prefixWord, tailWord_943720, baseEnd_943720] using wordTrace_append hprefix tailTrace_943720
  have hstable : (prefixWord ++ tailWord_943720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943720).length < 2 ^ (prefixWord ++ tailWord_943720).sum := by decide
  have hdescent : baseEnd_943720 < baseStart_943720 := by decide
  rcases family_descends (prefixWord ++ tailWord_943720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943729 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_943729 : Nat := 118140960795 + 943729 * 2 ^ 59
def prefixEnd_943729 : Nat := 4983230072969 + 3 ^ 40 * 943729 * 2
def baseEnd_943729 : Nat := 484586584587043389647375

theorem tailTrace_943729 : CollatzResearch.WordTrace tailWord_943729 prefixEnd_943729 484586584587043389647375 := by
  unfold tailWord_943729
  simp only [CollatzResearch.WordTrace]
  refine ⟨34420624398038483926426241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22947082932025655950950827 34420624398038483926426241)
  ·
    refine ⟨25815468298528862944819681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34420624398038483926426241 25815468298528862944819681)
    ·
      refine ⟨19361601223896647208614761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25815468298528862944819681 19361601223896647208614761)
      ·
        refine ⟨14521200917922485406461071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19361601223896647208614761 14521200917922485406461071)
        ·
          refine ⟨21781801376883728109691607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521200917922485406461071 21781801376883728109691607)
          ·
            refine ⟨32672702065325592164537411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781801376883728109691607 32672702065325592164537411)
            ·
              refine ⟨49009053097988388246806117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672702065325592164537411 49009053097988388246806117)
              ·
                refine ⟨9189197455872822796276147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49009053097988388246806117 9189197455872822796276147)
                ·
                  refine ⟨13783796183809234194414221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189197455872822796276147 13783796183809234194414221)
                  ·
                    refine ⟨5168923568928462822905333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13783796183809234194414221 5168923568928462822905333)
                    ·
                      refine ⟨484586584587043389647375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5168923568928462822905333 484586584587043389647375)
                      ·
                        rfl

theorem cell23_943729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_943729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943729 prefixEnd_943729 := by exact prefixLift 943729
  have htrace : WordTrace (prefixWord ++ tailWord_943729) baseStart_943729 baseEnd_943729 := by
    simpa [prefixWord, tailWord_943729, baseEnd_943729] using wordTrace_append hprefix tailTrace_943729
  have hstable : (prefixWord ++ tailWord_943729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943729).length < 2 ^ (prefixWord ++ tailWord_943729).sum := by decide
  have hdescent : baseEnd_943729 < baseStart_943729 := by decide
  rcases family_descends (prefixWord ++ tailWord_943729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943777 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_943777 : Nat := 118140960795 + 943777 * 2 ^ 59
def prefixEnd_943777 : Nat := 4983230072969 + 3 ^ 40 * 943777 * 2
def baseEnd_943777 : Nat := 484611231658459201847155

theorem tailTrace_943777 : CollatzResearch.WordTrace tailWord_943777 prefixEnd_943777 484611231658459201847155 := by
  unfold tailWord_943777
  simp only [CollatzResearch.WordTrace]
  refine ⟨34422375101864588124173585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22948250067909725416115723 34422375101864588124173585)
  ·
    refine ⟨25816781326398441093130189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34422375101864588124173585 25816781326398441093130189)
    ·
      refine ⟨9681292997399415409923821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25816781326398441093130189 9681292997399415409923821)
      ·
        refine ⟨3630484874024780778721433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9681292997399415409923821 3630484874024780778721433)
        ·
          refine ⟨2722863655518585584041075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630484874024780778721433 2722863655518585584041075)
          ·
            refine ⟨4084295483277878376061613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722863655518585584041075 4084295483277878376061613)
            ·
              refine ⟨1531610806229204391023105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4084295483277878376061613 1531610806229204391023105)
              ·
                refine ⟨1148708104671903293267329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531610806229204391023105 1148708104671903293267329)
                ·
                  refine ⟨861531078503927469950497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1148708104671903293267329 861531078503927469950497)
                  ·
                    refine ⟨646148308877945602462873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861531078503927469950497 646148308877945602462873)
                    ·
                      refine ⟨484611231658459201847155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646148308877945602462873 484611231658459201847155)
                      ·
                        rfl

theorem cell23_943777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_943777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943777 prefixEnd_943777 := by exact prefixLift 943777
  have htrace : WordTrace (prefixWord ++ tailWord_943777) baseStart_943777 baseEnd_943777 := by
    simpa [prefixWord, tailWord_943777, baseEnd_943777] using wordTrace_append hprefix tailTrace_943777
  have hstable : (prefixWord ++ tailWord_943777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943777).length < 2 ^ (prefixWord ++ tailWord_943777).sum := by decide
  have hdescent : baseEnd_943777 < baseStart_943777 := by decide
  rcases family_descends (prefixWord ++ tailWord_943777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943816 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_943816 : Nat := 118140960795 + 943816 * 2 ^ 59
def prefixEnd_943816 : Nat := 4983230072969 + 3 ^ 40 * 943816 * 2
def baseEnd_943816 : Nat := 484631257403984549259475

theorem tailTrace_943816 : CollatzResearch.WordTrace tailWord_943816 prefixEnd_943816 484631257403984549259475 := by
  unfold tailWord_943816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211898774361648892421651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22949198365815531856562201 17211898774361648892421651)
  ·
    refine ⟨25817848161542473338632477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17211898774361648892421651 25817848161542473338632477)
    ·
      refine ⟨9681693060578427501987179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25817848161542473338632477 9681693060578427501987179)
      ·
        refine ⟨14522539590867641252980769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9681693060578427501987179 14522539590867641252980769)
        ·
          refine ⟨10891904693150730939735577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14522539590867641252980769 10891904693150730939735577)
          ·
            refine ⟨8168928519863048204801683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10891904693150730939735577 8168928519863048204801683)
            ·
              refine ⟨12253392779794572307202525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168928519863048204801683 12253392779794572307202525)
              ·
                refine ⟨4595022292422964615200947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12253392779794572307202525 4595022292422964615200947)
                ·
                  refine ⟨6892533438634446922801421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595022292422964615200947 6892533438634446922801421)
                  ·
                    refine ⟨2584700039487917596050533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892533438634446922801421 2584700039487917596050533)
                    ·
                      refine ⟨484631257403984549259475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2584700039487917596050533 484631257403984549259475)
                      ·
                        rfl

theorem cell23_943816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_943816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943816 prefixEnd_943816 := by exact prefixLift 943816
  have htrace : WordTrace (prefixWord ++ tailWord_943816) baseStart_943816 baseEnd_943816 := by
    simpa [prefixWord, tailWord_943816, baseEnd_943816] using wordTrace_append hprefix tailTrace_943816
  have hstable : (prefixWord ++ tailWord_943816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943816).length < 2 ^ (prefixWord ++ tailWord_943816).sum := by decide
  have hdescent : baseEnd_943816 < baseStart_943816 := by decide
  rcases family_descends (prefixWord ++ tailWord_943816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943833 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_943833 : Nat := 118140960795 + 943833 * 2 ^ 59
def prefixEnd_943833 : Nat := 4983230072969 + 3 ^ 40 * 943833 * 2
def baseEnd_943833 : Nat := 484639986575110982746897

theorem tailTrace_943833 : CollatzResearch.WordTrace tailWord_943833 prefixEnd_943833 484639986575110982746897 := by
  unfold tailWord_943833
  simp only [CollatzResearch.WordTrace]
  refine ⟨34424417589661709688212153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22949611726441139792141435 34424417589661709688212153)
  ·
    refine ⟨25818313192246282266159115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34424417589661709688212153 25818313192246282266159115)
    ·
      refine ⟨38727469788369423399238673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25818313192246282266159115 38727469788369423399238673)
      ·
        refine ⟨29045602341277067549429005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38727469788369423399238673 29045602341277067549429005)
        ·
          refine ⟨10892100877978900331035877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29045602341277067549429005 10892100877978900331035877)
          ·
            refine ⟨2042268914621043812069227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10892100877978900331035877 2042268914621043812069227)
            ·
              refine ⟨3063403371931565718103841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042268914621043812069227 3063403371931565718103841)
              ·
                refine ⟨2297552528948674288577881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063403371931565718103841 2297552528948674288577881)
                ·
                  refine ⟨1723164396711505716433411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297552528948674288577881 1723164396711505716433411)
                  ·
                    refine ⟨2584746595067258574650117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723164396711505716433411 2584746595067258574650117)
                    ·
                      refine ⟨484639986575110982746897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2584746595067258574650117 484639986575110982746897)
                      ·
                        rfl

theorem cell23_943833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_943833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943833 prefixEnd_943833 := by exact prefixLift 943833
  have htrace : WordTrace (prefixWord ++ tailWord_943833) baseStart_943833 baseEnd_943833 := by
    simpa [prefixWord, tailWord_943833, baseEnd_943833] using wordTrace_append hprefix tailTrace_943833
  have hstable : (prefixWord ++ tailWord_943833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943833).length < 2 ^ (prefixWord ++ tailWord_943833).sum := by decide
  have hdescent : baseEnd_943833 < baseStart_943833 := by decide
  rcases family_descends (prefixWord ++ tailWord_943833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943885 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 5]
def baseStart_943885 : Nat := 118140960795 + 943885 * 2 ^ 59
def prefixEnd_943885 : Nat := 4983230072969 + 3 ^ 40 * 943885 * 2
def baseEnd_943885 : Nat := 53851854174349419921851

theorem tailTrace_943885 : CollatzResearch.WordTrace tailWord_943885 prefixEnd_943885 53851854174349419921851 := by
  unfold tailWord_943885
  simp only [CollatzResearch.WordTrace]
  refine ⟨34426314185473322569105109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22950876123648881712736739 34426314185473322569105109)
  ·
    refine ⟨806866738722030997713401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 34426314185473322569105109 806866738722030997713401)
    ·
      refine ⟨605150054041523248285051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 806866738722030997713401 605150054041523248285051)
      ·
        refine ⟨907725081062284872427577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605150054041523248285051 907725081062284872427577)
        ·
          refine ⟨680793810796713654320683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907725081062284872427577 680793810796713654320683)
          ·
            refine ⟨1021190716195070481481025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680793810796713654320683 1021190716195070481481025)
            ·
              refine ⟨765893037146302861110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021190716195070481481025 765893037146302861110769)
              ·
                refine ⟨574419777859727145833077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765893037146302861110769 574419777859727145833077)
                ·
                  refine ⟨53851854174349419921851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574419777859727145833077 53851854174349419921851)
                  ·
                    rfl

theorem cell23_943885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_943885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943885 prefixEnd_943885 := by exact prefixLift 943885
  have htrace : WordTrace (prefixWord ++ tailWord_943885) baseStart_943885 baseEnd_943885 := by
    simpa [prefixWord, tailWord_943885, baseEnd_943885] using wordTrace_append hprefix tailTrace_943885
  have hstable : (prefixWord ++ tailWord_943885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943885).length < 2 ^ (prefixWord ++ tailWord_943885).sum := by decide
  have hdescent : baseEnd_943885 < baseStart_943885 := by decide
  rcases family_descends (prefixWord ++ tailWord_943885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943890 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_943890 : Nat := 118140960795 + 943890 * 2 ^ 59
def prefixEnd_943890 : Nat := 4983230072969 + 3 ^ 40 * 943890 * 2
def baseEnd_943890 : Nat := 53852139441379695526015

theorem tailTrace_943890 : CollatzResearch.WordTrace tailWord_943890 prefixEnd_943890 53852139441379695526015 := by
  unfold tailWord_943890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8606624137613802105759281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22950997700303472282024749 8606624137613802105759281)
  ·
    refine ⟨6454968103210351579319461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8606624137613802105759281 6454968103210351579319461)
    ·
      refine ⟨1210306519351940921122399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6454968103210351579319461 1210306519351940921122399)
      ·
        refine ⟨1815459779027911381683599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210306519351940921122399 1815459779027911381683599)
        ·
          refine ⟨2723189668541867072525399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815459779027911381683599 2723189668541867072525399)
          ·
            refine ⟨4084784502812800608788099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723189668541867072525399 4084784502812800608788099)
            ·
              refine ⟨6127176754219200913182149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084784502812800608788099 6127176754219200913182149)
              ·
                refine ⟨1148845641416100171221653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6127176754219200913182149 1148845641416100171221653)
                ·
                  refine ⟨53852139441379695526015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1148845641416100171221653 53852139441379695526015)
                  ·
                    rfl

theorem cell23_943890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_943890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943890 prefixEnd_943890 := by exact prefixLift 943890
  have htrace : WordTrace (prefixWord ++ tailWord_943890) baseStart_943890 baseEnd_943890 := by
    simpa [prefixWord, tailWord_943890, baseEnd_943890] using wordTrace_append hprefix tailTrace_943890
  have hstable : (prefixWord ++ tailWord_943890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943890).length < 2 ^ (prefixWord ++ tailWord_943890).sum := by decide
  have hdescent : baseEnd_943890 < baseStart_943890 := by decide
  rcases family_descends (prefixWord ++ tailWord_943890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943900 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_943900 : Nat := 118140960795 + 943900 * 2 ^ 59
def prefixEnd_943900 : Nat := 4983230072969 + 3 ^ 40 * 943900 * 2
def baseEnd_943900 : Nat := 484674389778962220609089

theorem tailTrace_943900 : CollatzResearch.WordTrace tailWord_943900 prefixEnd_943900 484674389778962220609089 := by
  unfold tailWord_943900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17213430640209490065450577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22951240853612653420600769 17213430640209490065450577)
  ·
    refine ⟨12910072980157117549087933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17213430640209490065450577 12910072980157117549087933)
    ·
      refine ⟨4841277367558919080907975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12910072980157117549087933 4841277367558919080907975)
      ·
        refine ⟨7261916051338378621361963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841277367558919080907975 7261916051338378621361963)
        ·
          refine ⟨10892874077007567932042945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261916051338378621361963 10892874077007567932042945)
          ·
            refine ⟨8169655557755675949032209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10892874077007567932042945 8169655557755675949032209)
            ·
              refine ⟨6127241668316756961774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8169655557755675949032209 6127241668316756961774157)
              ·
                refine ⟨2297715625618783860665309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6127241668316756961774157 2297715625618783860665309)
                ·
                  refine ⟨861643359607043947749491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2297715625618783860665309 861643359607043947749491)
                  ·
                    refine ⟨1292465039410565921624237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 861643359607043947749491 1292465039410565921624237)
                    ·
                      refine ⟨484674389778962220609089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292465039410565921624237 484674389778962220609089)
                      ·
                        rfl

theorem cell23_943900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_943900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943900 prefixEnd_943900 := by exact prefixLift 943900
  have htrace : WordTrace (prefixWord ++ tailWord_943900) baseStart_943900 baseEnd_943900 := by
    simpa [prefixWord, tailWord_943900, baseEnd_943900] using wordTrace_append hprefix tailTrace_943900
  have hstable : (prefixWord ++ tailWord_943900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943900).length < 2 ^ (prefixWord ++ tailWord_943900).sum := by decide
  have hdescent : baseEnd_943900 < baseStart_943900 := by decide
  rcases family_descends (prefixWord ++ tailWord_943900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943934 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_943934 : Nat := 118140960795 + 943934 * 2 ^ 59
def prefixEnd_943934 : Nat := 4983230072969 + 3 ^ 40 * 943934 * 2
def baseEnd_943934 : Nat := 484691848121215087583933

theorem tailTrace_943934 : CollatzResearch.WordTrace tailWord_943934 prefixEnd_943934 484691848121215087583933 := by
  unfold tailWord_943934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303512670286975492204857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22952067574863869291759237 4303512670286975492204857)
  ·
    refine ⟨3227634502715231619153643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4303512670286975492204857 3227634502715231619153643)
    ·
      refine ⟨4841451754072847428730465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227634502715231619153643 4841451754072847428730465)
      ·
        refine ⟨3631088815554635571547849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4841451754072847428730465 3631088815554635571547849)
        ·
          refine ⟨2723316611665976678660887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631088815554635571547849 2723316611665976678660887)
          ·
            refine ⟨4084974917498965017991331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723316611665976678660887 4084974917498965017991331)
            ·
              refine ⟨6127462376248447526986997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084974917498965017991331 6127462376248447526986997)
              ·
                refine ⟨574449597773291955655031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6127462376248447526986997 574449597773291955655031)
                ·
                  refine ⟨861674396659937933482547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574449597773291955655031 861674396659937933482547)
                  ·
                    refine ⟨1292511594989906900223821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 861674396659937933482547 1292511594989906900223821)
                    ·
                      refine ⟨484691848121215087583933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292511594989906900223821 484691848121215087583933)
                      ·
                        rfl

theorem cell23_943934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_943934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943934 prefixEnd_943934 := by exact prefixLift 943934
  have htrace : WordTrace (prefixWord ++ tailWord_943934) baseStart_943934 baseEnd_943934 := by
    simpa [prefixWord, tailWord_943934, baseEnd_943934] using wordTrace_append hprefix tailTrace_943934
  have hstable : (prefixWord ++ tailWord_943934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943934).length < 2 ^ (prefixWord ++ tailWord_943934).sum := by decide
  have hdescent : baseEnd_943934 < baseStart_943934 := by decide
  rcases family_descends (prefixWord ++ tailWord_943934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943936 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_943936 : Nat := 118140960795 + 943936 * 2 ^ 59
def prefixEnd_943936 : Nat := 4983230072969 + 3 ^ 40 * 943936 * 2
def baseEnd_943936 : Nat := 484692875082524079758923

theorem tailTrace_943936 : CollatzResearch.WordTrace tailWord_943936 prefixEnd_943936 484692875082524079758923 := by
  unfold tailWord_943936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214087154144279139605831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22952116205525705519474441 17214087154144279139605831)
  ·
    refine ⟨25821130731216418709408747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17214087154144279139605831 25821130731216418709408747)
    ·
      refine ⟨38731696096824628064113121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25821130731216418709408747 38731696096824628064113121)
      ·
        refine ⟨29048772072618471048084841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38731696096824628064113121 29048772072618471048084841)
        ·
          refine ⟨21786579054463853286063631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29048772072618471048084841 21786579054463853286063631)
          ·
            refine ⟨32679868581695779929095447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21786579054463853286063631 32679868581695779929095447)
            ·
              refine ⟨49019802872543669893643171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32679868581695779929095447 49019802872543669893643171)
              ·
                refine ⟨73529704308815504840464757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49019802872543669893643171 73529704308815504840464757)
                ·
                  refine ⟨6893409778951453578793571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73529704308815504840464757 6893409778951453578793571)
                  ·
                    refine ⟨10340114668427180368190357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6893409778951453578793571 10340114668427180368190357)
                    ·
                      refine ⟨484692875082524079758923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10340114668427180368190357 484692875082524079758923)
                      ·
                        rfl

theorem cell23_943936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_943936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943936 prefixEnd_943936 := by exact prefixLift 943936
  have htrace : WordTrace (prefixWord ++ tailWord_943936) baseStart_943936 baseEnd_943936 := by
    simpa [prefixWord, tailWord_943936, baseEnd_943936] using wordTrace_append hprefix tailTrace_943936
  have hstable : (prefixWord ++ tailWord_943936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943936).length < 2 ^ (prefixWord ++ tailWord_943936).sum := by decide
  have hdescent : baseEnd_943936 < baseStart_943936 := by decide
  rcases family_descends (prefixWord ++ tailWord_943936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943946 : List Nat := [3, 1, 2, 1, 1, 1, 14]
def baseStart_943946 : Nat := 118140960795 + 943946 * 2 ^ 59
def prefixEnd_943946 : Nat := 4983230072969 + 3 ^ 40 * 943946 * 2
def baseEnd_943946 : Nat := 5983926048013198032517

theorem tailTrace_943946 : CollatzResearch.WordTrace tailWord_943946 prefixEnd_943946 5983926048013198032517 := by
  unfold tailWord_943946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607134759563082496768923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22952359358834886658050461 8607134759563082496768923)
  ·
    refine ⟨12910702139344623745153385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8607134759563082496768923 12910702139344623745153385)
    ·
      refine ⟨9683026604508467808865039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12910702139344623745153385 9683026604508467808865039)
      ·
        refine ⟨14524539906762701713297559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683026604508467808865039 14524539906762701713297559)
        ·
          refine ⟨21786809860144052569946339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524539906762701713297559 21786809860144052569946339)
          ·
            refine ⟨32680214790216078854919509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21786809860144052569946339 32680214790216078854919509)
            ·
              refine ⟨5983926048013198032517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 32680214790216078854919509 5983926048013198032517)
              ·
                rfl

theorem cell23_943946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 14].length) (baseStart_943946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943946 prefixEnd_943946 := by exact prefixLift 943946
  have htrace : WordTrace (prefixWord ++ tailWord_943946) baseStart_943946 baseEnd_943946 := by
    simpa [prefixWord, tailWord_943946, baseEnd_943946] using wordTrace_append hprefix tailTrace_943946
  have hstable : (prefixWord ++ tailWord_943946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943946).length < 2 ^ (prefixWord ++ tailWord_943946).sum := by decide
  have hdescent : baseEnd_943946 < baseStart_943946 := by decide
  rcases family_descends (prefixWord ++ tailWord_943946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943957 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_943957 : Nat := 118140960795 + 943957 * 2 ^ 59
def prefixEnd_943957 : Nat := 4983230072969 + 3 ^ 40 * 943957 * 2
def baseEnd_943957 : Nat := 484703658176268497596327

theorem tailTrace_943957 : CollatzResearch.WordTrace tailWord_943957 prefixEnd_943957 484703658176268497596327 := by
  unfold tailWord_943957
  simp only [CollatzResearch.WordTrace]
  refine ⟨34428940241212478865726125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22952626827474985910484083 34428940241212478865726125)
  ·
    refine ⟨12910852590454679574647297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34428940241212478865726125 12910852590454679574647297)
    ·
      refine ⟨9683139442841009680985473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12910852590454679574647297 9683139442841009680985473)
      ·
        refine ⟨7262354582130757260739105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9683139442841009680985473 7262354582130757260739105)
        ·
          refine ⟨5446765936598067945554329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7262354582130757260739105 5446765936598067945554329)
          ·
            refine ⟨4085074452448550959165747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5446765936598067945554329 4085074452448550959165747)
            ·
              refine ⟨6127611678672826438748621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085074452448550959165747 6127611678672826438748621)
              ·
                refine ⟨2297854379502309914530733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6127611678672826438748621 2297854379502309914530733)
                ·
                  refine ⟨861695392313366217949025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2297854379502309914530733 861695392313366217949025)
                  ·
                    refine ⟨646271544235024663461769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861695392313366217949025 646271544235024663461769)
                    ·
                      refine ⟨484703658176268497596327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646271544235024663461769 484703658176268497596327)
                      ·
                        rfl

theorem cell23_943957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_943957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943957 prefixEnd_943957 := by exact prefixLift 943957
  have htrace : WordTrace (prefixWord ++ tailWord_943957) baseStart_943957 baseEnd_943957 := by
    simpa [prefixWord, tailWord_943957, baseEnd_943957] using wordTrace_append hprefix tailTrace_943957
  have hstable : (prefixWord ++ tailWord_943957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943957).length < 2 ^ (prefixWord ++ tailWord_943957).sum := by decide
  have hdescent : baseEnd_943957 < baseStart_943957 := by decide
  rcases family_descends (prefixWord ++ tailWord_943957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943967 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 2, 4]
def baseStart_943967 : Nat := 118140960795 + 943967 * 2 ^ 59
def prefixEnd_943967 : Nat := 4983230072969 + 3 ^ 40 * 943967 * 2
def baseEnd_943967 : Nat := 161569597660937819490427

theorem tailTrace_943967 : CollatzResearch.WordTrace tailWord_943967 prefixEnd_943967 161569597660937819490427 := by
  unfold tailWord_943967
  simp only [CollatzResearch.WordTrace]
  refine ⟨34429304971176250573590155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22952869980784167049060103 34429304971176250573590155)
  ·
    refine ⟨51643957456764375860385233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34429304971176250573590155 51643957456764375860385233)
    ·
      refine ⟨38732968092573281895288925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51643957456764375860385233 38732968092573281895288925)
      ·
        refine ⟨14524863034714980710733347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38732968092573281895288925 14524863034714980710733347)
        ·
          refine ⟨21787294552072471066100021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524863034714980710733347 21787294552072471066100021)
          ·
            refine ⟨2042558864256794162446877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21787294552072471066100021 2042558864256794162446877)
            ·
              refine ⟨765959574096297810917579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2042558864256794162446877 765959574096297810917579)
              ·
                refine ⟨1148939361144446716376369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765959574096297810917579 1148939361144446716376369)
                ·
                  refine ⟨861704520858335037282277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1148939361144446716376369 861704520858335037282277)
                  ·
                    refine ⟨161569597660937819490427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861704520858335037282277 161569597660937819490427)
                    ·
                      rfl

theorem cell23_943967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_943967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943967 prefixEnd_943967 := by exact prefixLift 943967
  have htrace : WordTrace (prefixWord ++ tailWord_943967) baseStart_943967 baseEnd_943967 := by
    simpa [prefixWord, tailWord_943967, baseEnd_943967] using wordTrace_append hprefix tailTrace_943967
  have hstable : (prefixWord ++ tailWord_943967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943967).length < 2 ^ (prefixWord ++ tailWord_943967).sum := by decide
  have hdescent : baseEnd_943967 < baseStart_943967 := by decide
  rcases family_descends (prefixWord ++ tailWord_943967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943970 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_943970 : Nat := 118140960795 + 943970 * 2 ^ 59
def prefixEnd_943970 : Nat := 4983230072969 + 3 ^ 40 * 943970 * 2
def baseEnd_943970 : Nat := 484710333424776946733767

theorem tailTrace_943970 : CollatzResearch.WordTrace tailWord_943970 prefixEnd_943970 484710333424776946733767 := by
  unfold tailWord_943970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607353597541345521487341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22952942926776921390632909 8607353597541345521487341)
  ·
    refine ⟨3227757599078004570557753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8607353597541345521487341 3227757599078004570557753)
    ·
      refine ⟨2420818199308503427918315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3227757599078004570557753 2420818199308503427918315)
      ·
        refine ⟨3631227298962755141877473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420818199308503427918315 3631227298962755141877473)
        ·
          refine ⟨2723420474222066356408105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631227298962755141877473 2723420474222066356408105)
          ·
            refine ⟨2042565355666549767306079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723420474222066356408105 2042565355666549767306079)
            ·
              refine ⟨3063848033499824650959119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042565355666549767306079 3063848033499824650959119)
              ·
                refine ⟨4595772050249736976438679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063848033499824650959119 4595772050249736976438679)
                ·
                  refine ⟨6893658075374605464658019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595772050249736976438679 6893658075374605464658019)
                  ·
                    refine ⟨10340487113061908196987029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6893658075374605464658019 10340487113061908196987029)
                    ·
                      refine ⟨484710333424776946733767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10340487113061908196987029 484710333424776946733767)
                      ·
                        rfl

theorem cell23_943970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_943970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943970 prefixEnd_943970 := by exact prefixLift 943970
  have htrace : WordTrace (prefixWord ++ tailWord_943970) baseStart_943970 baseEnd_943970 := by
    simpa [prefixWord, tailWord_943970, baseEnd_943970] using wordTrace_append hprefix tailTrace_943970
  have hstable : (prefixWord ++ tailWord_943970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943970).length < 2 ^ (prefixWord ++ tailWord_943970).sum := by decide
  have hdescent : baseEnd_943970 < baseStart_943970 := by decide
  rcases family_descends (prefixWord ++ tailWord_943970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943980 : List Nat := [2, 2, 1, 1, 4, 4, 2, 7]
def baseStart_943980 : Nat := 118140960795 + 943980 * 2 ^ 59
def prefixEnd_943980 : Nat := 4983230072969 + 3 ^ 40 * 943980 * 2
def baseEnd_943980 : Nat := 17952424749308218800323

theorem tailTrace_943980 : CollatzResearch.WordTrace tailWord_943980 prefixEnd_943980 17952424749308218800323 := by
  unfold tailWord_943980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214889560064576896906697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22953186080086102529208929 17214889560064576896906697)
  ·
    refine ⟨12911167170048432672680023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17214889560064576896906697 12911167170048432672680023)
    ·
      refine ⟨19366750755072649009020035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12911167170048432672680023 19366750755072649009020035)
      ·
        refine ⟨29050126132608973513530053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19366750755072649009020035 29050126132608973513530053)
        ·
          refine ⟨5446898649864182533786885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29050126132608973513530053 5446898649864182533786885)
          ·
            refine ⟨1021293496849534225085041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5446898649864182533786885 1021293496849534225085041)
            ·
              refine ⟨765970122637150668813781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021293496849534225085041 765970122637150668813781)
              ·
                refine ⟨17952424749308218800323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 765970122637150668813781 17952424749308218800323)
                ·
                  rfl

theorem cell23_943980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 7].length) (baseStart_943980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_943980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_943980 prefixEnd_943980 := by exact prefixLift 943980
  have htrace : WordTrace (prefixWord ++ tailWord_943980) baseStart_943980 baseEnd_943980 := by
    simpa [prefixWord, tailWord_943980, baseEnd_943980] using wordTrace_append hprefix tailTrace_943980
  have hstable : (prefixWord ++ tailWord_943980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943980).length < 2 ^ (prefixWord ++ tailWord_943980).sum := by decide
  have hdescent : baseEnd_943980 < baseStart_943980 := by decide
  rcases family_descends (prefixWord ++ tailWord_943980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944008 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_944008 : Nat := 118140960795 + 944008 * 2 ^ 59
def prefixEnd_944008 : Nat := 4983230072969 + 3 ^ 40 * 944008 * 2
def baseEnd_944008 : Nat := 484729845689647798058593

theorem tailTrace_944008 : CollatzResearch.WordTrace tailWord_944008 prefixEnd_944008 484729845689647798058593 := by
  unfold tailWord_944008
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215400182013857287916339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22953866909351809717221785 17215400182013857287916339)
  ·
    refine ⟨25823100273020785931874509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17215400182013857287916339 25823100273020785931874509)
    ·
      refine ⟨9683662602382794724452941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25823100273020785931874509 9683662602382794724452941)
      ·
        refine ⟨3631373475893548021669853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9683662602382794724452941 3631373475893548021669853)
        ·
          refine ⟨1361765053460080508126195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3631373475893548021669853 1361765053460080508126195)
          ·
            refine ⟨2042647580190120762189293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361765053460080508126195 2042647580190120762189293)
            ·
              refine ⟨765992842571295285820985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2042647580190120762189293 765992842571295285820985)
              ·
                refine ⟨574494631928471464365739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765992842571295285820985 574494631928471464365739)
                ·
                  refine ⟨861741947892707196548609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574494631928471464365739 861741947892707196548609)
                  ·
                    refine ⟨646306460919530397411457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861741947892707196548609 646306460919530397411457)
                    ·
                      refine ⟨484729845689647798058593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646306460919530397411457 484729845689647798058593)
                      ·
                        rfl

theorem cell23_944008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_944008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944008 prefixEnd_944008 := by exact prefixLift 944008
  have htrace : WordTrace (prefixWord ++ tailWord_944008) baseStart_944008 baseEnd_944008 := by
    simpa [prefixWord, tailWord_944008, baseEnd_944008] using wordTrace_append hprefix tailTrace_944008
  have hstable : (prefixWord ++ tailWord_944008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944008).length < 2 ^ (prefixWord ++ tailWord_944008).sum := by decide
  have hdescent : baseEnd_944008 < baseStart_944008 := by decide
  rcases family_descends (prefixWord ++ tailWord_944008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944034 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_944034 : Nat := 118140960795 + 944034 * 2 ^ 59
def prefixEnd_944034 : Nat := 4983230072969 + 3 ^ 40 * 944034 * 2
def baseEnd_944034 : Nat := 484743196186664696333473

theorem tailTrace_944034 : CollatzResearch.WordTrace tailWord_944034 prefixEnd_944034 484743196186664696333473 := by
  unfold tailWord_944034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607937165483380254069789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22954499107955680677519437 8607937165483380254069789)
  ·
    refine ⟨3227976437056267595276171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8607937165483380254069789 3227976437056267595276171)
    ·
      refine ⟨4841964655584401392914257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227976437056267595276171 4841964655584401392914257)
      ·
        refine ⟨3631473491688301044685693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4841964655584401392914257 3631473491688301044685693)
        ·
          refine ⟨1361802559383112891757135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3631473491688301044685693 1361802559383112891757135)
          ·
            refine ⟨2042703839074669337635703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361802559383112891757135 2042703839074669337635703)
            ·
              refine ⟨3064055758612004006453555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042703839074669337635703 3064055758612004006453555)
              ·
                refine ⟨4596083637918006009680333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064055758612004006453555 4596083637918006009680333)
                ·
                  refine ⟨1723531364219252253630125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4596083637918006009680333 1723531364219252253630125)
                  ·
                    refine ⟨646324261582219595111297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723531364219252253630125 646324261582219595111297)
                    ·
                      refine ⟨484743196186664696333473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646324261582219595111297 484743196186664696333473)
                      ·
                        rfl

theorem cell23_944034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_944034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944034 prefixEnd_944034 := by exact prefixLift 944034
  have htrace : WordTrace (prefixWord ++ tailWord_944034) baseStart_944034 baseEnd_944034 := by
    simpa [prefixWord, tailWord_944034, baseEnd_944034] using wordTrace_append hprefix tailTrace_944034
  have hstable : (prefixWord ++ tailWord_944034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944034).length < 2 ^ (prefixWord ++ tailWord_944034).sum := by decide
  have hdescent : baseEnd_944034 < baseStart_944034 := by decide
  rcases family_descends (prefixWord ++ tailWord_944034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944064 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2]
def baseStart_944064 : Nat := 118140960795 + 944064 * 2 ^ 59
def prefixEnd_944064 : Nat := 4983230072969 + 3 ^ 40 * 944064 * 2
def baseEnd_944064 : Nat := 484758600606299578958335

theorem tailTrace_944064 : CollatzResearch.WordTrace tailWord_944064 prefixEnd_944064 484758600606299578958335 := by
  unfold tailWord_944064
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216421425912418069935623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22955228567883224093247497 17216421425912418069935623)
  ·
    refine ⟨25824632138868627104903435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17216421425912418069935623 25824632138868627104903435)
    ·
      refine ⟨38736948208302940657355153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25824632138868627104903435 38736948208302940657355153)
      ·
        refine ⟨29052711156227205493016365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38736948208302940657355153 29052711156227205493016365)
        ·
          refine ⟨10894766683585202059881137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29052711156227205493016365 10894766683585202059881137)
          ·
            refine ⟨8171075012688901544910853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10894766683585202059881137 8171075012688901544910853)
            ·
              refine ⟨1532076564879169039670785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8171075012688901544910853 1532076564879169039670785)
              ·
                refine ⟨1149057423659376779753089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532076564879169039670785 1149057423659376779753089)
                ·
                  refine ⟨861793067744532584814817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149057423659376779753089 861793067744532584814817)
                  ·
                    refine ⟨646344800808399438611113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861793067744532584814817 646344800808399438611113)
                    ·
                      refine ⟨484758600606299578958335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646344800808399438611113 484758600606299578958335)
                      ·
                        rfl

theorem cell23_944064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_944064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944064 prefixEnd_944064 := by exact prefixLift 944064
  have htrace : WordTrace (prefixWord ++ tailWord_944064) baseStart_944064 baseEnd_944064 := by
    simpa [prefixWord, tailWord_944064, baseEnd_944064] using wordTrace_append hprefix tailTrace_944064
  have hstable : (prefixWord ++ tailWord_944064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944064).length < 2 ^ (prefixWord ++ tailWord_944064).sum := by decide
  have hdescent : baseEnd_944064 < baseStart_944064 := by decide
  rcases family_descends (prefixWord ++ tailWord_944064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944120 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_944120 : Nat := 118140960795 + 944120 * 2 ^ 59
def prefixEnd_944120 : Nat := 4983230072969 + 3 ^ 40 * 944120 * 2
def baseEnd_944120 : Nat := 484787355522951359858077

theorem tailTrace_944120 : CollatzResearch.WordTrace tailWord_944120 prefixEnd_944120 484787355522951359858077 := by
  unfold tailWord_944120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217442669810978851954907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22956590226414638469273209 17217442669810978851954907)
  ·
    refine ⟨25826164004716468277932361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17217442669810978851954907 25826164004716468277932361)
    ·
      refine ⟨19369623003537351208449271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25826164004716468277932361 19369623003537351208449271)
      ·
        refine ⟨29054434505306026812673907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19369623003537351208449271 29054434505306026812673907)
        ·
          refine ⟨43581651757959040219010861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29054434505306026812673907 43581651757959040219010861)
          ·
            refine ⟨16343119409234640082129073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43581651757959040219010861 16343119409234640082129073)
            ·
              refine ⟨12257339556925980061596805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16343119409234640082129073 12257339556925980061596805)
              ·
                refine ⟨2298251166923621261549401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12257339556925980061596805 2298251166923621261549401)
                ·
                  refine ⟨1723688375192715946162051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298251166923621261549401 1723688375192715946162051)
                  ·
                    refine ⟨2585532562789073919243077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723688375192715946162051 2585532562789073919243077)
                    ·
                      refine ⟨484787355522951359858077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2585532562789073919243077 484787355522951359858077)
                      ·
                        rfl

theorem cell23_944120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_944120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944120 prefixEnd_944120 := by exact prefixLift 944120
  have htrace : WordTrace (prefixWord ++ tailWord_944120) baseStart_944120 baseEnd_944120 := by
    simpa [prefixWord, tailWord_944120, baseEnd_944120] using wordTrace_append hprefix tailTrace_944120
  have hstable : (prefixWord ++ tailWord_944120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944120).length < 2 ^ (prefixWord ++ tailWord_944120).sum := by decide
  have hdescent : baseEnd_944120 < baseStart_944120 := by decide
  rcases family_descends (prefixWord ++ tailWord_944120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944123 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_944123 : Nat := 118140960795 + 944123 * 2 ^ 59
def prefixEnd_944123 : Nat := 4983230072969 + 3 ^ 40 * 944123 * 2
def baseEnd_944123 : Nat := 484788895964914848120563

theorem tailTrace_944123 : CollatzResearch.WordTrace tailWord_944123 prefixEnd_944123 484788895964914848120563 := by
  unfold tailWord_944123
  simp only [CollatzResearch.WordTrace]
  refine ⟨34434994758611089216269023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22956663172407392810846015 34434994758611089216269023)
  ·
    refine ⟨51652492137916633824403535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34434994758611089216269023 51652492137916633824403535)
    ·
      refine ⟨77478738206874950736605303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51652492137916633824403535 77478738206874950736605303)
      ·
        refine ⟨116218107310312426104907955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77478738206874950736605303 116218107310312426104907955)
        ·
          refine ⟨174327160965468639157361933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116218107310312426104907955 174327160965468639157361933)
          ·
            refine ⟨65372685362050739684010725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174327160965468639157361933 65372685362050739684010725)
            ·
              refine ⟨12257378505384513690752011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65372685362050739684010725 12257378505384513690752011)
              ·
                refine ⟨18386067758076770536128017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257378505384513690752011 18386067758076770536128017)
                ·
                  refine ⟨13789550818557577902096013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18386067758076770536128017 13789550818557577902096013)
                  ·
                    refine ⟨5171081556959091713286005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13789550818557577902096013 5171081556959091713286005)
                    ·
                      refine ⟨484788895964914848120563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5171081556959091713286005 484788895964914848120563)
                      ·
                        rfl

theorem cell23_944123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_944123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944123 prefixEnd_944123 := by exact prefixLift 944123
  have htrace : WordTrace (prefixWord ++ tailWord_944123) baseStart_944123 baseEnd_944123 := by
    simpa [prefixWord, tailWord_944123, baseEnd_944123] using wordTrace_append hprefix tailTrace_944123
  have hstable : (prefixWord ++ tailWord_944123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944123).length < 2 ^ (prefixWord ++ tailWord_944123).sum := by decide
  have hdescent : baseEnd_944123 < baseStart_944123 := by decide
  rcases family_descends (prefixWord ++ tailWord_944123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944140 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_944140 : Nat := 118140960795 + 944140 * 2 ^ 59
def prefixEnd_944140 : Nat := 4983230072969 + 3 ^ 40 * 944140 * 2
def baseEnd_944140 : Nat := 484797625136041281607985

theorem tailTrace_944140 : CollatzResearch.WordTrace tailWord_944140 prefixEnd_944140 484797625136041281607985 := by
  unfold tailWord_944140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217807399774750559818937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22957076533033000746425249 17217807399774750559818937)
  ·
    refine ⟨12913355549831062919864203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17217807399774750559818937 12913355549831062919864203)
    ·
      refine ⟨19370033324746594379796305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12913355549831062919864203 19370033324746594379796305)
      ·
        refine ⟨14527524993559945784847229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19370033324746594379796305 14527524993559945784847229)
        ·
          refine ⟨5447821872584979669317711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14527524993559945784847229 5447821872584979669317711)
          ·
            refine ⟨8171732808877469503976567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447821872584979669317711 8171732808877469503976567)
            ·
              refine ⟨12257599213316204255964851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171732808877469503976567 12257599213316204255964851)
              ·
                refine ⟨18386398819974306383947277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257599213316204255964851 18386398819974306383947277)
                ·
                  refine ⟨6894899557490364893980229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18386398819974306383947277 6894899557490364893980229)
                  ·
                    refine ⟨1292793667029443417621293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894899557490364893980229 1292793667029443417621293)
                    ·
                      refine ⟨484797625136041281607985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292793667029443417621293 484797625136041281607985)
                      ·
                        rfl

theorem cell23_944140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_944140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944140 prefixEnd_944140 := by exact prefixLift 944140
  have htrace : WordTrace (prefixWord ++ tailWord_944140) baseStart_944140 baseEnd_944140 := by
    simpa [prefixWord, tailWord_944140, baseEnd_944140] using wordTrace_append hprefix tailTrace_944140
  have hstable : (prefixWord ++ tailWord_944140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944140).length < 2 ^ (prefixWord ++ tailWord_944140).sum := by decide
  have hdescent : baseEnd_944140 < baseStart_944140 := by decide
  rcases family_descends (prefixWord ++ tailWord_944140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944157 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_944157 : Nat := 118140960795 + 944157 * 2 ^ 59
def prefixEnd_944157 : Nat := 4983230072969 + 3 ^ 40 * 944157 * 2
def baseEnd_944157 : Nat := 484806354307167715095407

theorem tailTrace_944157 : CollatzResearch.WordTrace tailWord_944157 prefixEnd_944157 484806354307167715095407 := by
  unfold tailWord_944157
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436234840487913023006725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22957489893658608682004483 34436234840487913023006725)
  ·
    refine ⟨6456794032591483691813761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34436234840487913023006725 6456794032591483691813761)
    ·
      refine ⟨4842595524443612768860321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6456794032591483691813761 4842595524443612768860321)
      ·
        refine ⟨3631946643332709576645241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4842595524443612768860321 3631946643332709576645241)
        ·
          refine ⟨2723959982499532182483931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631946643332709576645241 2723959982499532182483931)
          ·
            refine ⟨4085939973749298273725897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723959982499532182483931 4085939973749298273725897)
            ·
              refine ⟨3064454980311973705294423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085939973749298273725897 3064454980311973705294423)
              ·
                refine ⟨4596682470467960557941635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064454980311973705294423 4596682470467960557941635)
                ·
                  refine ⟨6895023705701940836912453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596682470467960557941635 6895023705701940836912453)
                  ·
                    refine ⟨1292816944819113906921085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6895023705701940836912453 1292816944819113906921085)
                    ·
                      refine ⟨484806354307167715095407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292816944819113906921085 484806354307167715095407)
                      ·
                        rfl

theorem cell23_944157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_944157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944157 prefixEnd_944157 := by exact prefixLift 944157
  have htrace : WordTrace (prefixWord ++ tailWord_944157) baseStart_944157 baseEnd_944157 := by
    simpa [prefixWord, tailWord_944157, baseEnd_944157] using wordTrace_append hprefix tailTrace_944157
  have hstable : (prefixWord ++ tailWord_944157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944157).length < 2 ^ (prefixWord ++ tailWord_944157).sum := by decide
  have hdescent : baseEnd_944157 < baseStart_944157 := by decide
  rcases family_descends (prefixWord ++ tailWord_944157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944174 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_944174 : Nat := 118140960795 + 944174 * 2 ^ 59
def prefixEnd_944174 : Nat := 4983230072969 + 3 ^ 40 * 944174 * 2
def baseEnd_944174 : Nat := 484815083478294148582829

theorem tailTrace_944174 : CollatzResearch.WordTrace tailWord_944174 prefixEnd_944174 484815083478294148582829 := by
  unfold tailWord_944174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304606860178290615796947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22957903254284216617583717 4304606860178290615796947)
  ·
    refine ⟨6456910290267435923695421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4304606860178290615796947 6456910290267435923695421)
    ·
      refine ⟨2421341358850288471385783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6456910290267435923695421 2421341358850288471385783)
      ·
        refine ⟨3632012038275432707078675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421341358850288471385783 3632012038275432707078675)
        ·
          refine ⟨5448018057413149060618013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632012038275432707078675 5448018057413149060618013)
          ·
            refine ⟨2043006771529930897731755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5448018057413149060618013 2043006771529930897731755)
            ·
              refine ⟨3064510157294896346597633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043006771529930897731755 3064510157294896346597633)
              ·
                refine ⟨2298382617971172259948225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064510157294896346597633 2298382617971172259948225)
                ·
                  refine ⟨1723786963478379194961169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298382617971172259948225 1723786963478379194961169)
                  ·
                    refine ⟨1292840222608784396220877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1723786963478379194961169 1292840222608784396220877)
                    ·
                      refine ⟨484815083478294148582829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292840222608784396220877 484815083478294148582829)
                      ·
                        rfl

theorem cell23_944174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_944174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944174 prefixEnd_944174 := by exact prefixLift 944174
  have htrace : WordTrace (prefixWord ++ tailWord_944174) baseStart_944174 baseEnd_944174 := by
    simpa [prefixWord, tailWord_944174, baseEnd_944174] using wordTrace_append hprefix tailTrace_944174
  have hstable : (prefixWord ++ tailWord_944174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944174).length < 2 ^ (prefixWord ++ tailWord_944174).sum := by decide
  have hdescent : baseEnd_944174 < baseStart_944174 := by decide
  rcases family_descends (prefixWord ++ tailWord_944174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944197 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_944197 : Nat := 118140960795 + 944197 * 2 ^ 59
def prefixEnd_944197 : Nat := 4983230072969 + 3 ^ 40 * 944197 * 2
def baseEnd_944197 : Nat := 484826893533347558595223

theorem tailTrace_944197 : CollatzResearch.WordTrace tailWord_944197 prefixEnd_944197 484826893533347558595223 := by
  unfold tailWord_944197
  simp only [CollatzResearch.WordTrace]
  refine ⟨34437693760342999854462845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22958462506895333236308563 34437693760342999854462845)
  ·
    refine ⟨12914135160128624945423567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34437693760342999854462845 12914135160128624945423567)
    ·
      refine ⟨19371202740192937418135351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12914135160128624945423567 19371202740192937418135351)
      ·
        refine ⟨29056804110289406127203027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19371202740192937418135351 29056804110289406127203027)
        ·
          refine ⟨43585206165434109190804541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29056804110289406127203027 43585206165434109190804541)
          ·
            refine ⟨16344452312037790946551703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43585206165434109190804541 16344452312037790946551703)
            ·
              refine ⟨24516678468056686419827555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344452312037790946551703 24516678468056686419827555)
              ·
                refine ⟨36775017702085029629741333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24516678468056686419827555 36775017702085029629741333)
                ·
                  refine ⟨1723828954785235763894125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36775017702085029629741333 1723828954785235763894125)
                  ·
                    refine ⟨646435858044463411460297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723828954785235763894125 646435858044463411460297)
                    ·
                      refine ⟨484826893533347558595223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646435858044463411460297 484826893533347558595223)
                      ·
                        rfl

theorem cell23_944197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_944197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944197 prefixEnd_944197 := by exact prefixLift 944197
  have htrace : WordTrace (prefixWord ++ tailWord_944197) baseStart_944197 baseEnd_944197 := by
    simpa [prefixWord, tailWord_944197, baseEnd_944197] using wordTrace_append hprefix tailTrace_944197
  have hstable : (prefixWord ++ tailWord_944197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944197).length < 2 ^ (prefixWord ++ tailWord_944197).sum := by decide
  have hdescent : baseEnd_944197 < baseStart_944197 := by decide
  rcases family_descends (prefixWord ++ tailWord_944197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944224 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 1, 5]
def baseStart_944224 : Nat := 118140960795 + 944224 * 2 ^ 59
def prefixEnd_944224 : Nat := 4983230072969 + 3 ^ 40 * 944224 * 2
def baseEnd_944224 : Nat := 161613585837006317652533

theorem tailTrace_944224 : CollatzResearch.WordTrace tailWord_944224 prefixEnd_944224 161613585837006317652533 := by
  unfold tailWord_944224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219339265622591732847863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22959119020830122310463817 17219339265622591732847863)
  ·
    refine ⟨25829008898433887599271795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17219339265622591732847863 25829008898433887599271795)
    ·
      refine ⟨38743513347650831398907693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25829008898433887599271795 38743513347650831398907693)
      ·
        refine ⟨14528817505369061774590385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38743513347650831398907693 14528817505369061774590385)
        ·
          refine ⟨10896613129026796330942789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14528817505369061774590385 10896613129026796330942789)
          ·
            refine ⟨2043114961692524312051773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10896613129026796330942789 2043114961692524312051773)
            ·
              refine ⟨766168110634696617019415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2043114961692524312051773 766168110634696617019415)
              ·
                refine ⟨1149252165952044925529123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766168110634696617019415 1149252165952044925529123)
                ·
                  refine ⟨1723878248928067388293685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149252165952044925529123 1723878248928067388293685)
                  ·
                    refine ⟨161613585837006317652533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1723878248928067388293685 161613585837006317652533)
                    ·
                      rfl

theorem cell23_944224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_944224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944224 prefixEnd_944224 := by exact prefixLift 944224
  have htrace : WordTrace (prefixWord ++ tailWord_944224) baseStart_944224 baseEnd_944224 := by
    simpa [prefixWord, tailWord_944224, baseEnd_944224] using wordTrace_append hprefix tailTrace_944224
  have hstable : (prefixWord ++ tailWord_944224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944224).length < 2 ^ (prefixWord ++ tailWord_944224).sum := by decide
  have hdescent : baseEnd_944224 < baseStart_944224 := by decide
  rcases family_descends (prefixWord ++ tailWord_944224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944227 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 4]
def baseStart_944227 : Nat := 118140960795 + 944227 * 2 ^ 59
def prefixEnd_944227 : Nat := 4983230072969 + 3 ^ 40 * 944227 * 2
def baseEnd_944227 : Nat := 484842297952982441220085

theorem tailTrace_944227 : CollatzResearch.WordTrace tailWord_944227 prefixEnd_944227 484842297952982441220085 := by
  unfold tailWord_944227
  simp only [CollatzResearch.WordTrace]
  refine ⟨34438787950234314978054935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22959191966822876652036623 34438787950234314978054935)
  ·
    refine ⟨51658181925351472467082403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34438787950234314978054935 51658181925351472467082403)
    ·
      refine ⟨77487272888027208700623605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51658181925351472467082403 77487272888027208700623605)
      ·
        refine ⟨7264431833252550815683463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77487272888027208700623605 7264431833252550815683463)
        ·
          refine ⟨10896647749878826223525195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264431833252550815683463 10896647749878826223525195)
          ·
            refine ⟨16344971624818239335287793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896647749878826223525195 16344971624818239335287793)
            ·
              refine ⟨12258728718613679501465845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16344971624818239335287793 12258728718613679501465845)
              ·
                refine ⟨1149255817370032453262423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12258728718613679501465845 1149255817370032453262423)
                ·
                  refine ⟨1723883726055048679893635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149255817370032453262423 1723883726055048679893635)
                  ·
                    refine ⟨2585825589082573019840453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723883726055048679893635 2585825589082573019840453)
                    ·
                      refine ⟨484842297952982441220085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2585825589082573019840453 484842297952982441220085)
                      ·
                        rfl

theorem cell23_944227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_944227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944227 prefixEnd_944227 := by exact prefixLift 944227
  have htrace : WordTrace (prefixWord ++ tailWord_944227) baseStart_944227 baseEnd_944227 := by
    simpa [prefixWord, tailWord_944227, baseEnd_944227] using wordTrace_append hprefix tailTrace_944227
  have hstable : (prefixWord ++ tailWord_944227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944227).length < 2 ^ (prefixWord ++ tailWord_944227).sum := by decide
  have hdescent : baseEnd_944227 < baseStart_944227 := by decide
  rcases family_descends (prefixWord ++ tailWord_944227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944247 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_944247 : Nat := 118140960795 + 944247 * 2 ^ 59
def prefixEnd_944247 : Nat := 4983230072969 + 3 ^ 40 * 944247 * 2
def baseEnd_944247 : Nat := 484852567566072362969993

theorem tailTrace_944247 : CollatzResearch.WordTrace tailWord_944247 prefixEnd_944247 484852567566072362969993 := by
  unfold tailWord_944247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34439517410161858393782995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22959678273441238929188663 34439517410161858393782995)
  ·
    refine ⟨51659276115242787590674493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34439517410161858393782995 51659276115242787590674493)
    ·
      refine ⟨19372228543216045346502935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51659276115242787590674493 19372228543216045346502935)
      ·
        refine ⟨29058342814824068019754403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372228543216045346502935 29058342814824068019754403)
        ·
          refine ⟨43587514222236102029631605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29058342814824068019754403 43587514222236102029631605)
          ·
            refine ⟨4086329458334634565277963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43587514222236102029631605 4086329458334634565277963)
            ·
              refine ⟨6129494187501951847916945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086329458334634565277963 6129494187501951847916945)
              ·
                refine ⟨4597120640626463885937709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129494187501951847916945 4597120640626463885937709)
                ·
                  refine ⟨1723920240234923957226641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4597120640626463885937709 1723920240234923957226641)
                  ·
                    refine ⟨1292940180176192967919981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1723920240234923957226641 1292940180176192967919981)
                    ·
                      refine ⟨484852567566072362969993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292940180176192967919981 484852567566072362969993)
                      ·
                        rfl

theorem cell23_944247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_944247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944247 prefixEnd_944247 := by exact prefixLift 944247
  have htrace : WordTrace (prefixWord ++ tailWord_944247) baseStart_944247 baseEnd_944247 := by
    simpa [prefixWord, tailWord_944247, baseEnd_944247] using wordTrace_append hprefix tailTrace_944247
  have hstable : (prefixWord ++ tailWord_944247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944247).length < 2 ^ (prefixWord ++ tailWord_944247).sum := by decide
  have hdescent : baseEnd_944247 < baseStart_944247 := by decide
  rcases family_descends (prefixWord ++ tailWord_944247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944261 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_944261 : Nat := 118140960795 + 944261 * 2 ^ 59
def prefixEnd_944261 : Nat := 4983230072969 + 3 ^ 40 * 944261 * 2
def baseEnd_944261 : Nat := 484859756295235308194929

theorem tailTrace_944261 : CollatzResearch.WordTrace tailWord_944261 prefixEnd_944261 484859756295235308194929 := by
  unfold tailWord_944261
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440028032111138784792637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22960018688074092523195091 34440028032111138784792637)
  ·
    refine ⟨12915010512041677044297239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34440028032111138784792637 12915010512041677044297239)
    ·
      refine ⟨19372515768062515566445859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915010512041677044297239 19372515768062515566445859)
      ·
        refine ⟨29058773652093773349668789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372515768062515566445859 29058773652093773349668789)
        ·
          refine ⟨2724260029883791251531449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29058773652093773349668789 2724260029883791251531449)
          ·
            refine ⟨2043195022412843438648587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2724260029883791251531449 2043195022412843438648587)
            ·
              refine ⟨3064792533619265157972881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043195022412843438648587 3064792533619265157972881)
              ·
                refine ⟨2298594400214448868479661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064792533619265157972881 2298594400214448868479661)
                ·
                  refine ⟨861972900080418325679873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2298594400214448868479661 861972900080418325679873)
                  ·
                    refine ⟨646479675060313744259905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861972900080418325679873 646479675060313744259905)
                    ·
                      refine ⟨484859756295235308194929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646479675060313744259905 484859756295235308194929)
                      ·
                        rfl

theorem cell23_944261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_944261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944261 prefixEnd_944261 := by exact prefixLift 944261
  have htrace : WordTrace (prefixWord ++ tailWord_944261) baseStart_944261 baseEnd_944261 := by
    simpa [prefixWord, tailWord_944261, baseEnd_944261] using wordTrace_append hprefix tailTrace_944261
  have hstable : (prefixWord ++ tailWord_944261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944261).length < 2 ^ (prefixWord ++ tailWord_944261).sum := by decide
  have hdescent : baseEnd_944261 < baseStart_944261 := by decide
  rcases family_descends (prefixWord ++ tailWord_944261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944264 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_944264 : Nat := 118140960795 + 944264 * 2 ^ 59
def prefixEnd_944264 : Nat := 4983230072969 + 3 ^ 40 * 944264 * 2
def baseEnd_944264 : Nat := 484861296737198796457415

theorem tailTrace_944264 : CollatzResearch.WordTrace tailWord_944264 prefixEnd_944264 484861296737198796457415 := by
  unfold tailWord_944264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220068725550135148575923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22960091634066846864767897 17220068725550135148575923)
  ·
    refine ⟨25830103088325202722863885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17220068725550135148575923 25830103088325202722863885)
    ·
      refine ⟨9686288658121951021073957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25830103088325202722863885 9686288658121951021073957)
      ·
        refine ⟨1816179123397865816451367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9686288658121951021073957 1816179123397865816451367)
        ·
          refine ⟨2724268685096798724677051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816179123397865816451367 2724268685096798724677051)
          ·
            refine ⟨4086403027645198087015577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724268685096798724677051 4086403027645198087015577)
            ·
              refine ⟨3064802270733898565261683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086403027645198087015577 3064802270733898565261683)
              ·
                refine ⟨4597203406100847847892525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064802270733898565261683 4597203406100847847892525)
                ·
                  refine ⟨1723951277287817942959697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4597203406100847847892525 1723951277287817942959697)
                  ·
                    refine ⟨1292963457965863457219773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1723951277287817942959697 1292963457965863457219773)
                    ·
                      refine ⟨484861296737198796457415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292963457965863457219773 484861296737198796457415)
                      ·
                        rfl

theorem cell23_944264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_944264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944264 prefixEnd_944264 := by exact prefixLift 944264
  have htrace : WordTrace (prefixWord ++ tailWord_944264) baseStart_944264 baseEnd_944264 := by
    simpa [prefixWord, tailWord_944264, baseEnd_944264] using wordTrace_append hprefix tailTrace_944264
  have hstable : (prefixWord ++ tailWord_944264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944264).length < 2 ^ (prefixWord ++ tailWord_944264).sum := by decide
  have hdescent : baseEnd_944264 < baseStart_944264 := by decide
  rcases family_descends (prefixWord ++ tailWord_944264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944277 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_944277 : Nat := 118140960795 + 944277 * 2 ^ 59
def prefixEnd_944277 : Nat := 4983230072969 + 3 ^ 40 * 944277 * 2
def baseEnd_944277 : Nat := 484867971985707245594855

theorem tailTrace_944277 : CollatzResearch.WordTrace tailWord_944277 prefixEnd_944277 484867971985707245594855 := by
  unfold tailWord_944277
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440611600053173517375085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22960407733368782344916723 34440611600053173517375085)
  ·
    refine ⟨12915229350019940069015657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34440611600053173517375085 12915229350019940069015657)
    ·
      refine ⟨9686422012514955051761743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12915229350019940069015657 9686422012514955051761743)
      ·
        refine ⟨14529633018772432577642615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9686422012514955051761743 14529633018772432577642615)
        ·
          refine ⟨21794449528158648866463923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14529633018772432577642615 21794449528158648866463923)
          ·
            refine ⟨32691674292237973299695885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21794449528158648866463923 32691674292237973299695885)
            ·
              refine ⟨12259377859589239987385957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32691674292237973299695885 12259377859589239987385957)
              ·
                refine ⟨2298633348672982497634867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12259377859589239987385957 2298633348672982497634867)
                ·
                  refine ⟨3447950023009473746452301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298633348672982497634867 3447950023009473746452301)
                  ·
                    refine ⟨1292981258628552654919613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447950023009473746452301 1292981258628552654919613)
                    ·
                      refine ⟨484867971985707245594855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1292981258628552654919613 484867971985707245594855)
                      ·
                        rfl

theorem cell23_944277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_944277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944277 prefixEnd_944277 := by exact prefixLift 944277
  have htrace : WordTrace (prefixWord ++ tailWord_944277) baseStart_944277 baseEnd_944277 := by
    simpa [prefixWord, tailWord_944277, baseEnd_944277] using wordTrace_append hprefix tailTrace_944277
  have hstable : (prefixWord ++ tailWord_944277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944277).length < 2 ^ (prefixWord ++ tailWord_944277).sum := by decide
  have hdescent : baseEnd_944277 < baseStart_944277 := by decide
  rcases family_descends (prefixWord ++ tailWord_944277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944308 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_944308 : Nat := 118140960795 + 944308 * 2 ^ 59
def prefixEnd_944308 : Nat := 4983230072969 + 3 ^ 40 * 944308 * 2
def baseEnd_944308 : Nat := 484883889885996624307213

theorem tailTrace_944308 : CollatzResearch.WordTrace tailWord_944308 prefixEnd_944308 484883889885996624307213 := by
  unfold tailWord_944308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220871131470432905876789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22961161508627243874502385 17220871131470432905876789)
  ·
    refine ⟨1614456668575353084925949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17220871131470432905876789 1614456668575353084925949)
    ·
      refine ⟨605421250715757406847231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1614456668575353084925949 605421250715757406847231)
      ·
        refine ⟨908131876073636110270847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605421250715757406847231 908131876073636110270847)
        ·
          refine ⟨1362197814110454165406271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908131876073636110270847 1362197814110454165406271)
          ·
            refine ⟨2043296721165681248109407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362197814110454165406271 2043296721165681248109407)
            ·
              refine ⟨3064945081748521872164111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043296721165681248109407 3064945081748521872164111)
              ·
                refine ⟨4597417622622782808246167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064945081748521872164111 4597417622622782808246167)
                ·
                  refine ⟨6896126433934174212369251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597417622622782808246167 6896126433934174212369251)
                  ·
                    refine ⟨10344189650901261318553877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896126433934174212369251 10344189650901261318553877)
                    ·
                      refine ⟨484883889885996624307213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10344189650901261318553877 484883889885996624307213)
                      ·
                        rfl

theorem cell23_944308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_944308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944308 prefixEnd_944308 := by exact prefixLift 944308
  have htrace : WordTrace (prefixWord ++ tailWord_944308) baseStart_944308 baseEnd_944308 := by
    simpa [prefixWord, tailWord_944308, baseEnd_944308] using wordTrace_append hprefix tailTrace_944308
  have hstable : (prefixWord ++ tailWord_944308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944308).length < 2 ^ (prefixWord ++ tailWord_944308).sum := by decide
  have hdescent : baseEnd_944308 < baseStart_944308 := by decide
  rcases family_descends (prefixWord ++ tailWord_944308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944351 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 2, 2, 2]
def baseStart_944351 : Nat := 118140960795 + 944351 * 2 ^ 59
def prefixEnd_944351 : Nat := 4983230072969 + 3 ^ 40 * 944351 * 2
def baseEnd_944351 : Nat := 484905969554139956069515

theorem tailTrace_944351 : CollatzResearch.WordTrace tailWord_944351 prefixEnd_944351 484905969554139956069515 := by
  unfold tailWord_944351
  simp only [CollatzResearch.WordTrace]
  refine ⟨34443310601785084155568907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22962207067856722770379271 34443310601785084155568907)
  ·
    refine ⟨51664965902677626233353361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34443310601785084155568907 51664965902677626233353361)
    ·
      refine ⟨38748724427008219675015021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51664965902677626233353361 38748724427008219675015021)
      ·
        refine ⟨14530771660128082378130633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38748724427008219675015021 14530771660128082378130633)
        ·
          refine ⟨10898078745096061783597975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14530771660128082378130633 10898078745096061783597975)
          ·
            refine ⟨16347118117644092675396963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10898078745096061783597975 16347118117644092675396963)
            ·
              refine ⟨24520677176466139013095445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16347118117644092675396963 24520677176466139013095445)
              ·
                refine ⟨1149406742646850266238849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24520677176466139013095445 1149406742646850266238849)
                ·
                  refine ⟨862055056985137699679137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149406742646850266238849 862055056985137699679137)
                  ·
                    refine ⟨646541292738853274759353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 862055056985137699679137 646541292738853274759353)
                    ·
                      refine ⟨484905969554139956069515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646541292738853274759353 484905969554139956069515)
                      ·
                        rfl

theorem cell23_944351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_944351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944351 prefixEnd_944351 := by exact prefixLift 944351
  have htrace : WordTrace (prefixWord ++ tailWord_944351) baseStart_944351 baseEnd_944351 := by
    simpa [prefixWord, tailWord_944351, baseEnd_944351] using wordTrace_append hprefix tailTrace_944351
  have hstable : (prefixWord ++ tailWord_944351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944351).length < 2 ^ (prefixWord ++ tailWord_944351).sum := by decide
  have hdescent : baseEnd_944351 < baseStart_944351 := by decide
  rcases family_descends (prefixWord ++ tailWord_944351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944441 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_944441 : Nat := 118140960795 + 944441 * 2 ^ 59
def prefixEnd_944441 : Nat := 4983230072969 + 3 ^ 40 * 944441 * 2
def baseEnd_944441 : Nat := 484952182813044603944101

theorem tailTrace_944441 : CollatzResearch.WordTrace tailWord_944441 prefixEnd_944441 484952182813044603944101 := by
  unfold tailWord_944441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34446593171459029526345177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22964395447639353017563451 34446593171459029526345177)
  ·
    refine ⟨25834944878594272144758883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34446593171459029526345177 25834944878594272144758883)
    ·
      refine ⟨38752417317891408217138325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25834944878594272144758883 38752417317891408217138325)
      ·
        refine ⟨1816519561776159760178359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38752417317891408217138325 1816519561776159760178359)
        ·
          refine ⟨2724779342664239640267539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816519561776159760178359 2724779342664239640267539)
          ·
            refine ⟨4087169013996359460401309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724779342664239640267539 4087169013996359460401309)
            ·
              refine ⟨1532688380248634797650491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4087169013996359460401309 1532688380248634797650491)
              ·
                refine ⟨2299032570372952196475737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532688380248634797650491 2299032570372952196475737)
                ·
                  refine ⟨1724274427779714147356803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299032570372952196475737 1724274427779714147356803)
                  ·
                    refine ⟨2586411641669571221035205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724274427779714147356803 2586411641669571221035205)
                    ·
                      refine ⟨484952182813044603944101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2586411641669571221035205 484952182813044603944101)
                      ·
                        rfl

theorem cell23_944441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_944441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944441 prefixEnd_944441 := by exact prefixLift 944441
  have htrace : WordTrace (prefixWord ++ tailWord_944441) baseStart_944441 baseEnd_944441 := by
    simpa [prefixWord, tailWord_944441, baseEnd_944441] using wordTrace_append hprefix tailTrace_944441
  have hstable : (prefixWord ++ tailWord_944441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944441).length < 2 ^ (prefixWord ++ tailWord_944441).sum := by decide
  have hdescent : baseEnd_944441 < baseStart_944441 := by decide
  rcases family_descends (prefixWord ++ tailWord_944441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944444 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_944444 : Nat := 118140960795 + 944444 * 2 ^ 59
def prefixEnd_944444 : Nat := 4983230072969 + 3 ^ 40 * 944444 * 2
def baseEnd_944444 : Nat := 484953723255008092206587

theorem tailTrace_944444 : CollatzResearch.WordTrace tailWord_944444 prefixEnd_944444 484953723255008092206587 := by
  unfold tailWord_944444
  simp only [CollatzResearch.WordTrace]
  refine ⟨17223351295224080519352193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22964468393632107359136257 17223351295224080519352193)
  ·
    refine ⟨12917513471418060389514145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17223351295224080519352193 12917513471418060389514145)
    ·
      refine ⟨9688135103563545292135609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12917513471418060389514145 9688135103563545292135609)
      ·
        refine ⟨7266101327672658969101707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9688135103563545292135609 7266101327672658969101707)
        ·
          refine ⟨10899151991508988453652561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266101327672658969101707 10899151991508988453652561)
          ·
            refine ⟨8174363993631741340239421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10899151991508988453652561 8174363993631741340239421)
            ·
              refine ⟨3065386497611903002589783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8174363993631741340239421 3065386497611903002589783)
              ·
                refine ⟨4598079746417854503884675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065386497611903002589783 4598079746417854503884675)
                ·
                  refine ⟨6897119619626781755827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598079746417854503884675 6897119619626781755827013)
                  ·
                    refine ⟨1293209928680021579217565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897119619626781755827013 1293209928680021579217565)
                    ·
                      refine ⟨484953723255008092206587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1293209928680021579217565 484953723255008092206587)
                      ·
                        rfl

theorem cell23_944444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_944444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944444 prefixEnd_944444 := by exact prefixLift 944444
  have htrace : WordTrace (prefixWord ++ tailWord_944444) baseStart_944444 baseEnd_944444 := by
    simpa [prefixWord, tailWord_944444, baseEnd_944444] using wordTrace_append hprefix tailTrace_944444
  have hstable : (prefixWord ++ tailWord_944444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944444).length < 2 ^ (prefixWord ++ tailWord_944444).sum := by decide
  have hdescent : baseEnd_944444 < baseStart_944444 := by decide
  rcases family_descends (prefixWord ++ tailWord_944444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944447 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 8]
def baseStart_944447 : Nat := 118140960795 + 944447 * 2 ^ 59
def prefixEnd_944447 : Nat := 4983230072969 + 3 ^ 40 * 944447 * 2
def baseEnd_944447 : Nat := 53883918188552397829897

theorem tailTrace_944447 : CollatzResearch.WordTrace tailWord_944447 prefixEnd_944447 53883918188552397829897 := by
  unfold tailWord_944447
  simp only [CollatzResearch.WordTrace]
  refine ⟨34446812009437292551063595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22964541339624861700709063 34446812009437292551063595)
  ·
    refine ⟨51670218014155938826595393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34446812009437292551063595 51670218014155938826595393)
    ·
      refine ⟨38752663510616954119946545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51670218014155938826595393 38752663510616954119946545)
      ·
        refine ⟨29064497632962715589959909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38752663510616954119946545 29064497632962715589959909)
        ·
          refine ⟨5449593306180509173117483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29064497632962715589959909 5449593306180509173117483)
          ·
            refine ⟨8174389959270763759676225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449593306180509173117483 8174389959270763759676225)
            ·
              refine ⟨6130792469453072819757169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174389959270763759676225 6130792469453072819757169)
              ·
                refine ⟨4598094352089804614817877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130792469453072819757169 4598094352089804614817877)
                ·
                  refine ⟨53883918188552397829897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4598094352089804614817877 53883918188552397829897)
                  ·
                    rfl

theorem cell23_944447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 8].length) (baseStart_944447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944447 prefixEnd_944447 := by exact prefixLift 944447
  have htrace : WordTrace (prefixWord ++ tailWord_944447) baseStart_944447 baseEnd_944447 := by
    simpa [prefixWord, tailWord_944447, baseEnd_944447] using wordTrace_append hprefix tailTrace_944447
  have hstable : (prefixWord ++ tailWord_944447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944447).length < 2 ^ (prefixWord ++ tailWord_944447).sum := by decide
  have hdescent : baseEnd_944447 < baseStart_944447 := by decide
  rcases family_descends (prefixWord ++ tailWord_944447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944451 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 1, 4]
def baseStart_944451 : Nat := 118140960795 + 944451 * 2 ^ 59
def prefixEnd_944451 : Nat := 4983230072969 + 3 ^ 40 * 944451 * 2
def baseEnd_944451 : Nat := 161652439206529854939685

theorem tailTrace_944451 : CollatzResearch.WordTrace tailWord_944451 prefixEnd_944451 161652439206529854939685 := by
  unfold tailWord_944451
  simp only [CollatzResearch.WordTrace]
  refine ⟨34446957901422801234209207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22964638600948534156139471 34446957901422801234209207)
  ·
    refine ⟨51670436852134201851313811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34446957901422801234209207 51670436852134201851313811)
    ·
      refine ⟨77505655278201302776970717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51670436852134201851313811 77505655278201302776970717)
      ·
        refine ⟨29064620729325488541364019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77505655278201302776970717 29064620729325488541364019)
        ·
          refine ⟨43596931093988232812046029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29064620729325488541364019 43596931093988232812046029)
          ·
            refine ⟨16348849160245587304517261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43596931093988232812046029 16348849160245587304517261)
            ·
              refine ⟨6130818435092095239193973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16348849160245587304517261 6130818435092095239193973)
              ·
                refine ⟨574764228289883928674435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6130818435092095239193973 574764228289883928674435)
                ·
                  refine ⟨862146342434825893011653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574764228289883928674435 862146342434825893011653)
                  ·
                    refine ⟨161652439206529854939685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862146342434825893011653 161652439206529854939685)
                    ·
                      rfl

theorem cell23_944451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 4].length) (baseStart_944451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944451 prefixEnd_944451 := by exact prefixLift 944451
  have htrace : WordTrace (prefixWord ++ tailWord_944451) baseStart_944451 baseEnd_944451 := by
    simpa [prefixWord, tailWord_944451, baseEnd_944451] using wordTrace_append hprefix tailTrace_944451
  have hstable : (prefixWord ++ tailWord_944451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944451).length < 2 ^ (prefixWord ++ tailWord_944451).sum := by decide
  have hdescent : baseEnd_944451 < baseStart_944451 := by decide
  rcases family_descends (prefixWord ++ tailWord_944451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944464 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 6]
def baseStart_944464 : Nat := 118140960795 + 944464 * 2 ^ 59
def prefixEnd_944464 : Nat := 4983230072969 + 3 ^ 40 * 944464 * 2
def baseEnd_944464 : Nat := 53884888096455334884055

theorem tailTrace_944464 : CollatzResearch.WordTrace tailWord_944464 prefixEnd_944464 53884888096455334884055 := by
  unfold tailWord_944464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17223716025187852227216223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22964954700250469636288297 17223716025187852227216223)
  ·
    refine ⟨25835574037781778340824335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17223716025187852227216223 25835574037781778340824335)
    ·
      refine ⟨38753361056672667511236503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25835574037781778340824335 38753361056672667511236503)
      ·
        refine ⟨58130041585009001266854755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38753361056672667511236503 58130041585009001266854755)
        ·
          refine ⟨87195062377513501900282133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58130041585009001266854755 87195062377513501900282133)
          ·
            refine ⟨4087268548945945401575725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87195062377513501900282133 4087268548945945401575725)
            ·
              refine ⟨1532725705854729525590897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4087268548945945401575725 1532725705854729525590897)
              ·
                refine ⟨1149544279391047144193173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532725705854729525590897 1149544279391047144193173)
                ·
                  refine ⟨53884888096455334884055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1149544279391047144193173 53884888096455334884055)
                  ·
                    rfl

theorem cell23_944464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_944464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944464 prefixEnd_944464 := by exact prefixLift 944464
  have htrace : WordTrace (prefixWord ++ tailWord_944464) baseStart_944464 baseEnd_944464 := by
    simpa [prefixWord, tailWord_944464, baseEnd_944464] using wordTrace_append hprefix tailTrace_944464
  have hstable : (prefixWord ++ tailWord_944464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944464).length < 2 ^ (prefixWord ++ tailWord_944464).sum := by decide
  have hdescent : baseEnd_944464 < baseStart_944464 := by decide
  rcases family_descends (prefixWord ++ tailWord_944464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944468 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_944468 : Nat := 118140960795 + 944468 * 2 ^ 59
def prefixEnd_944468 : Nat := 4983230072969 + 3 ^ 40 * 944468 * 2
def baseEnd_944468 : Nat := 161655348930238666102159

theorem tailTrace_944468 : CollatzResearch.WordTrace tailWord_944468 prefixEnd_944468 161655348930238666102159 := by
  unfold tailWord_944468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17223788971180606568789029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22965051961574142091718705 17223788971180606568789029)
  ·
    refine ⟨3229460432096363731647943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17223788971180606568789029 3229460432096363731647943)
    ·
      refine ⟨4844190648144545597471915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3229460432096363731647943 4844190648144545597471915)
      ·
        refine ⟨7266285972216818396207873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4844190648144545597471915 7266285972216818396207873)
        ·
          refine ⟨5449714479162613797155905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7266285972216818396207873 5449714479162613797155905)
          ·
            refine ⟨4087285859371960347866929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5449714479162613797155905 4087285859371960347866929)
            ·
              refine ⟨3065464394528970260900197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087285859371960347866929 3065464394528970260900197)
              ·
                refine ⟨574774573974181923918787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3065464394528970260900197 574774573974181923918787)
                ·
                  refine ⟨862161860961272885878181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574774573974181923918787 862161860961272885878181)
                  ·
                    refine ⟨161655348930238666102159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862161860961272885878181 161655348930238666102159)
                    ·
                      rfl

theorem cell23_944468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_944468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944468 prefixEnd_944468 := by exact prefixLift 944468
  have htrace : WordTrace (prefixWord ++ tailWord_944468) baseStart_944468 baseEnd_944468 := by
    simpa [prefixWord, tailWord_944468, baseEnd_944468] using wordTrace_append hprefix tailTrace_944468
  have hstable : (prefixWord ++ tailWord_944468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944468).length < 2 ^ (prefixWord ++ tailWord_944468).sum := by decide
  have hdescent : baseEnd_944468 < baseStart_944468 := by decide
  rcases family_descends (prefixWord ++ tailWord_944468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944508 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_944508 : Nat := 118140960795 + 944508 * 2 ^ 59
def prefixEnd_944508 : Nat := 4983230072969 + 3 ^ 40 * 944508 * 2
def baseEnd_944508 : Nat := 484986586016895841806293

theorem tailTrace_944508 : CollatzResearch.WordTrace tailWord_944508 prefixEnd_944508 484986586016895841806293 := by
  unfold tailWord_944508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224518431108149984517089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22966024574810866646022785 17224518431108149984517089)
  ·
    refine ⟨12918388823331112488387817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17224518431108149984517089 12918388823331112488387817)
    ·
      refine ⟨9688791617498334366290863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12918388823331112488387817 9688791617498334366290863)
      ·
        refine ⟨14533187426247501549436295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688791617498334366290863 14533187426247501549436295)
        ·
          refine ⟨21799781139371252324154443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14533187426247501549436295 21799781139371252324154443)
          ·
            refine ⟨32699671709056878486231665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21799781139371252324154443 32699671709056878486231665)
            ·
              refine ⟨24524753781792658864673749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32699671709056878486231665 24524753781792658864673749)
              ·
                refine ⟨574798916760765442140791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24524753781792658864673749 574798916760765442140791)
                ·
                  refine ⟨862198375141148163211187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574798916760765442140791 862198375141148163211187)
                  ·
                    refine ⟨1293297562711722244816781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 862198375141148163211187 1293297562711722244816781)
                    ·
                      refine ⟨484986586016895841806293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1293297562711722244816781 484986586016895841806293)
                      ·
                        rfl

theorem cell23_944508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_944508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944508 prefixEnd_944508 := by exact prefixLift 944508
  have htrace : WordTrace (prefixWord ++ tailWord_944508) baseStart_944508 baseEnd_944508 := by
    simpa [prefixWord, tailWord_944508, baseEnd_944508] using wordTrace_append hprefix tailTrace_944508
  have hstable : (prefixWord ++ tailWord_944508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944508).length < 2 ^ (prefixWord ++ tailWord_944508).sum := by decide
  have hdescent : baseEnd_944508 < baseStart_944508 := by decide
  rcases family_descends (prefixWord ++ tailWord_944508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944544 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_944544 : Nat := 118140960795 + 944544 * 2 ^ 59
def prefixEnd_944544 : Nat := 4983230072969 + 3 ^ 40 * 944544 * 2
def baseEnd_944544 : Nat := 485005071320457700956127

theorem tailTrace_944544 : CollatzResearch.WordTrace tailWord_944544 prefixEnd_944544 485005071320457700956127 := by
  unfold tailWord_944544
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225174945042939058672343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22966899926723918744896457 17225174945042939058672343)
  ·
    refine ⟨25837762417564408588008515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17225174945042939058672343 25837762417564408588008515)
    ·
      refine ⟨38756643626346612882012773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25837762417564408588008515 38756643626346612882012773)
      ·
        refine ⟨7266870679939989915377395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38756643626346612882012773 7266870679939989915377395)
        ·
          refine ⟨10900306019909984873066093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266870679939989915377395 10900306019909984873066093)
          ·
            refine ⟨4087614757466244327399785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10900306019909984873066093 4087614757466244327399785)
            ·
              refine ⟨3065711068099683245549839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087614757466244327399785 3065711068099683245549839)
              ·
                refine ⟨4598566602149524868324759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065711068099683245549839 4598566602149524868324759)
                ·
                  refine ⟨6897849903224287302487139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598566602149524868324759 6897849903224287302487139)
                  ·
                    refine ⟨10346774854836430953730709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6897849903224287302487139 10346774854836430953730709)
                    ·
                      refine ⟨485005071320457700956127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10346774854836430953730709 485005071320457700956127)
                      ·
                        rfl

theorem cell23_944544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_944544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944544 prefixEnd_944544 := by exact prefixLift 944544
  have htrace : WordTrace (prefixWord ++ tailWord_944544) baseStart_944544 baseEnd_944544 := by
    simpa [prefixWord, tailWord_944544, baseEnd_944544] using wordTrace_append hprefix tailTrace_944544
  have hstable : (prefixWord ++ tailWord_944544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944544).length < 2 ^ (prefixWord ++ tailWord_944544).sum := by decide
  have hdescent : baseEnd_944544 < baseStart_944544 := by decide
  rcases family_descends (prefixWord ++ tailWord_944544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944545 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_944545 : Nat := 118140960795 + 944545 * 2 ^ 59
def prefixEnd_944545 : Nat := 4983230072969 + 3 ^ 40 * 944545 * 2
def baseEnd_944545 : Nat := 161668528267037399014541

theorem tailTrace_944545 : CollatzResearch.WordTrace tailWord_944545 prefixEnd_944545 161668528267037399014541 := by
  unfold tailWord_944545
  simp only [CollatzResearch.WordTrace]
  refine ⟨34450386363082255288131089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22966924242054836858754059 34450386363082255288131089)
  ·
    refine ⟨25837789772311691466098317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34450386363082255288131089 25837789772311691466098317)
    ·
      refine ⟨9689171164616884299786869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25837789772311691466098317 9689171164616884299786869)
      ·
        refine ⟨908359796682832903105019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9689171164616884299786869 908359796682832903105019)
        ·
          refine ⟨1362539695024249354657529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908359796682832903105019 1362539695024249354657529)
          ·
            refine ⟨1021904771268187015993147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1362539695024249354657529 1021904771268187015993147)
            ·
              refine ⟨1532857156902280523989721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021904771268187015993147 1532857156902280523989721)
              ·
                refine ⟨1149642867676710392992291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532857156902280523989721 1149642867676710392992291)
                ·
                  refine ⟨1724464301515065589488437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149642867676710392992291 1724464301515065589488437)
                  ·
                    refine ⟨161668528267037399014541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1724464301515065589488437 161668528267037399014541)
                    ·
                      rfl

theorem cell23_944545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_944545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944545 prefixEnd_944545 := by exact prefixLift 944545
  have htrace : WordTrace (prefixWord ++ tailWord_944545) baseStart_944545 baseEnd_944545 := by
    simpa [prefixWord, tailWord_944545, baseEnd_944545] using wordTrace_append hprefix tailTrace_944545
  have hstable : (prefixWord ++ tailWord_944545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944545).length < 2 ^ (prefixWord ++ tailWord_944545).sum := by decide
  have hdescent : baseEnd_944545 < baseStart_944545 := by decide
  rcases family_descends (prefixWord ++ tailWord_944545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944548 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_944548 : Nat := 118140960795 + 944548 * 2 ^ 59
def prefixEnd_944548 : Nat := 4983230072969 + 3 ^ 40 * 944548 * 2
def baseEnd_944548 : Nat := 485007125243075685306109

theorem tailTrace_944548 : CollatzResearch.WordTrace tailWord_944548 prefixEnd_944548 485007125243075685306109 := by
  unfold tailWord_944548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225247891035693400245149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22966997188047591200326865 17225247891035693400245149)
  ·
    refine ⟨6459467959138385025091931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17225247891035693400245149 6459467959138385025091931)
    ·
      refine ⟨9689201938707577537637897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6459467959138385025091931 9689201938707577537637897)
      ·
        refine ⟨7266901454030683153228423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9689201938707577537637897 7266901454030683153228423)
        ·
          refine ⟨10900352181046024729842635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266901454030683153228423 10900352181046024729842635)
          ·
            refine ⟨16350528271569037094763953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900352181046024729842635 16350528271569037094763953)
            ·
              refine ⟨12262896203676777821072965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16350528271569037094763953 12262896203676777821072965)
              ·
                refine ⟨2299293038189395841451181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12262896203676777821072965 2299293038189395841451181)
                ·
                  refine ⟨862234889321023440544193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2299293038189395841451181 862234889321023440544193)
                  ·
                    refine ⟨646676166990767580408145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 862234889321023440544193 646676166990767580408145)
                    ·
                      refine ⟨485007125243075685306109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646676166990767580408145 485007125243075685306109)
                      ·
                        rfl

theorem cell23_944548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_944548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944548 prefixEnd_944548 := by exact prefixLift 944548
  have htrace : WordTrace (prefixWord ++ tailWord_944548) baseStart_944548 baseEnd_944548 := by
    simpa [prefixWord, tailWord_944548, baseEnd_944548] using wordTrace_append hprefix tailTrace_944548
  have hstable : (prefixWord ++ tailWord_944548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944548).length < 2 ^ (prefixWord ++ tailWord_944548).sum := by decide
  have hdescent : baseEnd_944548 < baseStart_944548 := by decide
  rcases family_descends (prefixWord ++ tailWord_944548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944561 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_944561 : Nat := 118140960795 + 944561 * 2 ^ 59
def prefixEnd_944561 : Nat := 4983230072969 + 3 ^ 40 * 944561 * 2
def baseEnd_944561 : Nat := 485013800491584134443549

theorem tailTrace_944561 : CollatzResearch.WordTrace tailWord_944561 prefixEnd_944561 485013800491584134443549 := by
  unfold tailWord_944561
  simp only [CollatzResearch.WordTrace]
  refine ⟨34450969931024290020713537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22967313287349526680475691 34450969931024290020713537)
  ·
    refine ⟨25838227448268217515535153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34450969931024290020713537 25838227448268217515535153)
    ·
      refine ⟨19378670586201163136651365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25838227448268217515535153 19378670586201163136651365)
      ·
        refine ⟨3633500734912718088122131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19378670586201163136651365 3633500734912718088122131)
        ·
          refine ⟨5450251102369077132183197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633500734912718088122131 5450251102369077132183197)
          ·
            refine ⟨2043844163388403924568699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5450251102369077132183197 2043844163388403924568699)
            ·
              refine ⟨3065766245082605886853049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043844163388403924568699 3065766245082605886853049)
              ·
                refine ⟨2299324683811954415139787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065766245082605886853049 2299324683811954415139787)
                ·
                  refine ⟨3448987025717931622709681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299324683811954415139787 3448987025717931622709681)
                  ·
                    refine ⟨2586740269288448717032261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448987025717931622709681 2586740269288448717032261)
                    ·
                      refine ⟨485013800491584134443549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2586740269288448717032261 485013800491584134443549)
                      ·
                        rfl

theorem cell23_944561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_944561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944561 prefixEnd_944561 := by exact prefixLift 944561
  have htrace : WordTrace (prefixWord ++ tailWord_944561) baseStart_944561 baseEnd_944561 := by
    simpa [prefixWord, tailWord_944561, baseEnd_944561] using wordTrace_append hprefix tailTrace_944561
  have hstable : (prefixWord ++ tailWord_944561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944561).length < 2 ^ (prefixWord ++ tailWord_944561).sum := by decide
  have hdescent : baseEnd_944561 < baseStart_944561 := by decide
  rcases family_descends (prefixWord ++ tailWord_944561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944565 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_944565 : Nat := 118140960795 + 944565 * 2 ^ 59
def prefixEnd_944565 : Nat := 4983230072969 + 3 ^ 40 * 944565 * 2
def baseEnd_944565 : Nat := 485015854414202118793531

theorem tailTrace_944565 : CollatzResearch.WordTrace tailWord_944565 prefixEnd_944565 485015854414202118793531 := by
  unfold tailWord_944565
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451115823009798703859149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22967410548673199135906099 34451115823009798703859149)
  ·
    refine ⟨12919168433628674513947181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34451115823009798703859149 12919168433628674513947181)
    ·
      refine ⟨4844688162610752942730193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12919168433628674513947181 4844688162610752942730193)
      ·
        refine ⟨3633516121958064707047645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4844688162610752942730193 3633516121958064707047645)
        ·
          refine ⟨1362568545734274265142867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3633516121958064707047645 1362568545734274265142867)
          ·
            refine ⟨2043852818601411397714301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362568545734274265142867 2043852818601411397714301)
            ·
              refine ⟨766444806975529274142863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2043852818601411397714301 766444806975529274142863)
              ·
                refine ⟨1149667210463293911214295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766444806975529274142863 1149667210463293911214295)
                ·
                  refine ⟨1724500815694940866821443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149667210463293911214295 1724500815694940866821443)
                  ·
                    refine ⟨2586751223542411300232165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724500815694940866821443 2586751223542411300232165)
                    ·
                      refine ⟨485015854414202118793531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2586751223542411300232165 485015854414202118793531)
                      ·
                        rfl

theorem cell23_944565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_944565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944565 prefixEnd_944565 := by exact prefixLift 944565
  have htrace : WordTrace (prefixWord ++ tailWord_944565) baseStart_944565 baseEnd_944565 := by
    simpa [prefixWord, tailWord_944565, baseEnd_944565] using wordTrace_append hprefix tailTrace_944565
  have hstable : (prefixWord ++ tailWord_944565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944565).length < 2 ^ (prefixWord ++ tailWord_944565).sum := by decide
  have hdescent : baseEnd_944565 < baseStart_944565 := by decide
  rcases family_descends (prefixWord ++ tailWord_944565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944584 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_944584 : Nat := 118140960795 + 944584 * 2 ^ 59
def prefixEnd_944584 : Nat := 4983230072969 + 3 ^ 40 * 944584 * 2
def baseEnd_944584 : Nat := 161675203515545848151981

theorem tailTrace_944584 : CollatzResearch.WordTrace tailWord_944584 prefixEnd_944584 161675203515545848151981 := by
  unfold tailWord_944584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225904404970482474400403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22967872539960643299200537 17225904404970482474400403)
  ·
    refine ⟨25838856607455723711600605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17225904404970482474400403 25838856607455723711600605)
    ·
      refine ⟨9689571227795896391850227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25838856607455723711600605 9689571227795896391850227)
      ·
        refine ⟨14534356841693844587775341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9689571227795896391850227 14534356841693844587775341)
        ·
          refine ⟨5450383815635191720415753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14534356841693844587775341 5450383815635191720415753)
          ·
            refine ⟨4087787861726393790311815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450383815635191720415753 4087787861726393790311815)
            ·
              refine ⟨6131681792589590685467723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087787861726393790311815 6131681792589590685467723)
              ·
                refine ⟨9197522688884386028201585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131681792589590685467723 9197522688884386028201585)
                ·
                  refine ⟨6898142016663289521151189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9197522688884386028201585 6898142016663289521151189)
                  ·
                    refine ⟨161675203515545848151981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6898142016663289521151189 161675203515545848151981)
                    ·
                      rfl

theorem cell23_944584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_944584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944584 prefixEnd_944584 := by exact prefixLift 944584
  have htrace : WordTrace (prefixWord ++ tailWord_944584) baseStart_944584 baseEnd_944584 := by
    simpa [prefixWord, tailWord_944584, baseEnd_944584] using wordTrace_append hprefix tailTrace_944584
  have hstable : (prefixWord ++ tailWord_944584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944584).length < 2 ^ (prefixWord ++ tailWord_944584).sum := by decide
  have hdescent : baseEnd_944584 < baseStart_944584 := by decide
  rcases family_descends (prefixWord ++ tailWord_944584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944588 : List Nat := [2, 2, 1, 4, 4, 1, 1, 8]
def baseStart_944588 : Nat := 118140960795 + 944588 * 2 ^ 59
def prefixEnd_944588 : Nat := 4983230072969 + 3 ^ 40 * 944588 * 2
def baseEnd_944588 : Nat := 17963987572935389955775

theorem tailTrace_944588 : CollatzResearch.WordTrace tailWord_944588 prefixEnd_944588 17963987572935389955775 := by
  unfold tailWord_944588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225977350963236815973209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22967969801284315754630945 17225977350963236815973209)
  ·
    refine ⟨12919483013222427611979907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17225977350963236815973209 12919483013222427611979907)
    ·
      refine ⟨19379224519833641417969861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12919483013222427611979907 19379224519833641417969861)
      ·
        refine ⟨3633604597468807765869349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19379224519833641417969861 3633604597468807765869349)
        ·
          refine ⟨681300862025401456100503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3633604597468807765869349 681300862025401456100503)
          ·
            refine ⟨1021951293038102184150755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681300862025401456100503 1021951293038102184150755)
            ·
              refine ⟨1532926939557153276226133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021951293038102184150755 1532926939557153276226133)
              ·
                refine ⟨17963987572935389955775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1532926939557153276226133 17963987572935389955775)
                ·
                  rfl

theorem cell23_944588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 8].length) (baseStart_944588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944588 prefixEnd_944588 := by exact prefixLift 944588
  have htrace : WordTrace (prefixWord ++ tailWord_944588) baseStart_944588 baseEnd_944588 := by
    simpa [prefixWord, tailWord_944588, baseEnd_944588] using wordTrace_append hprefix tailTrace_944588
  have hstable : (prefixWord ++ tailWord_944588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944588).length < 2 ^ (prefixWord ++ tailWord_944588).sum := by decide
  have hdescent : baseEnd_944588 < baseStart_944588 := by decide
  rcases family_descends (prefixWord ++ tailWord_944588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944608 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2]
def baseStart_944608 : Nat := 118140960795 + 944608 * 2 ^ 59
def prefixEnd_944608 : Nat := 4983230072969 + 3 ^ 40 * 944608 * 2
def baseEnd_944608 : Nat := 485037934082345450555833

theorem tailTrace_944608 : CollatzResearch.WordTrace tailWord_944608 prefixEnd_944608 485037934082345450555833 := by
  unfold tailWord_944608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226342080927008523837239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22968456107902678031782985 17226342080927008523837239)
  ·
    refine ⟨25839513121390512785755859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17226342080927008523837239 25839513121390512785755859)
    ·
      refine ⟨38759269682085769178633789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25839513121390512785755859 38759269682085769178633789)
      ·
        refine ⟨14534726130782163441987671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38759269682085769178633789 14534726130782163441987671)
        ·
          refine ⟨21802089196173245162981507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14534726130782163441987671 21802089196173245162981507)
          ·
            refine ⟨32703133794259867744472261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21802089196173245162981507 32703133794259867744472261)
            ·
              refine ⟨6131837586423725202088549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32703133794259867744472261 6131837586423725202088549)
              ·
                refine ⟨1149719547454448475391603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6131837586423725202088549 1149719547454448475391603)
                ·
                  refine ⟨1724579321181672713087405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149719547454448475391603 1724579321181672713087405)
                  ·
                    refine ⟨646717245443127267407777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724579321181672713087405 646717245443127267407777)
                    ·
                      refine ⟨485037934082345450555833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646717245443127267407777 485037934082345450555833)
                      ·
                        rfl

theorem cell23_944608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_944608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944608 prefixEnd_944608 := by exact prefixLift 944608
  have htrace : WordTrace (prefixWord ++ tailWord_944608) baseStart_944608 baseEnd_944608 := by
    simpa [prefixWord, tailWord_944608, baseEnd_944608] using wordTrace_append hprefix tailTrace_944608
  have hstable : (prefixWord ++ tailWord_944608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944608).length < 2 ^ (prefixWord ++ tailWord_944608).sum := by decide
  have hdescent : baseEnd_944608 < baseStart_944608 := by decide
  rcases family_descends (prefixWord ++ tailWord_944608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944624 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_944624 : Nat := 118140960795 + 944624 * 2 ^ 59
def prefixEnd_944624 : Nat := 4983230072969 + 3 ^ 40 * 944624 * 2
def baseEnd_944624 : Nat := 485046149772817387955759

theorem tailTrace_944624 : CollatzResearch.WordTrace tailWord_944624 prefixEnd_944624 485046149772817387955759 := by
  unfold tailWord_944624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226633864898025890128463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22968845153197367853504617 17226633864898025890128463)
  ·
    refine ⟨25839950797347038835192695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17226633864898025890128463 25839950797347038835192695)
    ·
      refine ⟨38759926196020558252789043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25839950797347038835192695 38759926196020558252789043)
      ·
        refine ⟨58139889294030837379183565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38759926196020558252789043 58139889294030837379183565)
        ·
          refine ⟨21802458485261564017193837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58139889294030837379183565 21802458485261564017193837)
          ·
            refine ⟨8175921931973086506447689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21802458485261564017193837 8175921931973086506447689)
            ·
              refine ⟨6131941448979814879835767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8175921931973086506447689 6131941448979814879835767)
              ·
                refine ⟨9197912173469722319753651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131941448979814879835767 9197912173469722319753651)
                ·
                  refine ⟨13796868260204583479630477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9197912173469722319753651 13796868260204583479630477)
                  ·
                    refine ⟨5173825597576718804861429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13796868260204583479630477 5173825597576718804861429)
                    ·
                      refine ⟨485046149772817387955759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5173825597576718804861429 485046149772817387955759)
                      ·
                        rfl

theorem cell23_944624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_944624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944624 prefixEnd_944624 := by exact prefixLift 944624
  have htrace : WordTrace (prefixWord ++ tailWord_944624) baseStart_944624 baseEnd_944624 := by
    simpa [prefixWord, tailWord_944624, baseEnd_944624] using wordTrace_append hprefix tailTrace_944624
  have hstable : (prefixWord ++ tailWord_944624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944624).length < 2 ^ (prefixWord ++ tailWord_944624).sum := by decide
  have hdescent : baseEnd_944624 < baseStart_944624 := by decide
  rcases family_descends (prefixWord ++ tailWord_944624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944651 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_944651 : Nat := 118140960795 + 944651 * 2 ^ 59
def prefixEnd_944651 : Nat := 4983230072969 + 3 ^ 40 * 944651 * 2
def baseEnd_944651 : Nat := 485060013750488782318135

theorem tailTrace_944651 : CollatzResearch.WordTrace tailWord_944651 prefixEnd_944651 485060013750488782318135 := by
  unfold tailWord_944651
  simp only [CollatzResearch.WordTrace]
  refine ⟨34454252500698235391489807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22969501667132156927659871 34454252500698235391489807)
  ·
    refine ⟨51681378751047353087234711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34454252500698235391489807 51681378751047353087234711)
    ·
      refine ⟨77522068126571029630852067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51681378751047353087234711 77522068126571029630852067)
      ·
        refine ⟨116283102189856544446278101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77522068126571029630852067 116283102189856544446278101)
        ·
          refine ⟨2725385207574762760459643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 116283102189856544446278101 2725385207574762760459643)
          ·
            refine ⟨4088077811362144140689465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725385207574762760459643 4088077811362144140689465)
            ·
              refine ⟨3066058358521608105517099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088077811362144140689465 3066058358521608105517099)
              ·
                refine ⟨4599087537782412158275649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066058358521608105517099 4599087537782412158275649)
                ·
                  refine ⟨3449315653336809118706737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599087537782412158275649 3449315653336809118706737)
                  ·
                    refine ⟨2586986740002606839030053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3449315653336809118706737 2586986740002606839030053)
                    ·
                      refine ⟨485060013750488782318135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2586986740002606839030053 485060013750488782318135)
                      ·
                        rfl

theorem cell23_944651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_944651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944651 prefixEnd_944651 := by exact prefixLift 944651
  have htrace : WordTrace (prefixWord ++ tailWord_944651) baseStart_944651 baseEnd_944651 := by
    simpa [prefixWord, tailWord_944651, baseEnd_944651] using wordTrace_append hprefix tailTrace_944651
  have hstable : (prefixWord ++ tailWord_944651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944651).length < 2 ^ (prefixWord ++ tailWord_944651).sum := by decide
  have hdescent : baseEnd_944651 < baseStart_944651 := by decide
  rcases family_descends (prefixWord ++ tailWord_944651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944684 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_944684 : Nat := 118140960795 + 944684 * 2 ^ 59
def prefixEnd_944684 : Nat := 4983230072969 + 3 ^ 40 * 944684 * 2
def baseEnd_944684 : Nat := 485076958612087153205483

theorem tailTrace_944684 : CollatzResearch.WordTrace tailWord_944684 prefixEnd_944684 485076958612087153205483 := by
  unfold tailWord_944684
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227728054789341013720553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22970304073052454684960737 17227728054789341013720553)
  ·
    refine ⟨12920796041092005760290415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17227728054789341013720553 12920796041092005760290415)
    ·
      refine ⟨19381194061638008640435623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12920796041092005760290415 19381194061638008640435623)
      ·
        refine ⟨29071791092457012960653435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381194061638008640435623 29071791092457012960653435)
        ·
          refine ⟨43607686638685519440980153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29071791092457012960653435 43607686638685519440980153)
          ·
            refine ⟨32705764979014139580735115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43607686638685519440980153 32705764979014139580735115)
            ·
              refine ⟨49058647468521209371102673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32705764979014139580735115 49058647468521209371102673)
              ·
                refine ⟨36793985601390907028327005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49058647468521209371102673 36793985601390907028327005)
                ·
                  refine ⟨13797744600521590135622627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36793985601390907028327005 13797744600521590135622627)
                  ·
                    refine ⟨20696616900782385203433941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13797744600521590135622627 20696616900782385203433941)
                    ·
                      refine ⟨485076958612087153205483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20696616900782385203433941 485076958612087153205483)
                      ·
                        rfl

theorem cell23_944684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_944684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944684 prefixEnd_944684 := by exact prefixLift 944684
  have htrace : WordTrace (prefixWord ++ tailWord_944684) baseStart_944684 baseEnd_944684 := by
    simpa [prefixWord, tailWord_944684, baseEnd_944684] using wordTrace_append hprefix tailTrace_944684
  have hstable : (prefixWord ++ tailWord_944684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944684).length < 2 ^ (prefixWord ++ tailWord_944684).sum := by decide
  have hdescent : baseEnd_944684 < baseStart_944684 := by decide
  rcases family_descends (prefixWord ++ tailWord_944684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944691 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 2, 5]
def baseStart_944691 : Nat := 118140960795 + 944691 * 2 ^ 59
def prefixEnd_944691 : Nat := 4983230072969 + 3 ^ 40 * 944691 * 2
def baseEnd_944691 : Nat := 161693517658889541939317

theorem tailTrace_944691 : CollatzResearch.WordTrace tailWord_944691 prefixEnd_944691 161693517658889541939317 := by
  unfold tailWord_944691
  simp only [CollatzResearch.WordTrace]
  refine ⟨34455711420553322222945927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22970474280368881481963951 34455711420553322222945927)
  ·
    refine ⟨51683567130829983334418891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34455711420553322222945927 51683567130829983334418891)
    ·
      refine ⟨77525350696244975001628337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51683567130829983334418891 77525350696244975001628337)
      ·
        refine ⟨58144013022183731251221253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77525350696244975001628337 58144013022183731251221253)
        ·
          refine ⟨10902002441659449609603985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58144013022183731251221253 10902002441659449609603985)
          ·
            refine ⟨8176501831244587207202989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10902002441659449609603985 8176501831244587207202989)
            ·
              refine ⟨3066188186716720202701121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8176501831244587207202989 3066188186716720202701121)
              ·
                refine ⟨2299641140037540152025841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066188186716720202701121 2299641140037540152025841)
                ·
                  refine ⟨1724730855028155114019381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299641140037540152025841 1724730855028155114019381)
                  ·
                    refine ⟨161693517658889541939317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1724730855028155114019381 161693517658889541939317)
                    ·
                      rfl

theorem cell23_944691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 5].length) (baseStart_944691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944691 prefixEnd_944691 := by exact prefixLift 944691
  have htrace : WordTrace (prefixWord ++ tailWord_944691) baseStart_944691 baseEnd_944691 := by
    simpa [prefixWord, tailWord_944691, baseEnd_944691] using wordTrace_append hprefix tailTrace_944691
  have hstable : (prefixWord ++ tailWord_944691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944691).length < 2 ^ (prefixWord ++ tailWord_944691).sum := by decide
  have hdescent : baseEnd_944691 < baseStart_944691 := by decide
  rcases family_descends (prefixWord ++ tailWord_944691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944701 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_944701 : Nat := 118140960795 + 944701 * 2 ^ 59
def prefixEnd_944701 : Nat := 4983230072969 + 3 ^ 40 * 944701 * 2
def baseEnd_944701 : Nat := 485085687783213586692905

theorem tailTrace_944701 : CollatzResearch.WordTrace tailWord_944701 prefixEnd_944701 485085687783213586692905 := by
  unfold tailWord_944701
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456076150517093930809957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22970717433678062620539971 34456076150517093930809957)
  ·
    refine ⟨6460514278221955112026867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34456076150517093930809957 6460514278221955112026867)
    ·
      refine ⟨9690771417332932668040301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460514278221955112026867 9690771417332932668040301)
      ·
        refine ⟨3634039281499849750515113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9690771417332932668040301 3634039281499849750515113)
        ·
          refine ⟨2725529461124887312886335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634039281499849750515113 2725529461124887312886335)
          ·
            refine ⟨4088294191687330969329503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725529461124887312886335 4088294191687330969329503)
            ·
              refine ⟨6132441287530996453994255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088294191687330969329503 6132441287530996453994255)
              ·
                refine ⟨9198661931296494680991383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132441287530996453994255 9198661931296494680991383)
                ·
                  refine ⟨13797992896944742021487075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198661931296494680991383 13797992896944742021487075)
                  ·
                    refine ⟨20696989345417113032230613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13797992896944742021487075 20696989345417113032230613)
                    ·
                      refine ⟨485085687783213586692905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20696989345417113032230613 485085687783213586692905)
                      ·
                        rfl

theorem cell23_944701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_944701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944701 prefixEnd_944701 := by exact prefixLift 944701
  have htrace : WordTrace (prefixWord ++ tailWord_944701) baseStart_944701 baseEnd_944701 := by
    simpa [prefixWord, tailWord_944701, baseEnd_944701] using wordTrace_append hprefix tailTrace_944701
  have hstable : (prefixWord ++ tailWord_944701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944701).length < 2 ^ (prefixWord ++ tailWord_944701).sum := by decide
  have hdescent : baseEnd_944701 < baseStart_944701 := by decide
  rcases family_descends (prefixWord ++ tailWord_944701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944748 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_944748 : Nat := 118140960795 + 944748 * 2 ^ 59
def prefixEnd_944748 : Nat := 4983230072969 + 3 ^ 40 * 944748 * 2
def baseEnd_944748 : Nat := 485109821373974902805189

theorem tailTrace_944748 : CollatzResearch.WordTrace tailWord_944748 prefixEnd_944748 485109821373974902805189 := by
  unfold tailWord_944748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228895190673410478885449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22971860254231213971847265 17228895190673410478885449)
  ·
    refine ⟨12921671393005057859164087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17228895190673410478885449 12921671393005057859164087)
    ·
      refine ⟨19382507089507586788746131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921671393005057859164087 19382507089507586788746131)
      ·
        refine ⟨29073760634261380183119197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19382507089507586788746131 29073760634261380183119197)
        ·
          refine ⟨10902660237848017568669699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29073760634261380183119197 10902660237848017568669699)
          ·
            refine ⟨16353990356772026353004549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902660237848017568669699 16353990356772026353004549)
            ·
              refine ⟨3066373191894754941188353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16353990356772026353004549 3066373191894754941188353)
              ·
                refine ⟨2299779893921066205891265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066373191894754941188353 2299779893921066205891265)
                ·
                  refine ⟨1724834920440799654418449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299779893921066205891265 1724834920440799654418449)
                  ·
                    refine ⟨1293626190330599740813837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1724834920440799654418449 1293626190330599740813837)
                    ·
                      refine ⟨485109821373974902805189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1293626190330599740813837 485109821373974902805189)
                      ·
                        rfl

theorem cell23_944748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_944748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944748 prefixEnd_944748 := by exact prefixLift 944748
  have htrace : WordTrace (prefixWord ++ tailWord_944748) baseStart_944748 baseEnd_944748 := by
    simpa [prefixWord, tailWord_944748, baseEnd_944748] using wordTrace_append hprefix tailTrace_944748
  have hstable : (prefixWord ++ tailWord_944748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944748).length < 2 ^ (prefixWord ++ tailWord_944748).sum := by decide
  have hdescent : baseEnd_944748 < baseStart_944748 := by decide
  rcases family_descends (prefixWord ++ tailWord_944748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944751 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 6]
def baseStart_944751 : Nat := 118140960795 + 944751 * 2 ^ 59
def prefixEnd_944751 : Nat := 4983230072969 + 3 ^ 40 * 944751 * 2
def baseEnd_944751 : Nat := 53901262423993154563075

theorem tailTrace_944751 : CollatzResearch.WordTrace tailWord_944751 prefixEnd_944751 53901262423993154563075 := by
  unfold tailWord_944751
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457899800335952470130107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22971933200223968313420071 34457899800335952470130107)
  ·
    refine ⟨51686849700503928705195161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34457899800335952470130107 51686849700503928705195161)
    ·
      refine ⟨38765137275377946528896371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51686849700503928705195161 38765137275377946528896371)
      ·
        refine ⟨58147705913066919793344557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38765137275377946528896371 58147705913066919793344557)
        ·
          refine ⟨21805389717400094922504209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58147705913066919793344557 21805389717400094922504209)
          ·
            refine ⟨16354042288050071191878157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21805389717400094922504209 16354042288050071191878157)
            ·
              refine ⟨6132765858018776696954309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16354042288050071191878157 6132765858018776696954309)
              ·
                refine ⟨1149893598378520630678933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6132765858018776696954309 1149893598378520630678933)
                ·
                  refine ⟨53901262423993154563075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1149893598378520630678933 53901262423993154563075)
                  ·
                    rfl

theorem cell23_944751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 6].length) (baseStart_944751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944751 prefixEnd_944751 := by exact prefixLift 944751
  have htrace : WordTrace (prefixWord ++ tailWord_944751) baseStart_944751 baseEnd_944751 := by
    simpa [prefixWord, tailWord_944751, baseEnd_944751] using wordTrace_append hprefix tailTrace_944751
  have hstable : (prefixWord ++ tailWord_944751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944751).length < 2 ^ (prefixWord ++ tailWord_944751).sum := by decide
  have hdescent : baseEnd_944751 < baseStart_944751 := by decide
  rcases family_descends (prefixWord ++ tailWord_944751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944855 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_944855 : Nat := 118140960795 + 944855 * 2 ^ 59
def prefixEnd_944855 : Nat := 4983230072969 + 3 ^ 40 * 944855 * 2
def baseEnd_944855 : Nat := 485164763804005984167197

theorem tailTrace_944855 : CollatzResearch.WordTrace tailWord_944855 prefixEnd_944855 485164763804005984167197 := by
  unfold tailWord_944855
  simp only [CollatzResearch.WordTrace]
  refine ⟨34461692991959178231916019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22974461994639452154610679 34461692991959178231916019)
  ·
    refine ⟨51692539487938767347874029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34461692991959178231916019 51692539487938767347874029)
    ·
      refine ⟨19384702307977037755452761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51692539487938767347874029 19384702307977037755452761)
      ·
        refine ⟨14538526730982778316589571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19384702307977037755452761 14538526730982778316589571)
        ·
          refine ⟨21807790096474167474884357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538526730982778316589571 21807790096474167474884357)
          ·
            refine ⟨4088960643088906401540817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21807790096474167474884357 4088960643088906401540817)
            ·
              refine ⟨3066720482316679801155613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088960643088906401540817 3066720482316679801155613)
              ·
                refine ⟨1150020180868754925433355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3066720482316679801155613 1150020180868754925433355)
                ·
                  refine ⟨1725030271303132388150033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150020180868754925433355 1725030271303132388150033)
                  ·
                    refine ⟨1293772703477349291112525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725030271303132388150033 1293772703477349291112525)
                    ·
                      refine ⟨485164763804005984167197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1293772703477349291112525 485164763804005984167197)
                      ·
                        rfl

theorem cell23_944855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_944855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944855 prefixEnd_944855 := by exact prefixLift 944855
  have htrace : WordTrace (prefixWord ++ tailWord_944855) baseStart_944855 baseEnd_944855 := by
    simpa [prefixWord, tailWord_944855, baseEnd_944855] using wordTrace_append hprefix tailTrace_944855
  have hstable : (prefixWord ++ tailWord_944855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944855).length < 2 ^ (prefixWord ++ tailWord_944855).sum := by decide
  have hdescent : baseEnd_944855 < baseStart_944855 := by decide
  rcases family_descends (prefixWord ++ tailWord_944855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944869 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_944869 : Nat := 118140960795 + 944869 * 2 ^ 59
def prefixEnd_944869 : Nat := 4983230072969 + 3 ^ 40 * 944869 * 2
def baseEnd_944869 : Nat := 485171952533168929392133

theorem tailTrace_944869 : CollatzResearch.WordTrace tailWord_944869 prefixEnd_944869 485171952533168929392133 := by
  unfold tailWord_944869
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462203613908458622925661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22974802409272305748617107 34462203613908458622925661)
  ·
    refine ⟨12923326355215671983597123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34462203613908458622925661 12923326355215671983597123)
    ·
      refine ⟨19384989532823507975395685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12923326355215671983597123 19384989532823507975395685)
      ·
        refine ⟨3634685537404407745386691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19384989532823507975395685 3634685537404407745386691)
        ·
          refine ⟨5452028306106611618080037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634685537404407745386691 5452028306106611618080037)
          ·
            refine ⟨1022255307394989678390007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5452028306106611618080037 1022255307394989678390007)
            ·
              refine ⟨1533382961092484517585011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022255307394989678390007 1533382961092484517585011)
              ·
                refine ⟨2300074441638726776377517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533382961092484517585011 2300074441638726776377517)
                ·
                  refine ⟨862527915614522541141569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2300074441638726776377517 862527915614522541141569)
                  ·
                    refine ⟨646895936710891905856177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 862527915614522541141569 646895936710891905856177)
                    ·
                      refine ⟨485171952533168929392133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646895936710891905856177 485171952533168929392133)
                      ·
                        rfl

theorem cell23_944869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_944869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944869 prefixEnd_944869 := by exact prefixLift 944869
  have htrace : WordTrace (prefixWord ++ tailWord_944869) baseStart_944869 baseEnd_944869 := by
    simpa [prefixWord, tailWord_944869, baseEnd_944869] using wordTrace_append hprefix tailTrace_944869
  have hstable : (prefixWord ++ tailWord_944869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944869).length < 2 ^ (prefixWord ++ tailWord_944869).sum := by decide
  have hdescent : baseEnd_944869 < baseStart_944869 := by decide
  rcases family_descends (prefixWord ++ tailWord_944869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944919 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_944919 : Nat := 118140960795 + 944919 * 2 ^ 59
def prefixEnd_944919 : Nat := 4983230072969 + 3 ^ 40 * 944919 * 2
def baseEnd_944919 : Nat := 485197626565893733766903

theorem tailTrace_944919 : CollatzResearch.WordTrace tailWord_944919 prefixEnd_944919 485197626565893733766903 := by
  unfold tailWord_944919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34464027263727317162245811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22976018175818211441497207 34464027263727317162245811)
  ·
    refine ⟨51696040895590975743368717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34464027263727317162245811 51696040895590975743368717)
    ·
      refine ⟨19386015335846615903763269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51696040895590975743368717 19386015335846615903763269)
      ·
        refine ⟨3634877875471240481955613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19386015335846615903763269 3634877875471240481955613)
        ·
          refine ⟨1363079203301715180733355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3634877875471240481955613 1363079203301715180733355)
          ·
            refine ⟨2044618804952572771100033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363079203301715180733355 2044618804952572771100033)
            ·
              refine ⟨1533464103714429578325025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044618804952572771100033 1533464103714429578325025)
              ·
                refine ⟨1150098077785822183743769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533464103714429578325025 1150098077785822183743769)
                ·
                  refine ⟨862573558339366637807827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150098077785822183743769 862573558339366637807827)
                  ·
                    refine ⟨1293860337509049956711741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 862573558339366637807827 1293860337509049956711741)
                    ·
                      refine ⟨485197626565893733766903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1293860337509049956711741 485197626565893733766903)
                      ·
                        rfl

theorem cell23_944919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_944919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_944919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_944919 prefixEnd_944919 := by exact prefixLift 944919
  have htrace : WordTrace (prefixWord ++ tailWord_944919) baseStart_944919 baseEnd_944919 := by
    simpa [prefixWord, tailWord_944919, baseEnd_944919] using wordTrace_append hprefix tailTrace_944919
  have hstable : (prefixWord ++ tailWord_944919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944919).length < 2 ^ (prefixWord ++ tailWord_944919).sum := by decide
  have hdescent : baseEnd_944919 < baseStart_944919 := by decide
  rcases family_descends (prefixWord ++ tailWord_944919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945015 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_945015 : Nat := 118140960795 + 945015 * 2 ^ 59
def prefixEnd_945015 : Nat := 4983230072969 + 3 ^ 40 * 945015 * 2
def baseEnd_945015 : Nat := 485246920708725358166461

theorem tailTrace_945015 : CollatzResearch.WordTrace tailWord_945015 prefixEnd_945015 485246920708725358166461 := by
  unfold tailWord_945015
  simp only [CollatzResearch.WordTrace]
  refine ⟨34467528671379525557740499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22978352447586350371826999 34467528671379525557740499)
  ·
    refine ⟨51701293007069288336610749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34467528671379525557740499 51701293007069288336610749)
    ·
      refine ⟨19387984877650983126229031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51701293007069288336610749 19387984877650983126229031)
      ·
        refine ⟨29081977316476474689343547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19387984877650983126229031 29081977316476474689343547)
        ·
          refine ⟨43622965974714712034015321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29081977316476474689343547 43622965974714712034015321)
          ·
            refine ⟨32717224481036034025511491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43622965974714712034015321 32717224481036034025511491)
            ·
              refine ⟨49075836721554051038267237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32717224481036034025511491 49075836721554051038267237)
              ·
                refine ⟨9201719385291384569675107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49075836721554051038267237 9201719385291384569675107)
                ·
                  refine ⟨13802579077937076854512661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201719385291384569675107 13802579077937076854512661)
                  ·
                    refine ⟨646995894278300477555281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13802579077937076854512661 646995894278300477555281)
                    ·
                      refine ⟨485246920708725358166461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 646995894278300477555281 485246920708725358166461)
                      ·
                        rfl

theorem cell23_945015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_945015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945015 prefixEnd_945015 := by exact prefixLift 945015
  have htrace : WordTrace (prefixWord ++ tailWord_945015) baseStart_945015 baseEnd_945015 := by
    simpa [prefixWord, tailWord_945015, baseEnd_945015] using wordTrace_append hprefix tailTrace_945015
  have hstable : (prefixWord ++ tailWord_945015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945015).length < 2 ^ (prefixWord ++ tailWord_945015).sum := by decide
  have hdescent : baseEnd_945015 < baseStart_945015 := by decide
  rcases family_descends (prefixWord ++ tailWord_945015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945018 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_945018 : Nat := 118140960795 + 945018 * 2 ^ 59
def prefixEnd_945018 : Nat := 4983230072969 + 3 ^ 40 * 945018 * 2
def baseEnd_945018 : Nat := 485248461150688846428947

theorem tailTrace_945018 : CollatzResearch.WordTrace tailWord_945018 prefixEnd_945018 485248461150688846428947 := by
  unfold tailWord_945018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616909522592164267524927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22978425393579104713399805 8616909522592164267524927)
  ·
    refine ⟨12925364283888246401287391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8616909522592164267524927 12925364283888246401287391)
    ·
      refine ⟨19388046425832369601931087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12925364283888246401287391 19388046425832369601931087)
      ·
        refine ⟨29082069638748554402896631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19388046425832369601931087 29082069638748554402896631)
        ·
          refine ⟨43623104458122831604344947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29082069638748554402896631 43623104458122831604344947)
          ·
            refine ⟨65434656687184247406517421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43623104458122831604344947 65434656687184247406517421)
            ·
              refine ⟨24537996257694092777444033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65434656687184247406517421 24537996257694092777444033)
              ·
                refine ⟨18403497193270569583083025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24537996257694092777444033 18403497193270569583083025)
                ·
                  refine ⟨13802622894952927187312269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18403497193270569583083025 13802622894952927187312269)
                  ·
                    refine ⟨5175983585607347695242101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13802622894952927187312269 5175983585607347695242101)
                    ·
                      refine ⟨485248461150688846428947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5175983585607347695242101 485248461150688846428947)
                      ·
                        rfl

theorem cell23_945018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_945018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945018 prefixEnd_945018 := by exact prefixLift 945018
  have htrace : WordTrace (prefixWord ++ tailWord_945018) baseStart_945018 baseEnd_945018 := by
    simpa [prefixWord, tailWord_945018, baseEnd_945018] using wordTrace_append hprefix tailTrace_945018
  have hstable : (prefixWord ++ tailWord_945018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945018).length < 2 ^ (prefixWord ++ tailWord_945018).sum := by decide
  have hdescent : baseEnd_945018 < baseStart_945018 := by decide
  rcases family_descends (prefixWord ++ tailWord_945018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945032 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_945032 : Nat := 118140960795 + 945032 * 2 ^ 59
def prefixEnd_945032 : Nat := 4983230072969 + 3 ^ 40 * 945032 * 2
def baseEnd_945032 : Nat := 485255649879851791653883

theorem tailTrace_945032 : CollatzResearch.WordTrace tailWord_945032 prefixEnd_945032 485255649879851791653883 := by
  unfold tailWord_945032
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234074356158968730554675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22978765808211958307406233 17234074356158968730554675)
  ·
    refine ⟨25851111534238453095832013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17234074356158968730554675 25851111534238453095832013)
    ·
      refine ⟨9694166825339419910937005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25851111534238453095832013 9694166825339419910937005)
      ·
        refine ⟨3635312559502282466601377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9694166825339419910937005 3635312559502282466601377)
        ·
          refine ⟨2726484419626711849951033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3635312559502282466601377 2726484419626711849951033)
          ·
            refine ⟨2044863314720033887463275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726484419626711849951033 2044863314720033887463275)
            ·
              refine ⟨3067294972080050831194913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044863314720033887463275 3067294972080050831194913)
              ·
                refine ⟨2300471229060038123396185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067294972080050831194913 2300471229060038123396185)
                ·
                  refine ⟨1725353421795028592547139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2300471229060038123396185 1725353421795028592547139)
                  ·
                    refine ⟨2588030132692542888820709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1725353421795028592547139 2588030132692542888820709)
                    ·
                      refine ⟨485255649879851791653883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2588030132692542888820709 485255649879851791653883)
                      ·
                        rfl

theorem cell23_945032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_945032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945032 prefixEnd_945032 := by exact prefixLift 945032
  have htrace : WordTrace (prefixWord ++ tailWord_945032) baseStart_945032 baseEnd_945032 := by
    simpa [prefixWord, tailWord_945032, baseEnd_945032] using wordTrace_append hprefix tailTrace_945032
  have hstable : (prefixWord ++ tailWord_945032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945032).length < 2 ^ (prefixWord ++ tailWord_945032).sum := by decide
  have hdescent : baseEnd_945032 < baseStart_945032 := by decide
  rcases family_descends (prefixWord ++ tailWord_945032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945035 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3]
def baseStart_945035 : Nat := 118140960795 + 945035 * 2 ^ 59
def prefixEnd_945035 : Nat := 4983230072969 + 3 ^ 40 * 945035 * 2
def baseEnd_945035 : Nat := 485257190321815279916369

theorem tailTrace_945035 : CollatzResearch.WordTrace tailWord_945035 prefixEnd_945035 485257190321815279916369 := by
  unfold tailWord_945035
  simp only [CollatzResearch.WordTrace]
  refine ⟨34468258131307068973468559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22978838754204712648979039 34468258131307068973468559)
  ·
    refine ⟨51702387196960603460202839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34468258131307068973468559 51702387196960603460202839)
    ·
      refine ⟨77553580795440905190304259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51702387196960603460202839 77553580795440905190304259)
      ·
        refine ⟨116330371193161357785456389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77553580795440905190304259 116330371193161357785456389)
        ·
          refine ⟨21811944598717754584773073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116330371193161357785456389 21811944598717754584773073)
          ·
            refine ⟨16358958449038315938579805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21811944598717754584773073 16358958449038315938579805)
            ·
              refine ⟨6134609418389368476967427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16358958449038315938579805 6134609418389368476967427)
              ·
                refine ⟨9201914127584052715451141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134609418389368476967427 9201914127584052715451141)
                ·
                  refine ⟨1725358898922009884147089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9201914127584052715451141 1725358898922009884147089)
                  ·
                    refine ⟨1294019174191507413110317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725358898922009884147089 1294019174191507413110317)
                    ·
                      refine ⟨485257190321815279916369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294019174191507413110317 485257190321815279916369)
                      ·
                        rfl

theorem cell23_945035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3].length) (baseStart_945035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945035 prefixEnd_945035 := by exact prefixLift 945035
  have htrace : WordTrace (prefixWord ++ tailWord_945035) baseStart_945035 baseEnd_945035 := by
    simpa [prefixWord, tailWord_945035, baseEnd_945035] using wordTrace_append hprefix tailTrace_945035
  have hstable : (prefixWord ++ tailWord_945035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945035).length < 2 ^ (prefixWord ++ tailWord_945035).sum := by decide
  have hdescent : baseEnd_945035 < baseStart_945035 := by decide
  rcases family_descends (prefixWord ++ tailWord_945035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945068 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_945068 : Nat := 118140960795 + 945068 * 2 ^ 59
def prefixEnd_945068 : Nat := 4983230072969 + 3 ^ 40 * 945068 * 2
def baseEnd_945068 : Nat := 161758045061137883601239

theorem tailTrace_945068 : CollatzResearch.WordTrace tailWord_945068 prefixEnd_945068 161758045061137883601239 := by
  unfold tailWord_945068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234730870093757804709929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22979641160125010406279905 17234730870093757804709929)
  ·
    refine ⟨12926048152570318353532447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17234730870093757804709929 12926048152570318353532447)
    ·
      refine ⟨19389072228855477530298671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12926048152570318353532447 19389072228855477530298671)
      ·
        refine ⟨29083608343283216295448007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19389072228855477530298671 29083608343283216295448007)
        ·
          refine ⟨43625412514924824443172011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29083608343283216295448007 43625412514924824443172011)
          ·
            refine ⟨65438118772387236664758017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43625412514924824443172011 65438118772387236664758017)
            ·
              refine ⟨49078589079290427498568513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65438118772387236664758017 49078589079290427498568513)
              ·
                refine ⟨36808941809467820623926385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49078589079290427498568513 36808941809467820623926385)
                ·
                  refine ⟨27606706357100865467944789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36808941809467820623926385 27606706357100865467944789)
                  ·
                    refine ⟨161758045061137883601239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27606706357100865467944789 161758045061137883601239)
                    ·
                      rfl

theorem cell23_945068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_945068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945068 prefixEnd_945068 := by exact prefixLift 945068
  have htrace : WordTrace (prefixWord ++ tailWord_945068) baseStart_945068 baseEnd_945068 := by
    simpa [prefixWord, tailWord_945068, baseEnd_945068] using wordTrace_append hprefix tailTrace_945068
  have hstable : (prefixWord ++ tailWord_945068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945068).length < 2 ^ (prefixWord ++ tailWord_945068).sum := by decide
  have hdescent : baseEnd_945068 < baseStart_945068 := by decide
  rcases family_descends (prefixWord ++ tailWord_945068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945105 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_945105 : Nat := 118140960795 + 945105 * 2 ^ 59
def prefixEnd_945105 : Nat := 4983230072969 + 3 ^ 40 * 945105 * 2
def baseEnd_945105 : Nat := 485293133967630006041047

theorem tailTrace_945105 : CollatzResearch.WordTrace tailWord_945105 prefixEnd_945105 485293133967630006041047 := by
  unfold tailWord_945105
  simp only [CollatzResearch.WordTrace]
  refine ⟨34470811241053470928516769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22980540827368980619011179 34470811241053470928516769)
  ·
    refine ⟨25853108430790103196387577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34470811241053470928516769 25853108430790103196387577)
    ·
      refine ⟨19389831323092577397290683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25853108430790103196387577 19389831323092577397290683)
      ·
        refine ⟨29084746984638866095936025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19389831323092577397290683 29084746984638866095936025)
        ·
          refine ⟨21813560238479149571952019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29084746984638866095936025 21813560238479149571952019)
          ·
            refine ⟨32720340357718724357928029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21813560238479149571952019 32720340357718724357928029)
            ·
              refine ⟨12270127634144521634223011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32720340357718724357928029 12270127634144521634223011)
              ·
                refine ⟨18405191451216782451334517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270127634144521634223011 18405191451216782451334517)
                ·
                  refine ⟨1725486698551573354812611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18405191451216782451334517 1725486698551573354812611)
                  ·
                    refine ⟨2588230047827360032218917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1725486698551573354812611 2588230047827360032218917)
                    ·
                      refine ⟨485293133967630006041047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2588230047827360032218917 485293133967630006041047)
                      ·
                        rfl

theorem cell23_945105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_945105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945105 prefixEnd_945105 := by exact prefixLift 945105
  have htrace : WordTrace (prefixWord ++ tailWord_945105) baseStart_945105 baseEnd_945105 := by
    simpa [prefixWord, tailWord_945105, baseEnd_945105] using wordTrace_append hprefix tailTrace_945105
  have hstable : (prefixWord ++ tailWord_945105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945105).length < 2 ^ (prefixWord ++ tailWord_945105).sum := by decide
  have hdescent : baseEnd_945105 < baseStart_945105 := by decide
  rcases family_descends (prefixWord ++ tailWord_945105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945140 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 6]
def baseStart_945140 : Nat := 118140960795 + 945140 * 2 ^ 59
def prefixEnd_945140 : Nat := 4983230072969 + 3 ^ 40 * 945140 * 2
def baseEnd_945140 : Nat := 53923456198948596567043

theorem tailTrace_945140 : CollatzResearch.WordTrace tailWord_945140 prefixEnd_945140 53923456198948596567043 := by
  unfold tailWord_945140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236043897963335953020437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22981391863951114604027249 17236043897963335953020437)
  ·
    refine ⟨807939557717031372797833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17236043897963335953020437 807939557717031372797833)
    ·
      refine ⟨605954668287773529598375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807939557717031372797833 605954668287773529598375)
      ·
        refine ⟨908932002431660294397563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605954668287773529598375 908932002431660294397563)
        ·
          refine ⟨1363398003647490441596345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908932002431660294397563 1363398003647490441596345)
          ·
            refine ⟨1022548502735617831197259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363398003647490441596345 1022548502735617831197259)
            ·
              refine ⟨1533822754103426746795889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022548502735617831197259 1533822754103426746795889)
              ·
                refine ⟨1150367065577570060096917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533822754103426746795889 1150367065577570060096917)
                ·
                  refine ⟨53923456198948596567043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1150367065577570060096917 53923456198948596567043)
                  ·
                    rfl

theorem cell23_945140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_945140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945140 prefixEnd_945140 := by exact prefixLift 945140
  have htrace : WordTrace (prefixWord ++ tailWord_945140) baseStart_945140 baseEnd_945140 := by
    simpa [prefixWord, tailWord_945140, baseEnd_945140] using wordTrace_append hprefix tailTrace_945140
  have hstable : (prefixWord ++ tailWord_945140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945140).length < 2 ^ (prefixWord ++ tailWord_945140).sum := by decide
  have hdescent : baseEnd_945140 < baseStart_945140 := by decide
  rcases family_descends (prefixWord ++ tailWord_945140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945155 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3]
def baseStart_945155 : Nat := 118140960795 + 945155 * 2 ^ 59
def prefixEnd_945155 : Nat := 4983230072969 + 3 ^ 40 * 945155 * 2
def baseEnd_945155 : Nat := 485318808000354810415817

theorem tailTrace_945155 : CollatzResearch.WordTrace tailWord_945155 prefixEnd_945155 485318808000354810415817 := by
  unfold tailWord_945155
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472634890872329467836919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22981756593914886311891279 34472634890872329467836919)
  ·
    refine ⟨51708952336308494201755379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34472634890872329467836919 51708952336308494201755379)
    ·
      refine ⟨77563428504462741302633069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51708952336308494201755379 77563428504462741302633069)
      ·
        refine ⟨29086285689173527988487401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77563428504462741302633069 29086285689173527988487401)
        ·
          refine ⟨21814714266880145991365551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29086285689173527988487401 21814714266880145991365551)
          ·
            refine ⟨32722071400320218987048327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21814714266880145991365551 32722071400320218987048327)
            ·
              refine ⟨49083107100480328480572491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32722071400320218987048327 49083107100480328480572491)
              ·
                refine ⟨73624660650720492720858737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49083107100480328480572491 73624660650720492720858737)
                ·
                  refine ⟨55218495488040369540644053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73624660650720492720858737 55218495488040369540644053)
                  ·
                    refine ⟨1294183488000946161108845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55218495488040369540644053 1294183488000946161108845)
                    ·
                      refine ⟨485318808000354810415817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294183488000946161108845 485318808000354810415817)
                      ·
                        rfl

theorem cell23_945155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_945155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945155 prefixEnd_945155 := by exact prefixLift 945155
  have htrace : WordTrace (prefixWord ++ tailWord_945155) baseStart_945155 baseEnd_945155 := by
    simpa [prefixWord, tailWord_945155, baseEnd_945155] using wordTrace_append hprefix tailTrace_945155
  have hstable : (prefixWord ++ tailWord_945155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945155).length < 2 ^ (prefixWord ++ tailWord_945155).sum := by decide
  have hdescent : baseEnd_945155 < baseStart_945155 := by decide
  rcases family_descends (prefixWord ++ tailWord_945155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945166 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_945166 : Nat := 118140960795 + 945166 * 2 ^ 59
def prefixEnd_945166 : Nat := 4983230072969 + 3 ^ 40 * 945166 * 2
def baseEnd_945166 : Nat := 161774818762518089126089

theorem tailTrace_945166 : CollatzResearch.WordTrace tailWord_945166 prefixEnd_945166 161774818762518089126089 := by
  unfold tailWord_945166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309129511729059793310919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22982024062554985564324901 4309129511729059793310919)
  ·
    refine ⟨6463694267593589689966379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4309129511729059793310919 6463694267593589689966379)
    ·
      refine ⟨9695541401390384534949569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463694267593589689966379 9695541401390384534949569)
      ·
        refine ⟨7271656051042788401212177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9695541401390384534949569 7271656051042788401212177)
        ·
          refine ⟨5453742038282091300909133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7271656051042788401212177 5453742038282091300909133)
          ·
            refine ⟨2045153264355784237840925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5453742038282091300909133 2045153264355784237840925)
            ·
              refine ⟨766932474133419089190347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045153264355784237840925 766932474133419089190347)
              ·
                refine ⟨1150398711200128633785521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766932474133419089190347 1150398711200128633785521)
                ·
                  refine ⟨862799033400096475339141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150398711200128633785521 862799033400096475339141)
                  ·
                    refine ⟨161774818762518089126089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862799033400096475339141 161774818762518089126089)
                    ·
                      rfl

theorem cell23_945166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_945166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945166 prefixEnd_945166 := by exact prefixLift 945166
  have htrace : WordTrace (prefixWord ++ tailWord_945166) baseStart_945166 baseEnd_945166 := by
    simpa [prefixWord, tailWord_945166, baseEnd_945166] using wordTrace_append hprefix tailTrace_945166
  have hstable : (prefixWord ++ tailWord_945166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945166).length < 2 ^ (prefixWord ++ tailWord_945166).sum := by decide
  have hdescent : baseEnd_945166 < baseStart_945166 := by decide
  rcases family_descends (prefixWord ++ tailWord_945166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945206 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_945206 : Nat := 118140960795 + 945206 * 2 ^ 59
def prefixEnd_945206 : Nat := 4983230072969 + 3 ^ 40 * 945206 * 2
def baseEnd_945206 : Nat := 485344995513734110878083

theorem tailTrace_945206 : CollatzResearch.WordTrace tailWord_945206 prefixEnd_945206 485344995513734110878083 := by
  unfold tailWord_945206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154655938355472823621467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22982996675791710118628981 2154655938355472823621467)
  ·
    refine ⟨3231983907533209235432201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154655938355472823621467 3231983907533209235432201)
    ·
      refine ⟨2423987930649906926574151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3231983907533209235432201 2423987930649906926574151)
      ·
        refine ⟨3635981895974860389861227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423987930649906926574151 3635981895974860389861227)
        ·
          refine ⟨5453972843962290584791841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3635981895974860389861227 5453972843962290584791841)
          ·
            refine ⟨4090479632971717938593881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5453972843962290584791841 4090479632971717938593881)
            ·
              refine ⟨3067859724728788453945411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090479632971717938593881 3067859724728788453945411)
              ·
                refine ⟨4601789587093182680918117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067859724728788453945411 4601789587093182680918117)
                ·
                  refine ⟨862835547579971752672147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4601789587093182680918117 862835547579971752672147)
                  ·
                    refine ⟨1294253321369957629008221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 862835547579971752672147 1294253321369957629008221)
                    ·
                      refine ⟨485344995513734110878083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294253321369957629008221 485344995513734110878083)
                      ·
                        rfl

theorem cell23_945206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_945206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945206 prefixEnd_945206 := by exact prefixLift 945206
  have htrace : WordTrace (prefixWord ++ tailWord_945206) baseStart_945206 baseEnd_945206 := by
    simpa [prefixWord, tailWord_945206, baseEnd_945206] using wordTrace_append hprefix tailTrace_945206
  have hstable : (prefixWord ++ tailWord_945206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945206).length < 2 ^ (prefixWord ++ tailWord_945206).sum := by decide
  have hdescent : baseEnd_945206 < baseStart_945206 := by decide
  rcases family_descends (prefixWord ++ tailWord_945206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945215 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_945215 : Nat := 118140960795 + 945215 * 2 ^ 59
def prefixEnd_945215 : Nat := 4983230072969 + 3 ^ 40 * 945215 * 2
def baseEnd_945215 : Nat := 485349616839624575665541

theorem tailTrace_945215 : CollatzResearch.WordTrace tailWord_945215 prefixEnd_945215 485349616839624575665541 := by
  unfold tailWord_945215
  simp only [CollatzResearch.WordTrace]
  refine ⟨34474823270654959715021099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22983215513769973143347399 34474823270654959715021099)
  ·
    refine ⟨51712234905982439572531649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34474823270654959715021099 51712234905982439572531649)
    ·
      refine ⟨38784176179486829679398737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51712234905982439572531649 38784176179486829679398737)
      ·
        refine ⟨29088132134615122259549053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38784176179486829679398737 29088132134615122259549053)
        ·
          refine ⟨10908049550480670847330895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29088132134615122259549053 10908049550480670847330895)
          ·
            refine ⟨16362074325721006270996343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10908049550480670847330895 16362074325721006270996343)
            ·
              refine ⟨24543111488581509406494515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16362074325721006270996343 24543111488581509406494515)
              ·
                refine ⟨36814667232872264109741773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24543111488581509406494515 36814667232872264109741773)
                ·
                  refine ⟨13805500212327099041153165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36814667232872264109741773 13805500212327099041153165)
                  ·
                    refine ⟨5177062579622662140432437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13805500212327099041153165 5177062579622662140432437)
                    ·
                      refine ⟨485349616839624575665541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5177062579622662140432437 485349616839624575665541)
                      ·
                        rfl

theorem cell23_945215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_945215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945215 prefixEnd_945215 := by exact prefixLift 945215
  have htrace : WordTrace (prefixWord ++ tailWord_945215) baseStart_945215 baseEnd_945215 := by
    simpa [prefixWord, tailWord_945215, baseEnd_945215] using wordTrace_append hprefix tailTrace_945215
  have hstable : (prefixWord ++ tailWord_945215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945215).length < 2 ^ (prefixWord ++ tailWord_945215).sum := by decide
  have hdescent : baseEnd_945215 < baseStart_945215 := by decide
  rcases family_descends (prefixWord ++ tailWord_945215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945223 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_945223 : Nat := 118140960795 + 945223 * 2 ^ 59
def prefixEnd_945223 : Nat := 4983230072969 + 3 ^ 40 * 945223 * 2
def baseEnd_945223 : Nat := 485353724684860544365505

theorem tailTrace_945223 : CollatzResearch.WordTrace tailWord_945223 prefixEnd_945223 485353724684860544365505 := by
  unfold tailWord_945223
  simp only [CollatzResearch.WordTrace]
  refine ⟨34475115054625977081312323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22983410036417318054208215 34475115054625977081312323)
  ·
    refine ⟨51712672581938965621968485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34475115054625977081312323 51712672581938965621968485)
    ·
      refine ⟨9696126109113556054119091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51712672581938965621968485 9696126109113556054119091)
      ·
        refine ⟨14544189163670334081178637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9696126109113556054119091 14544189163670334081178637)
        ·
          refine ⟨5454070936376375280441989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14544189163670334081178637 5454070936376375280441989)
          ·
            refine ⟨1022638300570570365082873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5454070936376375280441989 1022638300570570365082873)
            ·
              refine ⟨766978725427927773812155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022638300570570365082873 766978725427927773812155)
              ·
                refine ⟨1150468088141891660718233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766978725427927773812155 1150468088141891660718233)
                ·
                  refine ⟨862851066106418745538675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150468088141891660718233 862851066106418745538675)
                  ·
                    refine ⟨1294276599159628118308013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 862851066106418745538675 1294276599159628118308013)
                    ·
                      refine ⟨485353724684860544365505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294276599159628118308013 485353724684860544365505)
                      ·
                        rfl

theorem cell23_945223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_945223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945223 prefixEnd_945223 := by exact prefixLift 945223
  have htrace : WordTrace (prefixWord ++ tailWord_945223) baseStart_945223 baseEnd_945223 := by
    simpa [prefixWord, tailWord_945223, baseEnd_945223] using wordTrace_append hprefix tailTrace_945223
  have hstable : (prefixWord ++ tailWord_945223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945223).length < 2 ^ (prefixWord ++ tailWord_945223).sum := by decide
  have hdescent : baseEnd_945223 < baseStart_945223 := by decide
  rcases family_descends (prefixWord ++ tailWord_945223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945250 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_945250 : Nat := 118140960795 + 945250 * 2 ^ 59
def prefixEnd_945250 : Nat := 4983230072969 + 3 ^ 40 * 945250 * 2
def baseEnd_945250 : Nat := 485367588662531938727881

theorem tailTrace_945250 : CollatzResearch.WordTrace tailWord_945250 prefixEnd_945250 485367588662531938727881 := by
  unfold tailWord_945250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619024956382040173136301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22984066550352107128363469 8619024956382040173136301)
  ·
    refine ⟨3232134358643265064926113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8619024956382040173136301 3232134358643265064926113)
    ·
      refine ⟨2424100768982448798694585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232134358643265064926113 2424100768982448798694585)
      ·
        refine ⟨1818075576736836599020939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424100768982448798694585 1818075576736836599020939)
        ·
          refine ⟨2727113365105254898531409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818075576736836599020939 2727113365105254898531409)
          ·
            refine ⟨2045335023828941173898557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727113365105254898531409 2045335023828941173898557)
            ·
              refine ⟨767000633935852940211959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045335023828941173898557 767000633935852940211959)
              ·
                refine ⟨1150500950903779410317939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767000633935852940211959 1150500950903779410317939)
                ·
                  refine ⟨1725751426355669115476909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150500950903779410317939 1725751426355669115476909)
                  ·
                    refine ⟨647156784883375918303841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725751426355669115476909 647156784883375918303841)
                    ·
                      refine ⟨485367588662531938727881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647156784883375918303841 485367588662531938727881)
                      ·
                        rfl

theorem cell23_945250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_945250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945250 prefixEnd_945250 := by exact prefixLift 945250
  have htrace : WordTrace (prefixWord ++ tailWord_945250) baseStart_945250 baseEnd_945250 := by
    simpa [prefixWord, tailWord_945250, baseEnd_945250] using wordTrace_append hprefix tailTrace_945250
  have hstable : (prefixWord ++ tailWord_945250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945250).length < 2 ^ (prefixWord ++ tailWord_945250).sum := by decide
  have hdescent : baseEnd_945250 < baseStart_945250 := by decide
  rcases family_descends (prefixWord ++ tailWord_945250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945373 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_945373 : Nat := 118140960795 + 945373 * 2 ^ 59
def prefixEnd_945373 : Nat := 4983230072969 + 3 ^ 40 * 945373 * 2
def baseEnd_945373 : Nat := 485430746783034957489815

theorem tailTrace_945373 : CollatzResearch.WordTrace tailWord_945373 prefixEnd_945373 485430746783034957489815 := by
  unfold tailWord_945373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34480586004082552699272773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22987057336055035132848515 34480586004082552699272773)
  ·
    refine ⟨6465109875765478631113645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34480586004082552699272773 6465109875765478631113645)
    ·
      refine ⟨2424416203412054486667617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6465109875765478631113645 2424416203412054486667617)
      ·
        refine ⟨1818312152559040865000713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424416203412054486667617 1818312152559040865000713)
        ·
          refine ⟨1363734114419280648750535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818312152559040865000713 1363734114419280648750535)
          ·
            refine ⟨2045601171628920973125803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363734114419280648750535 2045601171628920973125803)
            ·
              refine ⟨3068401757443381459688705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045601171628920973125803 3068401757443381459688705)
              ·
                refine ⟨2301301318082536094766529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068401757443381459688705 2301301318082536094766529)
                ·
                  refine ⟨1725975988561902071074897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301301318082536094766529 1725975988561902071074897)
                  ·
                    refine ⟨1294481991421426553306173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725975988561902071074897 1294481991421426553306173)
                    ·
                      refine ⟨485430746783034957489815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294481991421426553306173 485430746783034957489815)
                      ·
                        rfl

theorem cell23_945373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_945373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945373 prefixEnd_945373 := by exact prefixLift 945373
  have htrace : WordTrace (prefixWord ++ tailWord_945373) baseStart_945373 baseEnd_945373 := by
    simpa [prefixWord, tailWord_945373, baseEnd_945373] using wordTrace_append hprefix tailTrace_945373
  have hstable : (prefixWord ++ tailWord_945373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945373).length < 2 ^ (prefixWord ++ tailWord_945373).sum := by decide
  have hdescent : baseEnd_945373 < baseStart_945373 := by decide
  rcases family_descends (prefixWord ++ tailWord_945373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945392 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_945392 : Nat := 118140960795 + 945392 * 2 ^ 59
def prefixEnd_945392 : Nat := 4983230072969 + 3 ^ 40 * 945392 * 2
def baseEnd_945392 : Nat := 485440502915470383152227

theorem tailTrace_945392 : CollatzResearch.WordTrace tailWord_945392 prefixEnd_945392 485440502915470383152227 := by
  unfold tailWord_945392
  simp only [CollatzResearch.WordTrace]
  refine ⟨17240639495506859472107215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22987519327342479296142953 17240639495506859472107215)
  ·
    refine ⟨25860959243260289208160823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17240639495506859472107215 25860959243260289208160823)
    ·
      refine ⟨38791438864890433812241235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25860959243260289208160823 38791438864890433812241235)
      ·
        refine ⟨58187158297335650718361853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38791438864890433812241235 58187158297335650718361853)
        ·
          refine ⟨21820184361500869019385695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58187158297335650718361853 21820184361500869019385695)
          ·
            refine ⟨32730276542251303529078543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21820184361500869019385695 32730276542251303529078543)
            ·
              refine ⟨49095414813376955293617815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32730276542251303529078543 49095414813376955293617815)
              ·
                refine ⟨73643122220065432940426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49095414813376955293617815 73643122220065432940426723)
                ·
                  refine ⟨110464683330098149410640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73643122220065432940426723 110464683330098149410640085)
                  ·
                    refine ⟨2589016015549175376811877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 110464683330098149410640085 2589016015549175376811877)
                    ·
                      refine ⟨485440502915470383152227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2589016015549175376811877 485440502915470383152227)
                      ·
                        rfl

theorem cell23_945392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_945392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945392 prefixEnd_945392 := by exact prefixLift 945392
  have htrace : WordTrace (prefixWord ++ tailWord_945392) baseStart_945392 baseEnd_945392 := by
    simpa [prefixWord, tailWord_945392, baseEnd_945392] using wordTrace_append hprefix tailTrace_945392
  have hstable : (prefixWord ++ tailWord_945392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945392).length < 2 ^ (prefixWord ++ tailWord_945392).sum := by decide
  have hdescent : baseEnd_945392 < baseStart_945392 := by decide
  rcases family_descends (prefixWord ++ tailWord_945392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945406 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_945406 : Nat := 118140960795 + 945406 * 2 ^ 59
def prefixEnd_945406 : Nat := 4983230072969 + 3 ^ 40 * 945406 * 2
def baseEnd_945406 : Nat := 161815897214877776125721

theorem tailTrace_945406 : CollatzResearch.WordTrace tailWord_945406 prefixEnd_945406 161815897214877776125721 := by
  unfold tailWord_945406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310223701620374916903009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22987859741975332890149381 4310223701620374916903009)
  ·
    refine ⟨3232667776215281187677257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4310223701620374916903009 3232667776215281187677257)
    ·
      refine ⟨2424500832161460890757943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232667776215281187677257 2424500832161460890757943)
      ·
        refine ⟨3636751248242191336136915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424500832161460890757943 3636751248242191336136915)
        ·
          refine ⟨5455126872363287004205373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636751248242191336136915 5455126872363287004205373)
          ·
            refine ⟨2045672577136232626577015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5455126872363287004205373 2045672577136232626577015)
            ·
              refine ⟨3068508865704348939865523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045672577136232626577015 3068508865704348939865523)
              ·
                refine ⟨4602763298556523409798285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068508865704348939865523 4602763298556523409798285)
                ·
                  refine ⟨1726036236958696278674357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4602763298556523409798285 1726036236958696278674357)
                  ·
                    refine ⟨161815897214877776125721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1726036236958696278674357 161815897214877776125721)
                    ·
                      rfl

theorem cell23_945406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_945406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945406 prefixEnd_945406 := by exact prefixLift 945406
  have htrace : WordTrace (prefixWord ++ tailWord_945406) baseStart_945406 baseEnd_945406 := by
    simpa [prefixWord, tailWord_945406, baseEnd_945406] using wordTrace_append hprefix tailTrace_945406
  have hstable : (prefixWord ++ tailWord_945406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945406).length < 2 ^ (prefixWord ++ tailWord_945406).sum := by decide
  have hdescent : baseEnd_945406 < baseStart_945406 := by decide
  rcases family_descends (prefixWord ++ tailWord_945406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945419 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 1, 6]
def baseStart_945419 : Nat := 118140960795 + 945419 * 2 ^ 59
def prefixEnd_945419 : Nat := 4983230072969 + 3 ^ 40 * 945419 * 2
def baseEnd_945419 : Nat := 161818122297713925838201

theorem tailTrace_945419 : CollatzResearch.WordTrace tailWord_945419 prefixEnd_945419 161818122297713925838201 := by
  unfold tailWord_945419
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482263761915902555447311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22988175841277268370298207 34482263761915902555447311)
  ·
    refine ⟨51723395642873853833170967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34482263761915902555447311 51723395642873853833170967)
    ·
      refine ⟨77585093464310780749756451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51723395642873853833170967 77585093464310780749756451)
      ·
        refine ⟨116377640196466171124634677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77585093464310780749756451 116377640196466171124634677)
        ·
          refine ⟨10910403768418703542934501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116377640196466171124634677 10910403768418703542934501)
          ·
            refine ⟨2045700706578506914300219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10910403768418703542934501 2045700706578506914300219)
            ·
              refine ⟨3068551059867760371450329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045700706578506914300219 3068551059867760371450329)
              ·
                refine ⟨2301413294900820278587747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068551059867760371450329 2301413294900820278587747)
                ·
                  refine ⟨3452119942351230417881621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301413294900820278587747 3452119942351230417881621)
                  ·
                    refine ⟨161818122297713925838201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3452119942351230417881621 161818122297713925838201)
                    ·
                      rfl

theorem cell23_945419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 6].length) (baseStart_945419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945419 prefixEnd_945419 := by exact prefixLift 945419
  have htrace : WordTrace (prefixWord ++ tailWord_945419) baseStart_945419 baseEnd_945419 := by
    simpa [prefixWord, tailWord_945419, baseEnd_945419] using wordTrace_append hprefix tailTrace_945419
  have hstable : (prefixWord ++ tailWord_945419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945419).length < 2 ^ (prefixWord ++ tailWord_945419).sum := by decide
  have hdescent : baseEnd_945419 < baseStart_945419 := by decide
  rcases family_descends (prefixWord ++ tailWord_945419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945432 : List Nat := [2, 1, 2, 3, 1, 14]
def baseStart_945432 : Nat := 118140960795 + 945432 * 2 ^ 59
def prefixEnd_945432 : Nat := 4983230072969 + 3 ^ 40 * 945432 * 2
def baseEnd_945432 : Nat := 1997782066426544142601

theorem tailTrace_945432 : CollatzResearch.WordTrace tailWord_945432 prefixEnd_945432 1997782066426544142601 := by
  unfold tailWord_945432
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241368955434402887835275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22988491940579203850447033 17241368955434402887835275)
  ·
    refine ⟨25862053433151604331752913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17241368955434402887835275 25862053433151604331752913)
    ·
      refine ⟨19396540074863703248814685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25862053433151604331752913 19396540074863703248814685)
      ·
        refine ⟨7273702528073888718305507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19396540074863703248814685 7273702528073888718305507)
        ·
          refine ⟨10910553792110833077458261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7273702528073888718305507 10910553792110833077458261)
          ·
            refine ⟨1997782066426544142601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 10910553792110833077458261 1997782066426544142601)
            ·
              rfl

theorem cell23_945432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 14].length) (baseStart_945432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945432 prefixEnd_945432 := by exact prefixLift 945432
  have htrace : WordTrace (prefixWord ++ tailWord_945432) baseStart_945432 baseEnd_945432 := by
    simpa [prefixWord, tailWord_945432, baseEnd_945432] using wordTrace_append hprefix tailTrace_945432
  have hstable : (prefixWord ++ tailWord_945432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945432).length < 2 ^ (prefixWord ++ tailWord_945432).sum := by decide
  have hdescent : baseEnd_945432 < baseStart_945432 := by decide
  rcases family_descends (prefixWord ++ tailWord_945432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945436 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_945436 : Nat := 118140960795 + 945436 * 2 ^ 59
def prefixEnd_945436 : Nat := 4983230072969 + 3 ^ 40 * 945436 * 2
def baseEnd_945436 : Nat := 161821032021422737000675

theorem tailTrace_945436 : CollatzResearch.WordTrace tailWord_945436 prefixEnd_945436 161821032021422737000675 := by
  unfold tailWord_945436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241441901427157229408081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22988589201902876305877441 17241441901427157229408081)
  ·
    refine ⟨12931081426070367922056061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17241441901427157229408081 12931081426070367922056061)
    ·
      refine ⟨4849155534776387970771023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12931081426070367922056061 4849155534776387970771023)
      ·
        refine ⟨7273733302164581956156535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849155534776387970771023 7273733302164581956156535)
        ·
          refine ⟨10910599953246872934234803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7273733302164581956156535 10910599953246872934234803)
          ·
            refine ⟨16365899929870309401352205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910599953246872934234803 16365899929870309401352205)
            ·
              refine ⟨6137212473701366025507077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365899929870309401352205 6137212473701366025507077)
              ·
                refine ⟨1150727338819006129782577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6137212473701366025507077 1150727338819006129782577)
                ·
                  refine ⟨863045504114254597336933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150727338819006129782577 863045504114254597336933)
                  ·
                    refine ⟨161821032021422737000675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863045504114254597336933 161821032021422737000675)
                    ·
                      rfl

theorem cell23_945436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_945436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945436 prefixEnd_945436 := by exact prefixLift 945436
  have htrace : WordTrace (prefixWord ++ tailWord_945436) baseStart_945436 baseEnd_945436 := by
    simpa [prefixWord, tailWord_945436, baseEnd_945436] using wordTrace_append hprefix tailTrace_945436
  have hstable : (prefixWord ++ tailWord_945436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945436).length < 2 ^ (prefixWord ++ tailWord_945436).sum := by decide
  have hdescent : baseEnd_945436 < baseStart_945436 := by decide
  rcases family_descends (prefixWord ++ tailWord_945436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945437 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_945437 : Nat := 118140960795 + 945437 * 2 ^ 59
def prefixEnd_945437 : Nat := 4983230072969 + 3 ^ 40 * 945437 * 2
def baseEnd_945437 : Nat := 485463609544922707089521

theorem tailTrace_945437 : CollatzResearch.WordTrace tailWord_945437 prefixEnd_945437 485463609544922707089521 := by
  unfold tailWord_945437
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482920275850691629602565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22988613517233794419735043 34482920275850691629602565)
  ·
    refine ⟨6465547551722004680550481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34482920275850691629602565 6465547551722004680550481)
    ·
      refine ⟨4849160663791503510412861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6465547551722004680550481 4849160663791503510412861)
      ·
        refine ⟨1818435248921813816404823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4849160663791503510412861 1818435248921813816404823)
        ·
          refine ⟨2727652873382720724607235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818435248921813816404823 2727652873382720724607235)
          ·
            refine ⟨4091479310074081086910853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727652873382720724607235 4091479310074081086910853)
            ·
              refine ⟨767152370638890203795785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4091479310074081086910853 767152370638890203795785)
              ·
                refine ⟨575364277979167652846839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767152370638890203795785 575364277979167652846839)
                ·
                  refine ⟨863046416968751479270259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575364277979167652846839 863046416968751479270259)
                  ·
                    refine ⟨1294569625453127218905389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863046416968751479270259 1294569625453127218905389)
                    ·
                      refine ⟨485463609544922707089521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294569625453127218905389 485463609544922707089521)
                      ·
                        rfl

theorem cell23_945437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_945437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945437 prefixEnd_945437 := by exact prefixLift 945437
  have htrace : WordTrace (prefixWord ++ tailWord_945437) baseStart_945437 baseEnd_945437 := by
    simpa [prefixWord, tailWord_945437, baseEnd_945437] using wordTrace_append hprefix tailTrace_945437
  have hstable : (prefixWord ++ tailWord_945437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945437).length < 2 ^ (prefixWord ++ tailWord_945437).sum := by decide
  have hdescent : baseEnd_945437 < baseStart_945437 := by decide
  rcases family_descends (prefixWord ++ tailWord_945437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945453 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_945453 : Nat := 118140960795 + 945453 * 2 ^ 59
def prefixEnd_945453 : Nat := 4983230072969 + 3 ^ 40 * 945453 * 2
def baseEnd_945453 : Nat := 161823941745131548163149

theorem tailTrace_945453 : CollatzResearch.WordTrace tailWord_945453 prefixEnd_945453 161823941745131548163149 := by
  unfold tailWord_945453
  simp only [CollatzResearch.WordTrace]
  refine ⟨34483503843792726362185013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22989002562528484241456675 34483503843792726362185013)
  ·
    refine ⟨3232828485355568096454845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34483503843792726362185013 3232828485355568096454845)
    ·
      refine ⟨1212310682008338036170567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3232828485355568096454845 1212310682008338036170567)
      ·
        refine ⟨1818466023012507054255851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212310682008338036170567 1818466023012507054255851)
        ·
          refine ⟨2727699034518760581383777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818466023012507054255851 2727699034518760581383777)
          ·
            refine ⟨2045774275889070436037833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727699034518760581383777 2045774275889070436037833)
            ·
              refine ⟨1534330706916802827028375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045774275889070436037833 1534330706916802827028375)
              ·
                refine ⟨2301496060375204240542563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534330706916802827028375 2301496060375204240542563)
                ·
                  refine ⟨3452244090562806360813845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301496060375204240542563 3452244090562806360813845)
                  ·
                    refine ⟨161823941745131548163149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3452244090562806360813845 161823941745131548163149)
                    ·
                      rfl

theorem cell23_945453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_945453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945453 prefixEnd_945453 := by exact prefixLift 945453
  have htrace : WordTrace (prefixWord ++ tailWord_945453) baseStart_945453 baseEnd_945453 := by
    simpa [prefixWord, tailWord_945453, baseEnd_945453] using wordTrace_append hprefix tailTrace_945453
  have hstable : (prefixWord ++ tailWord_945453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945453).length < 2 ^ (prefixWord ++ tailWord_945453).sum := by decide
  have hdescent : baseEnd_945453 < baseStart_945453 := by decide
  rcases family_descends (prefixWord ++ tailWord_945453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945460 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_945460 : Nat := 118140960795 + 945460 * 2 ^ 59
def prefixEnd_945460 : Nat := 4983230072969 + 3 ^ 40 * 945460 * 2
def baseEnd_945460 : Nat := 485475419599976117101915

theorem tailTrace_945460 : CollatzResearch.WordTrace tailWord_945460 prefixEnd_945460 485475419599976117101915 := by
  unfold tailWord_945460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241879577383683278844917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22989172769844911038459889 17241879577383683278844917)
  ·
    refine ⟨1616426210379720307391711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17241879577383683278844917 1616426210379720307391711)
    ·
      refine ⟨2424639315569580461087567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616426210379720307391711 2424639315569580461087567)
      ·
        refine ⟨3636958973354370691631351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424639315569580461087567 3636958973354370691631351)
        ·
          refine ⟨5455438460031556037447027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636958973354370691631351 5455438460031556037447027)
          ·
            refine ⟨8183157690047334056170541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455438460031556037447027 8183157690047334056170541)
            ·
              refine ⟨3068684133767750271063953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8183157690047334056170541 3068684133767750271063953)
              ·
                refine ⟨2301513100325812703297965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068684133767750271063953 2301513100325812703297965)
                ·
                  refine ⟨863067412622179763736737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2301513100325812703297965 863067412622179763736737)
                  ·
                    refine ⟨647300559466634822802553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863067412622179763736737 647300559466634822802553)
                    ·
                      refine ⟨485475419599976117101915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647300559466634822802553 485475419599976117101915)
                      ·
                        rfl

theorem cell23_945460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_945460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945460 prefixEnd_945460 := by exact prefixLift 945460
  have htrace : WordTrace (prefixWord ++ tailWord_945460) baseStart_945460 baseEnd_945460 := by
    simpa [prefixWord, tailWord_945460, baseEnd_945460] using wordTrace_append hprefix tailTrace_945460
  have hstable : (prefixWord ++ tailWord_945460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945460).length < 2 ^ (prefixWord ++ tailWord_945460).sum := by decide
  have hdescent : baseEnd_945460 < baseStart_945460 := by decide
  rcases family_descends (prefixWord ++ tailWord_945460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945493 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_945493 : Nat := 118140960795 + 945493 * 2 ^ 59
def prefixEnd_945493 : Nat := 4983230072969 + 3 ^ 40 * 945493 * 2
def baseEnd_945493 : Nat := 485492364461574487989263

theorem tailTrace_945493 : CollatzResearch.WordTrace tailWord_945493 prefixEnd_945493 485492364461574487989263 := by
  unfold tailWord_945493
  simp only [CollatzResearch.WordTrace]
  refine ⟨34484962763647813193641133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22989975175765208795760755 34484962763647813193641133)
  ·
    refine ⟨12931861036367929947615425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34484962763647813193641133 12931861036367929947615425)
    ·
      refine ⟨9698895777275947460711569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12931861036367929947615425 9698895777275947460711569)
      ·
        refine ⟨7274171832956960595533677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9698895777275947460711569 7274171832956960595533677)
        ·
          refine ⟨2727814437358860223325129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7274171832956960595533677 2727814437358860223325129)
          ·
            refine ⟨2045860828019145167493847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727814437358860223325129 2045860828019145167493847)
            ·
              refine ⟨3068791242028717751240771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045860828019145167493847 3068791242028717751240771)
              ·
                refine ⟨4603186863043076626861157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068791242028717751240771 4603186863043076626861157)
                ·
                  refine ⟨863097536820576867536467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4603186863043076626861157 863097536820576867536467)
                  ·
                    refine ⟨1294646305230865301304701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863097536820576867536467 1294646305230865301304701)
                    ·
                      refine ⟨485492364461574487989263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294646305230865301304701 485492364461574487989263)
                      ·
                        rfl

theorem cell23_945493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_945493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945493 prefixEnd_945493 := by exact prefixLift 945493
  have htrace : WordTrace (prefixWord ++ tailWord_945493) baseStart_945493 baseEnd_945493 := by
    simpa [prefixWord, tailWord_945493, baseEnd_945493] using wordTrace_append hprefix tailTrace_945493
  have hstable : (prefixWord ++ tailWord_945493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945493).length < 2 ^ (prefixWord ++ tailWord_945493).sum := by decide
  have hdescent : baseEnd_945493 < baseStart_945493 := by decide
  rcases family_descends (prefixWord ++ tailWord_945493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945509 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_945509 : Nat := 118140960795 + 945509 * 2 ^ 59
def prefixEnd_945509 : Nat := 4983230072969 + 3 ^ 40 * 945509 * 2
def baseEnd_945509 : Nat := 161833526717348808463063

theorem tailTrace_945509 : CollatzResearch.WordTrace tailWord_945509 prefixEnd_945509 161833526717348808463063 := by
  unfold tailWord_945509
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485546331589847926223581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22990364221059898617482387 34485546331589847926223581)
  ·
    refine ⟨12932079874346192972333843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34485546331589847926223581 12932079874346192972333843)
    ·
      refine ⟨19398119811519289458500765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12932079874346192972333843 19398119811519289458500765)
      ·
        refine ⟨7274294929319733546937787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19398119811519289458500765 7274294929319733546937787)
        ·
          refine ⟨10911442393979600320406681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274294929319733546937787 10911442393979600320406681)
          ·
            refine ⟨8183581795484700240305011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911442393979600320406681 8183581795484700240305011)
            ·
              refine ⟨12275372693227050360457517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183581795484700240305011 12275372693227050360457517)
              ·
                refine ⟨4603264759960143885171569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12275372693227050360457517 4603264759960143885171569)
                ·
                  refine ⟨3452448569970107913878677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603264759960143885171569 3452448569970107913878677)
                  ·
                    refine ⟨161833526717348808463063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3452448569970107913878677 161833526717348808463063)
                    ·
                      rfl

theorem cell23_945509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_945509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945509 prefixEnd_945509 := by exact prefixLift 945509
  have htrace : WordTrace (prefixWord ++ tailWord_945509) baseStart_945509 baseEnd_945509 := by
    simpa [prefixWord, tailWord_945509, baseEnd_945509] using wordTrace_append hprefix tailTrace_945509
  have hstable : (prefixWord ++ tailWord_945509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945509).length < 2 ^ (prefixWord ++ tailWord_945509).sum := by decide
  have hdescent : baseEnd_945509 < baseStart_945509 := by decide
  rcases family_descends (prefixWord ++ tailWord_945509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945519 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_945519 : Nat := 118140960795 + 945519 * 2 ^ 59
def prefixEnd_945519 : Nat := 4983230072969 + 3 ^ 40 * 945519 * 2
def baseEnd_945519 : Nat := 485505714958591386264143

theorem tailTrace_945519 : CollatzResearch.WordTrace tailWord_945519 prefixEnd_945519 485505714958591386264143 := by
  unfold tailWord_945519
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485911061553619634087611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22990607374369079756058407 34485911061553619634087611)
  ·
    refine ⟨51728866592330429451131417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34485911061553619634087611 51728866592330429451131417)
    ·
      refine ⟨38796649944247822088348563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51728866592330429451131417 38796649944247822088348563)
      ·
        refine ⟨58194974916371733132522845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38796649944247822088348563 58194974916371733132522845)
        ·
          refine ⟨21823115593639399924696067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58194974916371733132522845 21823115593639399924696067)
          ·
            refine ⟨32734673390459099887044101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21823115593639399924696067 32734673390459099887044101)
            ·
              refine ⟨6137751260711081228820769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32734673390459099887044101 6137751260711081228820769)
              ·
                refine ⟨4603313445533310921615577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137751260711081228820769 4603313445533310921615577)
                ·
                  refine ⟨3452485084149983191211683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603313445533310921615577 3452485084149983191211683)
                  ·
                    refine ⟨5178727626224974786817525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3452485084149983191211683 5178727626224974786817525)
                    ·
                      refine ⟨485505714958591386264143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5178727626224974786817525 485505714958591386264143)
                      ·
                        rfl

theorem cell23_945519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_945519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945519 prefixEnd_945519 := by exact prefixLift 945519
  have htrace : WordTrace (prefixWord ++ tailWord_945519) baseStart_945519 baseEnd_945519 := by
    simpa [prefixWord, tailWord_945519, baseEnd_945519] using wordTrace_append hprefix tailTrace_945519
  have hstable : (prefixWord ++ tailWord_945519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945519).length < 2 ^ (prefixWord ++ tailWord_945519).sum := by decide
  have hdescent : baseEnd_945519 < baseStart_945519 := by decide
  rcases family_descends (prefixWord ++ tailWord_945519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945529 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_945529 : Nat := 118140960795 + 945529 * 2 ^ 59
def prefixEnd_945529 : Nat := 4983230072969 + 3 ^ 40 * 945529 * 2
def baseEnd_945529 : Nat := 485510849765136347139097

theorem tailTrace_945529 : CollatzResearch.WordTrace tailWord_945529 prefixEnd_945529 485510849765136347139097 := by
  unfold tailWord_945529
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486275791517391341951641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22990850527678260894634427 34486275791517391341951641)
  ·
    refine ⟨25864706843638043506463731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34486275791517391341951641 25864706843638043506463731)
    ·
      refine ⟨38797060265457065259695597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864706843638043506463731 38797060265457065259695597)
      ·
        refine ⟨14548897599546399472385849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38797060265457065259695597 14548897599546399472385849)
        ·
          refine ⟨10911673199659799604289387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14548897599546399472385849 10911673199659799604289387)
          ·
            refine ⟨16367509799489699406434081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10911673199659799604289387 16367509799489699406434081)
            ·
              refine ⟨12275632349617274554825561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16367509799489699406434081 12275632349617274554825561)
              ·
                refine ⟨9206724262212955916119171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12275632349617274554825561 9206724262212955916119171)
                ·
                  refine ⟨13810086393319433874178757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206724262212955916119171 13810086393319433874178757)
                  ·
                    refine ⟨2589391198747393851408517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13810086393319433874178757 2589391198747393851408517)
                    ·
                      refine ⟨485510849765136347139097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2589391198747393851408517 485510849765136347139097)
                      ·
                        rfl

theorem cell23_945529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_945529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945529 prefixEnd_945529 := by exact prefixLift 945529
  have htrace : WordTrace (prefixWord ++ tailWord_945529) baseStart_945529 baseEnd_945529 := by
    simpa [prefixWord, tailWord_945529, baseEnd_945529] using wordTrace_append hprefix tailTrace_945529
  have hstable : (prefixWord ++ tailWord_945529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945529).length < 2 ^ (prefixWord ++ tailWord_945529).sum := by decide
  have hdescent : baseEnd_945529 < baseStart_945529 := by decide
  rcases family_descends (prefixWord ++ tailWord_945529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945533 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_945533 : Nat := 118140960795 + 945533 * 2 ^ 59
def prefixEnd_945533 : Nat := 4983230072969 + 3 ^ 40 * 945533 * 2
def baseEnd_945533 : Nat := 485512903687754331489079

theorem tailTrace_945533 : CollatzResearch.WordTrace tailWord_945533 prefixEnd_945533 485512903687754331489079 := by
  unfold tailWord_945533
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486421683502900025097253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22990947789001933350064835 34486421683502900025097253)
  ·
    refine ⟨6466204065656793754705735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34486421683502900025097253 6466204065656793754705735)
    ·
      refine ⟨9699306098485190632058603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6466204065656793754705735 9699306098485190632058603)
      ·
        refine ⟨14548959147727785948087905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699306098485190632058603 14548959147727785948087905)
        ·
          refine ⟨10911719360795839461065929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14548959147727785948087905 10911719360795839461065929)
          ·
            refine ⟨8183789520596879595799447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911719360795839461065929 8183789520596879595799447)
            ·
              refine ⟨12275684280895319393699171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183789520596879595799447 12275684280895319393699171)
              ·
                refine ⟨18413526421342979090548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12275684280895319393699171 18413526421342979090548757)
                ·
                  refine ⟨863134051000452144869473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18413526421342979090548757 863134051000452144869473)
                  ·
                    refine ⟨647350538250339108652105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863134051000452144869473 647350538250339108652105)
                    ·
                      refine ⟨485512903687754331489079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647350538250339108652105 485512903687754331489079)
                      ·
                        rfl

theorem cell23_945533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_945533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945533 prefixEnd_945533 := by exact prefixLift 945533
  have htrace : WordTrace (prefixWord ++ tailWord_945533) baseStart_945533 baseEnd_945533 := by
    simpa [prefixWord, tailWord_945533, baseEnd_945533] using wordTrace_append hprefix tailTrace_945533
  have hstable : (prefixWord ++ tailWord_945533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945533).length < 2 ^ (prefixWord ++ tailWord_945533).sum := by decide
  have hdescent : baseEnd_945533 < baseStart_945533 := by decide
  rcases family_descends (prefixWord ++ tailWord_945533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945567 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 2, 2, 2]
def baseStart_945567 : Nat := 118140960795 + 945567 * 2 ^ 59
def prefixEnd_945567 : Nat := 4983230072969 + 3 ^ 40 * 945567 * 2
def baseEnd_945567 : Nat := 485530362030007198463923

theorem tailTrace_945567 : CollatzResearch.WordTrace tailWord_945567 prefixEnd_945567 485530362030007198463923 := by
  unfold tailWord_945567
  simp only [CollatzResearch.WordTrace]
  refine ⟨34487661765379723831834955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22991774510253149221223303 34487661765379723831834955)
  ·
    refine ⟨51731492648069585747752433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34487661765379723831834955 51731492648069585747752433)
    ·
      refine ⟨38798619486052189310814325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51731492648069585747752433 38798619486052189310814325)
      ·
        refine ⟨3637370576817392747888843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38798619486052189310814325 3637370576817392747888843)
        ·
          refine ⟨5456055865226089121833265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637370576817392747888843 5456055865226089121833265)
          ·
            refine ⟨4092041898919566841374949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5456055865226089121833265 4092041898919566841374949)
            ·
              refine ⟨767257856047418782757803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4092041898919566841374949 767257856047418782757803)
              ·
                refine ⟨1150886784071128174136705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767257856047418782757803 1150886784071128174136705)
                ·
                  refine ⟨863165088053346130602529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1150886784071128174136705 863165088053346130602529)
                  ·
                    refine ⟨647373816040009597951897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863165088053346130602529 647373816040009597951897)
                    ·
                      refine ⟨485530362030007198463923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647373816040009597951897 485530362030007198463923)
                      ·
                        rfl

theorem cell23_945567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_945567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945567 prefixEnd_945567 := by exact prefixLift 945567
  have htrace : WordTrace (prefixWord ++ tailWord_945567) baseStart_945567 baseEnd_945567 := by
    simpa [prefixWord, tailWord_945567, baseEnd_945567] using wordTrace_append hprefix tailTrace_945567
  have hstable : (prefixWord ++ tailWord_945567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945567).length < 2 ^ (prefixWord ++ tailWord_945567).sum := by decide
  have hdescent : baseEnd_945567 < baseStart_945567 := by decide
  rcases family_descends (prefixWord ++ tailWord_945567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945609 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_945609 : Nat := 118140960795 + 945609 * 2 ^ 59
def prefixEnd_945609 : Nat := 4983230072969 + 3 ^ 40 * 945609 * 2
def baseEnd_945609 : Nat := 485551928217496034138729

theorem tailTrace_945609 : CollatzResearch.WordTrace tailWord_945609 prefixEnd_945609 485551928217496034138729 := by
  unfold tailWord_945609
  simp only [CollatzResearch.WordTrace]
  refine ⟨34489193631227565004863881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22992795754151710003242587 34489193631227565004863881)
  ·
    refine ⟨25866895223420673753647911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34489193631227565004863881 25866895223420673753647911)
    ·
      refine ⟨38800342835131010630471867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25866895223420673753647911 38800342835131010630471867)
      ·
        refine ⟨58200514252696515945707801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38800342835131010630471867 58200514252696515945707801)
        ·
          refine ⟨43650385689522386959280851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58200514252696515945707801 43650385689522386959280851)
          ·
            refine ⟨65475578534283580438921277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43650385689522386959280851 65475578534283580438921277)
            ·
              refine ⟨24553341950356342664595479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65475578534283580438921277 24553341950356342664595479)
              ·
                refine ⟨36830012925534513996893219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24553341950356342664595479 36830012925534513996893219)
                ·
                  refine ⟨55245019388301770995339829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36830012925534513996893219 55245019388301770995339829)
                  ·
                    refine ⟨5179220567653291030813109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55245019388301770995339829 5179220567653291030813109)
                    ·
                      refine ⟨485551928217496034138729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5179220567653291030813109 485551928217496034138729)
                      ·
                        rfl

theorem cell23_945609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_945609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945609 prefixEnd_945609 := by exact prefixLift 945609
  have htrace : WordTrace (prefixWord ++ tailWord_945609) baseStart_945609 baseEnd_945609 := by
    simpa [prefixWord, tailWord_945609, baseEnd_945609] using wordTrace_append hprefix tailTrace_945609
  have hstable : (prefixWord ++ tailWord_945609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945609).length < 2 ^ (prefixWord ++ tailWord_945609).sum := by decide
  have hdescent : baseEnd_945609 < baseStart_945609 := by decide
  rcases family_descends (prefixWord ++ tailWord_945609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945633 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_945633 : Nat := 118140960795 + 945633 * 2 ^ 59
def prefixEnd_945633 : Nat := 4983230072969 + 3 ^ 40 * 945633 * 2
def baseEnd_945633 : Nat := 161854750584401313412873

theorem tailTrace_945633 : CollatzResearch.WordTrace tailWord_945633 prefixEnd_945633 161854750584401313412873 := by
  unfold tailWord_945633
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490068983140617103737553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22993379322093744735825035 34490068983140617103737553)
  ·
    refine ⟨25867551737355462827803165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34490068983140617103737553 25867551737355462827803165)
    ·
      refine ⟨9700331901508298560426187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25867551737355462827803165 9700331901508298560426187)
      ·
        refine ⟨14550497852262447840639281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9700331901508298560426187 14550497852262447840639281)
        ·
          refine ⟨10912873389196835880479461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14550497852262447840639281 10912873389196835880479461)
          ·
            refine ⟨2046163760474406727589899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10912873389196835880479461 2046163760474406727589899)
            ·
              refine ⟨3069245640711610091384849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046163760474406727589899 3069245640711610091384849)
              ·
                refine ⟨2301934230533707568538637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069245640711610091384849 2301934230533707568538637)
                ·
                  refine ⟨863225336450140338201989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2301934230533707568538637 863225336450140338201989)
                  ·
                    refine ⟨161854750584401313412873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863225336450140338201989 161854750584401313412873)
                    ·
                      rfl

theorem cell23_945633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_945633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945633 prefixEnd_945633 := by exact prefixLift 945633
  have htrace : WordTrace (prefixWord ++ tailWord_945633) baseStart_945633 baseEnd_945633 := by
    simpa [prefixWord, tailWord_945633, baseEnd_945633] using wordTrace_append hprefix tailTrace_945633
  have hstable : (prefixWord ++ tailWord_945633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945633).length < 2 ^ (prefixWord ++ tailWord_945633).sum := by decide
  have hdescent : baseEnd_945633 < baseStart_945633 := by decide
  rcases family_descends (prefixWord ++ tailWord_945633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945646 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_945646 : Nat := 118140960795 + 945646 * 2 ^ 59
def prefixEnd_945646 : Nat := 4983230072969 + 3 ^ 40 * 945646 * 2
def baseEnd_945646 : Nat := 53952325222412487708451

theorem tailTrace_945646 : CollatzResearch.WordTrace tailWord_945646 prefixEnd_945646 53952325222412487708451 := by
  unfold tailWord_945646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311317891511690040495099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22993695421395680215973861 4311317891511690040495099)
  ·
    refine ⟨6466976837267535060742649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311317891511690040495099 6466976837267535060742649)
    ·
      refine ⟨4850232627950651295556987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6466976837267535060742649 4850232627950651295556987)
      ·
        refine ⟨7275348941925976943335481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850232627950651295556987 7275348941925976943335481)
        ·
          refine ⟨5456511706444482707501611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275348941925976943335481 5456511706444482707501611)
          ·
            refine ⟨8184767559666724061252417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456511706444482707501611 8184767559666724061252417)
            ·
              refine ⟨6138575669750043045939313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8184767559666724061252417 6138575669750043045939313)
              ·
                refine ⟨4603931752312532284454485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138575669750043045939313 4603931752312532284454485)
                ·
                  refine ⟨53952325222412487708451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4603931752312532284454485 53952325222412487708451)
                  ·
                    rfl

theorem cell23_945646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_945646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945646 prefixEnd_945646 := by exact prefixLift 945646
  have htrace : WordTrace (prefixWord ++ tailWord_945646) baseStart_945646 baseEnd_945646 := by
    simpa [prefixWord, tailWord_945646, baseEnd_945646] using wordTrace_append hprefix tailTrace_945646
  have hstable : (prefixWord ++ tailWord_945646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945646).length < 2 ^ (prefixWord ++ tailWord_945646).sum := by decide
  have hdescent : baseEnd_945646 < baseStart_945646 := by decide
  rcases family_descends (prefixWord ++ tailWord_945646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945653 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_945653 : Nat := 118140960795 + 945653 * 2 ^ 59
def prefixEnd_945653 : Nat := 4983230072969 + 3 ^ 40 * 945653 * 2
def baseEnd_945653 : Nat := 485574521366293861988527

theorem tailTrace_945653 : CollatzResearch.WordTrace tailWord_945653 prefixEnd_945653 485574521366293861988527 := by
  unfold tailWord_945653
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490798443068160519465613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22993865628712107012977075 34490798443068160519465613)
  ·
    refine ⟨12934049416150560194799605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34490798443068160519465613 12934049416150560194799605)
    ·
      refine ⟨1212567132764115018262463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12934049416150560194799605 1212567132764115018262463)
      ·
        refine ⟨1818850699146172527393695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212567132764115018262463 1818850699146172527393695)
        ·
          refine ⟨2728276048719258791090543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818850699146172527393695 2728276048719258791090543)
          ·
            refine ⟨4092414073078888186635815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728276048719258791090543 4092414073078888186635815)
            ·
              refine ⟨6138621109618332279953723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092414073078888186635815 6138621109618332279953723)
              ·
                refine ⟨9207931664427498419930585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138621109618332279953723 9207931664427498419930585)
                ·
                  refine ⟨6905948748320623814947939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207931664427498419930585 6905948748320623814947939)
                  ·
                    refine ⟨10358923122480935722421909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905948748320623814947939 10358923122480935722421909)
                    ·
                      refine ⟨485574521366293861988527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10358923122480935722421909 485574521366293861988527)
                      ·
                        rfl

theorem cell23_945653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_945653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945653 prefixEnd_945653 := by exact prefixLift 945653
  have htrace : WordTrace (prefixWord ++ tailWord_945653) baseStart_945653 baseEnd_945653 := by
    simpa [prefixWord, tailWord_945653, baseEnd_945653] using wordTrace_append hprefix tailTrace_945653
  have hstable : (prefixWord ++ tailWord_945653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945653).length < 2 ^ (prefixWord ++ tailWord_945653).sum := by decide
  have hdescent : baseEnd_945653 < baseStart_945653 := by decide
  rcases family_descends (prefixWord ++ tailWord_945653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945683 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 5, 2]
def baseStart_945683 : Nat := 118140960795 + 945683 * 2 ^ 59
def prefixEnd_945683 : Nat := 4983230072969 + 3 ^ 40 * 945683 * 2
def baseEnd_945683 : Nat := 485589925785928744613389

theorem tailTrace_945683 : CollatzResearch.WordTrace tailWord_945683 prefixEnd_945683 485589925785928744613389 := by
  unfold tailWord_945683
  simp only [CollatzResearch.WordTrace]
  refine ⟨34491892632959475643057703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22994595088639650428705135 34491892632959475643057703)
  ·
    refine ⟨51737838949439213464586555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34491892632959475643057703 51737838949439213464586555)
    ·
      refine ⟨77606758424158820196879833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51737838949439213464586555 77606758424158820196879833)
      ·
        refine ⟨58205068818119115147659875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77606758424158820196879833 58205068818119115147659875)
        ·
          refine ⟨87307603227178672721489813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58205068818119115147659875 87307603227178672721489813)
          ·
            refine ⟨4092543901274000283819835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87307603227178672721489813 4092543901274000283819835)
            ·
              refine ⟨6138815851911000425729753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092543901274000283819835 6138815851911000425729753)
              ·
                refine ⟨4604111888933250319297315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138815851911000425729753 4604111888933250319297315)
                ·
                  refine ⟨6906167833399875478945973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604111888933250319297315 6906167833399875478945973)
                  ·
                    refine ⟨647453234381238326151185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6906167833399875478945973 647453234381238326151185)
                    ·
                      refine ⟨485589925785928744613389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647453234381238326151185 485589925785928744613389)
                      ·
                        rfl

theorem cell23_945683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5, 2].length) (baseStart_945683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945683 prefixEnd_945683 := by exact prefixLift 945683
  have htrace : WordTrace (prefixWord ++ tailWord_945683) baseStart_945683 baseEnd_945683 := by
    simpa [prefixWord, tailWord_945683, baseEnd_945683] using wordTrace_append hprefix tailTrace_945683
  have hstable : (prefixWord ++ tailWord_945683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945683).length < 2 ^ (prefixWord ++ tailWord_945683).sum := by decide
  have hdescent : baseEnd_945683 < baseStart_945683 := by decide
  rcases family_descends (prefixWord ++ tailWord_945683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945710 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_945710 : Nat := 118140960795 + 945710 * 2 ^ 59
def prefixEnd_945710 : Nat := 4983230072969 + 3 ^ 40 * 945710 * 2
def baseEnd_945710 : Nat := 161867929921200046325255

theorem tailTrace_945710 : CollatzResearch.WordTrace tailWord_945710 prefixEnd_945710 161867929921200046325255 := by
  unfold tailWord_945710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311609675482707406786323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22995251602574439502860389 4311609675482707406786323)
  ·
    refine ⟨6467414513224061110179485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311609675482707406786323 6467414513224061110179485)
    ·
      refine ⟨2425280442459022916317307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6467414513224061110179485 2425280442459022916317307)
      ·
        refine ⟨3637920663688534374475961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425280442459022916317307 3637920663688534374475961)
        ·
          refine ⟨2728440497766400780856971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3637920663688534374475961 2728440497766400780856971)
          ·
            refine ⟨4092660746649601171285457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728440497766400780856971 4092660746649601171285457)
            ·
              refine ⟨3069495559987200878464093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092660746649601171285457 3069495559987200878464093)
              ·
                refine ⟨1151060834995200329424035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069495559987200878464093 1151060834995200329424035)
                ·
                  refine ⟨1726591252492800494136053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151060834995200329424035 1726591252492800494136053)
                  ·
                    refine ⟨161867929921200046325255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1726591252492800494136053 161867929921200046325255)
                    ·
                      rfl

theorem cell23_945710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_945710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945710 prefixEnd_945710 := by exact prefixLift 945710
  have htrace : WordTrace (prefixWord ++ tailWord_945710) baseStart_945710 baseEnd_945710 := by
    simpa [prefixWord, tailWord_945710, baseEnd_945710] using wordTrace_append hprefix tailTrace_945710
  have hstable : (prefixWord ++ tailWord_945710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945710).length < 2 ^ (prefixWord ++ tailWord_945710).sum := by decide
  have hdescent : baseEnd_945710 < baseStart_945710 := by decide
  rcases family_descends (prefixWord ++ tailWord_945710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945724 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_945724 : Nat := 118140960795 + 945724 * 2 ^ 59
def prefixEnd_945724 : Nat := 4983230072969 + 3 ^ 40 * 945724 * 2
def baseEnd_945724 : Nat := 485610978492763084200701

theorem tailTrace_945724 : CollatzResearch.WordTrace tailWord_945724 prefixEnd_945724 485610978492763084200701 := by
  unfold tailWord_945724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246694012905469822650113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22995592017207293096866817 17246694012905469822650113)
  ·
    refine ⟨12935020509679102366987585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17246694012905469822650113 12935020509679102366987585)
    ·
      refine ⟨9701265382259326775240689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12935020509679102366987585 9701265382259326775240689)
      ·
        refine ⟨7275949036694495081430517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9701265382259326775240689 7275949036694495081430517)
        ·
          refine ⟨682120222190108913884111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7275949036694495081430517 682120222190108913884111)
          ·
            refine ⟨1023180333285163370826167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682120222190108913884111 1023180333285163370826167)
            ·
              refine ⟨1534770499927745056239251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023180333285163370826167 1534770499927745056239251)
              ·
                refine ⟨2302155749891617584358877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534770499927745056239251 2302155749891617584358877)
                ·
                  refine ⟨863308406209356594134579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2302155749891617584358877 863308406209356594134579)
                  ·
                    refine ⟨1294962609314034891201869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 863308406209356594134579 1294962609314034891201869)
                    ·
                      refine ⟨485610978492763084200701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294962609314034891201869 485610978492763084200701)
                      ·
                        rfl

theorem cell23_945724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_945724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945724 prefixEnd_945724 := by exact prefixLift 945724
  have htrace : WordTrace (prefixWord ++ tailWord_945724) baseStart_945724 baseEnd_945724 := by
    simpa [prefixWord, tailWord_945724, baseEnd_945724] using wordTrace_append hprefix tailTrace_945724
  have hstable : (prefixWord ++ tailWord_945724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945724).length < 2 ^ (prefixWord ++ tailWord_945724).sum := by decide
  have hdescent : baseEnd_945724 < baseStart_945724 := by decide
  rcases family_descends (prefixWord ++ tailWord_945724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945733 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_945733 : Nat := 118140960795 + 945733 * 2 ^ 59
def prefixEnd_945733 : Nat := 4983230072969 + 3 ^ 40 * 945733 * 2
def baseEnd_945733 : Nat := 485615599818653548988159

theorem tailTrace_945733 : CollatzResearch.WordTrace tailWord_945733 prefixEnd_945733 485615599818653548988159 := by
  unfold tailWord_945733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34493716282778334182377853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22995810855185556121585235 34493716282778334182377853)
  ·
    refine ⟨12935143606041875318391695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34493716282778334182377853 12935143606041875318391695)
    ·
      refine ⟨19402715409062812977587543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12935143606041875318391695 19402715409062812977587543)
      ·
        refine ⟨29104073113594219466381315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19402715409062812977587543 29104073113594219466381315)
        ·
          refine ⟨43656109670391329199571973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29104073113594219466381315 43656109670391329199571973)
          ·
            refine ⟨8185520563198374224919745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43656109670391329199571973 8185520563198374224919745)
            ·
              refine ⟨6139140422398780668689809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185520563198374224919745 6139140422398780668689809)
              ·
                refine ⟨4604355316799085501517357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139140422398780668689809 4604355316799085501517357)
                ·
                  refine ⟨1726633243799657063069009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4604355316799085501517357 1726633243799657063069009)
                  ·
                    refine ⟨1294974932849742797301757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726633243799657063069009 1294974932849742797301757)
                    ·
                      refine ⟨485615599818653548988159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1294974932849742797301757 485615599818653548988159)
                      ·
                        rfl

theorem cell23_945733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_945733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945733 prefixEnd_945733 := by exact prefixLift 945733
  have htrace : WordTrace (prefixWord ++ tailWord_945733) baseStart_945733 baseEnd_945733 := by
    simpa [prefixWord, tailWord_945733, baseEnd_945733] using wordTrace_append hprefix tailTrace_945733
  have hstable : (prefixWord ++ tailWord_945733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945733).length < 2 ^ (prefixWord ++ tailWord_945733).sum := by decide
  have hdescent : baseEnd_945733 < baseStart_945733 := by decide
  rcases family_descends (prefixWord ++ tailWord_945733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945740 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_945740 : Nat := 118140960795 + 945740 * 2 ^ 59
def prefixEnd_945740 : Nat := 4983230072969 + 3 ^ 40 * 945740 * 2
def baseEnd_945740 : Nat := 161873064727745007200209

theorem tailTrace_945740 : CollatzResearch.WordTrace tailWord_945740 prefixEnd_945740 161873064727745007200209 := by
  unfold tailWord_945740
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246985796876487188941337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22995981062501982918588449 17246985796876487188941337)
  ·
    refine ⟨12935239347657365391706003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17246985796876487188941337 12935239347657365391706003)
    ·
      refine ⟨19402859021486048087559005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12935239347657365391706003 19402859021486048087559005)
      ·
        refine ⟨7276072133057268032834627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19402859021486048087559005 7276072133057268032834627)
        ·
          refine ⟨10914108199585902049251941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276072133057268032834627 10914108199585902049251941)
          ·
            refine ⟨2046395287422356634234739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10914108199585902049251941 2046395287422356634234739)
            ·
              refine ⟨3069592931133534951352109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046395287422356634234739 3069592931133534951352109)
              ·
                refine ⟨1151097349175075606757041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069592931133534951352109 1151097349175075606757041)
                ·
                  refine ⟨863323011881306705067781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151097349175075606757041 863323011881306705067781)
                  ·
                    refine ⟨161873064727745007200209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863323011881306705067781 161873064727745007200209)
                    ·
                      rfl

theorem cell23_945740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_945740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945740 prefixEnd_945740 := by exact prefixLift 945740
  have htrace : WordTrace (prefixWord ++ tailWord_945740) baseStart_945740 baseEnd_945740 := by
    simpa [prefixWord, tailWord_945740, baseEnd_945740] using wordTrace_append hprefix tailTrace_945740
  have hstable : (prefixWord ++ tailWord_945740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945740).length < 2 ^ (prefixWord ++ tailWord_945740).sum := by decide
  have hdescent : baseEnd_945740 < baseStart_945740 := by decide
  rcases family_descends (prefixWord ++ tailWord_945740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945757 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_945757 : Nat := 118140960795 + 945757 * 2 ^ 59
def prefixEnd_945757 : Nat := 4983230072969 + 3 ^ 40 * 945757 * 2
def baseEnd_945757 : Nat := 161875974451453818362683

theorem tailTrace_945757 : CollatzResearch.WordTrace tailWord_945757 prefixEnd_945757 161875974451453818362683 := by
  unfold tailWord_945757
  simp only [CollatzResearch.WordTrace]
  refine ⟨34494591634691386281251525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22996394423127590854167683 34494591634691386281251525)
  ·
    refine ⟨6467735931504634927734661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34494591634691386281251525 6467735931504634927734661)
    ·
      refine ⟨1212700487157119048950249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6467735931504634927734661 1212700487157119048950249)
      ·
        refine ⟨909525365367839286712687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1212700487157119048950249 909525365367839286712687)
        ·
          refine ⟨1364288048051758930069031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909525365367839286712687 1364288048051758930069031)
          ·
            refine ⟨2046432072077638395103547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364288048051758930069031 2046432072077638395103547)
            ·
              refine ⟨3069648108116457592655321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046432072077638395103547 3069648108116457592655321)
              ·
                refine ⟨2302236081087343194491491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069648108116457592655321 2302236081087343194491491)
                ·
                  refine ⟨3453354121631014791737237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302236081087343194491491 3453354121631014791737237)
                  ·
                    refine ⟨161875974451453818362683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3453354121631014791737237 161875974451453818362683)
                    ·
                      rfl

theorem cell23_945757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_945757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945757 prefixEnd_945757 := by exact prefixLift 945757
  have htrace : WordTrace (prefixWord ++ tailWord_945757) baseStart_945757 baseEnd_945757 := by
    simpa [prefixWord, tailWord_945757, baseEnd_945757] using wordTrace_append hprefix tailTrace_945757
  have hstable : (prefixWord ++ tailWord_945757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945757).length < 2 ^ (prefixWord ++ tailWord_945757).sum := by decide
  have hdescent : baseEnd_945757 < baseStart_945757 := by decide
  rcases family_descends (prefixWord ++ tailWord_945757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945763 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3]
def baseStart_945763 : Nat := 118140960795 + 945763 * 2 ^ 59
def prefixEnd_945763 : Nat := 4983230072969 + 3 ^ 40 * 945763 * 2
def baseEnd_945763 : Nat := 485631004238288431613021

theorem tailTrace_945763 : CollatzResearch.WordTrace tailWord_945763 prefixEnd_945763 485631004238288431613021 := by
  unfold tailWord_945763
  simp only [CollatzResearch.WordTrace]
  refine ⟨34494810472669649305969943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22996540315113099537313295 34494810472669649305969943)
  ·
    refine ⟨51742215709004473958954915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34494810472669649305969943 51742215709004473958954915)
    ·
      refine ⟨77613323563506710938432373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51742215709004473958954915 77613323563506710938432373)
      ·
        refine ⟨7276249084078754150478035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77613323563506710938432373 7276249084078754150478035)
        ·
          refine ⟨10914373626118131225717053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276249084078754150478035 10914373626118131225717053)
          ·
            refine ⟨4092890109794299209643895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914373626118131225717053 4092890109794299209643895)
            ·
              refine ⟨6139335164691448814465843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092890109794299209643895 6139335164691448814465843)
              ·
                refine ⟨9209002747037173221698765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139335164691448814465843 9209002747037173221698765)
                ·
                  refine ⟨3453376030138939958137037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9209002747037173221698765 3453376030138939958137037)
                  ·
                    refine ⟨1295016011302102484301389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453376030138939958137037 1295016011302102484301389)
                    ·
                      refine ⟨485631004238288431613021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1295016011302102484301389 485631004238288431613021)
                      ·
                        rfl

theorem cell23_945763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_945763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945763 prefixEnd_945763 := by exact prefixLift 945763
  have htrace : WordTrace (prefixWord ++ tailWord_945763) baseStart_945763 baseEnd_945763 := by
    simpa [prefixWord, tailWord_945763, baseEnd_945763] using wordTrace_append hprefix tailTrace_945763
  have hstable : (prefixWord ++ tailWord_945763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945763).length < 2 ^ (prefixWord ++ tailWord_945763).sum := by decide
  have hdescent : baseEnd_945763 < baseStart_945763 := by decide
  rcases family_descends (prefixWord ++ tailWord_945763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945781 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_945781 : Nat := 118140960795 + 945781 * 2 ^ 59
def prefixEnd_945781 : Nat := 4983230072969 + 3 ^ 40 * 945781 * 2
def baseEnd_945781 : Nat := 485640246890069361187939

theorem tailTrace_945781 : CollatzResearch.WordTrace tailWord_945781 prefixEnd_945781 485640246890069361187939 := by
  unfold tailWord_945781
  simp only [CollatzResearch.WordTrace]
  refine ⟨34495466986604438380125197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22996977991069625586750131 34495466986604438380125197)
  ·
    refine ⟨12935800119976664392546949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34495466986604438380125197 12935800119976664392546949)
    ·
      refine ⟨2425462522495624573602553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12935800119976664392546949 2425462522495624573602553)
      ·
        refine ⟨1819096891871718430201915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425462522495624573602553 1819096891871718430201915)
        ·
          refine ⟨2728645337807577645302873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819096891871718430201915 2728645337807577645302873)
          ·
            refine ⟨2046484003355683233977155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728645337807577645302873 2046484003355683233977155)
            ·
              refine ⟨3069726005033524850965733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046484003355683233977155 3069726005033524850965733)
              ·
                refine ⟨575573625943785909556075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3069726005033524850965733 575573625943785909556075)
                ·
                  refine ⟨863360438915678864334113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575573625943785909556075 863360438915678864334113)
                  ·
                    refine ⟨647520329186759148250585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863360438915678864334113 647520329186759148250585)
                    ·
                      refine ⟨485640246890069361187939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647520329186759148250585 485640246890069361187939)
                      ·
                        rfl

theorem cell23_945781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_945781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945781 prefixEnd_945781 := by exact prefixLift 945781
  have htrace : WordTrace (prefixWord ++ tailWord_945781) baseStart_945781 baseEnd_945781 := by
    simpa [prefixWord, tailWord_945781, baseEnd_945781] using wordTrace_append hprefix tailTrace_945781
  have hstable : (prefixWord ++ tailWord_945781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945781).length < 2 ^ (prefixWord ++ tailWord_945781).sum := by decide
  have hdescent : baseEnd_945781 < baseStart_945781 := by decide
  rcases family_descends (prefixWord ++ tailWord_945781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945824 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2]
def baseStart_945824 : Nat := 118140960795 + 945824 * 2 ^ 59
def prefixEnd_945824 : Nat := 4983230072969 + 3 ^ 40 * 945824 * 2
def baseEnd_945824 : Nat := 485662326558212692950241

theorem tailTrace_945824 : CollatzResearch.WordTrace tailWord_945824 prefixEnd_945824 485662326558212692950241 := by
  unfold tailWord_945824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17248517662724328361970263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22998023550299104482627017 17248517662724328361970263)
  ·
    refine ⟨25872776494086492542955395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17248517662724328361970263 25872776494086492542955395)
    ·
      refine ⟨38809164741129738814433093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25872776494086492542955395 38809164741129738814433093)
      ·
        refine ⟨7276718388961826027706205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38809164741129738814433093 7276718388961826027706205)
        ·
          refine ⟨2728769395860684760389827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7276718388961826027706205 2728769395860684760389827)
          ·
            refine ⟨4093154093791027140584741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728769395860684760389827 4093154093791027140584741)
            ·
              refine ⟨767466392585817588859639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4093154093791027140584741 767466392585817588859639)
              ·
                refine ⟨1151199588878726383289459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767466392585817588859639 1151199588878726383289459)
                ·
                  refine ⟨1726799383318089574934189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151199588878726383289459 1726799383318089574934189)
                  ·
                    refine ⟨647549768744283590600321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726799383318089574934189 647549768744283590600321)
                    ·
                      refine ⟨485662326558212692950241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647549768744283590600321 485662326558212692950241)
                      ·
                        rfl

theorem cell23_945824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_945824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945824 prefixEnd_945824 := by exact prefixLift 945824
  have htrace : WordTrace (prefixWord ++ tailWord_945824) baseStart_945824 baseEnd_945824 := by
    simpa [prefixWord, tailWord_945824, baseEnd_945824] using wordTrace_append hprefix tailTrace_945824
  have hstable : (prefixWord ++ tailWord_945824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945824).length < 2 ^ (prefixWord ++ tailWord_945824).sum := by decide
  have hdescent : baseEnd_945824 < baseStart_945824 := by decide
  rcases family_descends (prefixWord ++ tailWord_945824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945843 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 7]
def baseStart_945843 : Nat := 118140960795 + 945843 * 2 ^ 59
def prefixEnd_945843 : Nat := 4983230072969 + 3 ^ 40 * 945843 * 2
def baseEnd_945843 : Nat := 53963564743405346512517

theorem tailTrace_945843 : CollatzResearch.WordTrace tailWord_945843 prefixEnd_945843 53963564743405346512517 := by
  unfold tailWord_945843
  simp only [CollatzResearch.WordTrace]
  refine ⟨34497728312379822968882183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22998485541586548645921455 34497728312379822968882183)
  ·
    refine ⟨51746592468569734453323275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34497728312379822968882183 51746592468569734453323275)
    ·
      refine ⟨77619888702854601679984913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51746592468569734453323275 77619888702854601679984913)
      ·
        refine ⟨58214916527140951259988685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77619888702854601679984913 58214916527140951259988685)
        ·
          refine ⟨21830593697677856722495757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58214916527140951259988685 21830593697677856722495757)
          ·
            refine ⟨8186472636629196270935909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21830593697677856722495757 8186472636629196270935909)
            ·
              refine ⟨1534963619367974300800483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8186472636629196270935909 1534963619367974300800483)
              ·
                refine ⟨2302445429051961451200725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534963619367974300800483 2302445429051961451200725)
                ·
                  refine ⟨53963564743405346512517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2302445429051961451200725 53963564743405346512517)
                  ·
                    rfl

theorem cell23_945843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 7].length) (baseStart_945843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945843 prefixEnd_945843 := by exact prefixLift 945843
  have htrace : WordTrace (prefixWord ++ tailWord_945843) baseStart_945843 baseEnd_945843 := by
    simpa [prefixWord, tailWord_945843, baseEnd_945843] using wordTrace_append hprefix tailTrace_945843
  have hstable : (prefixWord ++ tailWord_945843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945843).length < 2 ^ (prefixWord ++ tailWord_945843).sum := by decide
  have hdescent : baseEnd_945843 < baseStart_945843 := by decide
  rcases family_descends (prefixWord ++ tailWord_945843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945854 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_945854 : Nat := 118140960795 + 945854 * 2 ^ 59
def prefixEnd_945854 : Nat := 4983230072969 + 3 ^ 40 * 945854 * 2
def baseEnd_945854 : Nat := 485677730977847575575103

theorem tailTrace_945854 : CollatzResearch.WordTrace tailWord_945854 prefixEnd_945854 485677730977847575575103 := by
  unfold tailWord_945854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312266189417496480941577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22998753010226647898355077 4312266189417496480941577)
  ·
    refine ⟨3234199642063122360706183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4312266189417496480941577 3234199642063122360706183)
    ·
      refine ⟨4851299463094683541059275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234199642063122360706183 4851299463094683541059275)
      ·
        refine ⟨7276949194642025311588913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851299463094683541059275 7276949194642025311588913)
        ·
          refine ⟨5457711895981518983691685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7276949194642025311588913 5457711895981518983691685)
          ·
            refine ⟨1023320980496534809442191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5457711895981518983691685 1023320980496534809442191)
            ·
              refine ⟨1534981470744802214163287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023320980496534809442191 1534981470744802214163287)
              ·
                refine ⟨2302472206117203321244931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534981470744802214163287 2302472206117203321244931)
                ·
                  refine ⟨3453708309175804981867397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302472206117203321244931 3453708309175804981867397)
                  ·
                    refine ⟨647570307970463434100137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3453708309175804981867397 647570307970463434100137)
                    ·
                      refine ⟨485677730977847575575103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647570307970463434100137 485677730977847575575103)
                      ·
                        rfl

theorem cell23_945854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_945854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945854 prefixEnd_945854 := by exact prefixLift 945854
  have htrace : WordTrace (prefixWord ++ tailWord_945854) baseStart_945854 baseEnd_945854 := by
    simpa [prefixWord, tailWord_945854, baseEnd_945854] using wordTrace_append hprefix tailTrace_945854
  have hstable : (prefixWord ++ tailWord_945854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945854).length < 2 ^ (prefixWord ++ tailWord_945854).sum := by decide
  have hdescent : baseEnd_945854 < baseStart_945854 := by decide
  rcases family_descends (prefixWord ++ tailWord_945854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945873 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_945873 : Nat := 118140960795 + 945873 * 2 ^ 59
def prefixEnd_945873 : Nat := 4983230072969 + 3 ^ 40 * 945873 * 2
def baseEnd_945873 : Nat := 161895829036761000412505

theorem tailTrace_945873 : CollatzResearch.WordTrace tailWord_945873 prefixEnd_945873 161895829036761000412505 := by
  unfold tailWord_945873
  simp only [CollatzResearch.WordTrace]
  refine ⟨34498822502271138092474273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22999215001514092061649515 34498822502271138092474273)
  ·
    refine ⟨25874116876703353569355705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34498822502271138092474273 25874116876703353569355705)
    ·
      refine ⟨19405587657527515177016779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25874116876703353569355705 19405587657527515177016779)
      ·
        refine ⟨29108381486291272765525169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19405587657527515177016779 29108381486291272765525169)
        ·
          refine ⟨21831286114718454574143877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29108381486291272765525169 21831286114718454574143877)
          ·
            refine ⟨4093366146509710232651977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21831286114718454574143877 4093366146509710232651977)
            ·
              refine ⟨3070024609882282674488983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093366146509710232651977 3070024609882282674488983)
              ·
                refine ⟨4605036914823424011733475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070024609882282674488983 4605036914823424011733475)
                ·
                  refine ⟨6907555372235136017600213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605036914823424011733475 6907555372235136017600213)
                  ·
                    refine ⟨161895829036761000412505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6907555372235136017600213 161895829036761000412505)
                    ·
                      rfl

theorem cell23_945873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_945873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945873 prefixEnd_945873 := by exact prefixLift 945873
  have htrace : WordTrace (prefixWord ++ tailWord_945873) baseStart_945873 baseEnd_945873 := by
    simpa [prefixWord, tailWord_945873, baseEnd_945873] using wordTrace_append hprefix tailTrace_945873
  have hstable : (prefixWord ++ tailWord_945873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945873).length < 2 ^ (prefixWord ++ tailWord_945873).sum := by decide
  have hdescent : baseEnd_945873 < baseStart_945873 := by decide
  rcases family_descends (prefixWord ++ tailWord_945873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945923 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_945923 : Nat := 118140960795 + 945923 * 2 ^ 59
def prefixEnd_945923 : Nat := 4983230072969 + 3 ^ 40 * 945923 * 2
def baseEnd_945923 : Nat := 485713161143007805612285

theorem tailTrace_945923 : CollatzResearch.WordTrace tailWord_945923 prefixEnd_945923 485713161143007805612285 := by
  unfold tailWord_945923
  simp only [CollatzResearch.WordTrace]
  refine ⟨34500646152089996631794423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23000430768059997754529615 34500646152089996631794423)
  ·
    refine ⟨51750969228134994947691635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34500646152089996631794423 51750969228134994947691635)
    ·
      refine ⟨77626453842202492421537453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51750969228134994947691635 77626453842202492421537453)
      ·
        refine ⟨29109920190825934658076545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77626453842202492421537453 29109920190825934658076545)
        ·
          refine ⟨21832440143119450993557409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29109920190825934658076545 21832440143119450993557409)
          ·
            refine ⟨16374330107339588245168057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21832440143119450993557409 16374330107339588245168057)
            ·
              refine ⟨12280747580504691183876043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16374330107339588245168057 12280747580504691183876043)
              ·
                refine ⟨18421121370757036775814065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12280747580504691183876043 18421121370757036775814065)
                ·
                  refine ⟨13815841028067777581860549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18421121370757036775814065 13815841028067777581860549)
                  ·
                    refine ⟨2590470192762708296598853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13815841028067777581860549 2590470192762708296598853)
                    ·
                      refine ⟨485713161143007805612285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2590470192762708296598853 485713161143007805612285)
                      ·
                        rfl

theorem cell23_945923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_945923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945923 prefixEnd_945923 := by exact prefixLift 945923
  have htrace : WordTrace (prefixWord ++ tailWord_945923) baseStart_945923 baseEnd_945923 := by
    simpa [prefixWord, tailWord_945923, baseEnd_945923] using wordTrace_append hprefix tailTrace_945923
  have hstable : (prefixWord ++ tailWord_945923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945923).length < 2 ^ (prefixWord ++ tailWord_945923).sum := by decide
  have hdescent : baseEnd_945923 < baseStart_945923 := by decide
  rcases family_descends (prefixWord ++ tailWord_945923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945937 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 1, 4]
def baseStart_945937 : Nat := 118140960795 + 945937 * 2 ^ 59
def prefixEnd_945937 : Nat := 4983230072969 + 3 ^ 40 * 945937 * 2
def baseEnd_945937 : Nat := 161906783290723583612407

theorem tailTrace_945937 : CollatzResearch.WordTrace tailWord_945937 prefixEnd_945937 161906783290723583612407 := by
  unfold tailWord_945937
  simp only [CollatzResearch.WordTrace]
  refine ⟨34501156774039277022804065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23000771182692851348536043 34501156774039277022804065)
  ·
    refine ⟨25875867580529457767103049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34501156774039277022804065 25875867580529457767103049)
    ·
      refine ⟨19406900685397093325327287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25875867580529457767103049 19406900685397093325327287)
      ·
        refine ⟨29110351028095639987990931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19406900685397093325327287 29110351028095639987990931)
        ·
          refine ⟨43665526542143459981986397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29110351028095639987990931 43665526542143459981986397)
          ·
            refine ⟨16374572453303797493244899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43665526542143459981986397 16374572453303797493244899)
            ·
              refine ⟨24561858679955696239867349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16374572453303797493244899 24561858679955696239867349)
              ·
                refine ⟨575668562811461630621891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24561858679955696239867349 575668562811461630621891)
                ·
                  refine ⟨863502844217192445932837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575668562811461630621891 863502844217192445932837)
                  ·
                    refine ⟨161906783290723583612407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863502844217192445932837 161906783290723583612407)
                    ·
                      rfl

theorem cell23_945937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_945937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945937 prefixEnd_945937 := by exact prefixLift 945937
  have htrace : WordTrace (prefixWord ++ tailWord_945937) baseStart_945937 baseEnd_945937 := by
    simpa [prefixWord, tailWord_945937, baseEnd_945937] using wordTrace_append hprefix tailTrace_945937
  have hstable : (prefixWord ++ tailWord_945937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945937).length < 2 ^ (prefixWord ++ tailWord_945937).sum := by decide
  have hdescent : baseEnd_945937 < baseStart_945937 := by decide
  rcases family_descends (prefixWord ++ tailWord_945937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945954 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_945954 : Nat := 118140960795 + 945954 * 2 ^ 59
def prefixEnd_945954 : Nat := 4983230072969 + 3 ^ 40 * 945954 * 2
def baseEnd_945954 : Nat := 161909693014432394774881

theorem tailTrace_945954 : CollatzResearch.WordTrace tailWord_945954 prefixEnd_945954 161909693014432394774881 := by
  unfold tailWord_945954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625444203744422231543229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23001184543318459284115277 8625444203744422231543229)
  ·
    refine ⟨3234541576404158336828711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8625444203744422231543229 3234541576404158336828711)
    ·
      refine ⟨4851812364606237505243067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234541576404158336828711 4851812364606237505243067)
      ·
        refine ⟨7277718546909356257864601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851812364606237505243067 7277718546909356257864601)
        ·
          refine ⟨5458288910182017193398451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277718546909356257864601 5458288910182017193398451)
          ·
            refine ⟨8187433365273025790097677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458288910182017193398451 8187433365273025790097677)
            ·
              refine ⟨3070287511977384671286629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8187433365273025790097677 3070287511977384671286629)
              ·
                refine ⟨575678908495759625866243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3070287511977384671286629 575678908495759625866243)
                ·
                  refine ⟨863518362743639438799365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575678908495759625866243 863518362743639438799365)
                  ·
                    refine ⟨161909693014432394774881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863518362743639438799365 161909693014432394774881)
                    ·
                      rfl

theorem cell23_945954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_945954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945954 prefixEnd_945954 := by exact prefixLift 945954
  have htrace : WordTrace (prefixWord ++ tailWord_945954) baseStart_945954 baseEnd_945954 := by
    simpa [prefixWord, tailWord_945954, baseEnd_945954] using wordTrace_append hprefix tailTrace_945954
  have hstable : (prefixWord ++ tailWord_945954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945954).length < 2 ^ (prefixWord ++ tailWord_945954).sum := by decide
  have hdescent : baseEnd_945954 < baseStart_945954 := by decide
  rcases family_descends (prefixWord ++ tailWord_945954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945980 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_945980 : Nat := 118140960795 + 945980 * 2 ^ 59
def prefixEnd_945980 : Nat := 4983230072969 + 3 ^ 40 * 945980 * 2
def baseEnd_945980 : Nat := 161914143180104694199841

theorem tailTrace_945980 : CollatzResearch.WordTrace tailWord_945980 prefixEnd_945980 161914143180104694199841 := by
  unfold tailWord_945980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251362556441747683309697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23001816741922330244412929 17251362556441747683309697)
  ·
    refine ⟨12938521917331310762482273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17251362556441747683309697 12938521917331310762482273)
    ·
      refine ⟨9703891437998483071861705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12938521917331310762482273 9703891437998483071861705)
      ·
        refine ⟨7277918578498862303896279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703891437998483071861705 7277918578498862303896279)
        ·
          refine ⟨10916877867748293455844419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277918578498862303896279 10916877867748293455844419)
          ·
            refine ⟨16375316801622440183766629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916877867748293455844419 16375316801622440183766629)
            ·
              refine ⟨3070371900304207534456243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16375316801622440183766629 3070371900304207534456243)
              ·
                refine ⟨4605557850456311301684365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070371900304207534456243 4605557850456311301684365)
                ·
                  refine ⟨1727084193921116738131637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4605557850456311301684365 1727084193921116738131637)
                  ·
                    refine ⟨161914143180104694199841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1727084193921116738131637 161914143180104694199841)
                    ·
                      rfl

theorem cell23_945980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_945980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945980 prefixEnd_945980 := by exact prefixLift 945980
  have htrace : WordTrace (prefixWord ++ tailWord_945980) baseStart_945980 baseEnd_945980 := by
    simpa [prefixWord, tailWord_945980, baseEnd_945980] using wordTrace_append hprefix tailTrace_945980
  have hstable : (prefixWord ++ tailWord_945980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945980).length < 2 ^ (prefixWord ++ tailWord_945980).sum := by decide
  have hdescent : baseEnd_945980 < baseStart_945980 := by decide
  rcases family_descends (prefixWord ++ tailWord_945980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945987 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 5, 2]
def baseStart_945987 : Nat := 118140960795 + 945987 * 2 ^ 59
def prefixEnd_945987 : Nat := 4983230072969 + 3 ^ 40 * 945987 * 2
def baseEnd_945987 : Nat := 485746023904895555211991

theorem tailTrace_945987 : CollatzResearch.WordTrace tailWord_945987 prefixEnd_945987 485746023904895555211991 := by
  unfold tailWord_945987
  simp only [CollatzResearch.WordTrace]
  refine ⟨34502980423858135562124215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23001986949238757041416143 34502980423858135562124215)
  ·
    refine ⟨51754470635787203343186323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34502980423858135562124215 51754470635787203343186323)
    ·
      refine ⟨77631705953680805014779485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51754470635787203343186323 77631705953680805014779485)
      ·
        refine ⟨29111889732630301880542307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77631705953680805014779485 29111889732630301880542307)
        ·
          refine ⟨43667834598945452820813461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29111889732630301880542307 43667834598945452820813461)
          ·
            refine ⟨2046929746825568100975631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43667834598945452820813461 2046929746825568100975631)
            ·
              refine ⟨3070394620238352151463447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046929746825568100975631 3070394620238352151463447)
              ·
                refine ⟨4605591930357528227195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070394620238352151463447 4605591930357528227195171)
                ·
                  refine ⟨6908387895536292340792757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605591930357528227195171 6908387895536292340792757)
                  ·
                    refine ⟨647661365206527406949321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6908387895536292340792757 647661365206527406949321)
                    ·
                      refine ⟨485746023904895555211991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647661365206527406949321 485746023904895555211991)
                      ·
                        rfl

theorem cell23_945987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_945987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_945987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_945987 prefixEnd_945987 := by exact prefixLift 945987
  have htrace : WordTrace (prefixWord ++ tailWord_945987) baseStart_945987 baseEnd_945987 := by
    simpa [prefixWord, tailWord_945987, baseEnd_945987] using wordTrace_append hprefix tailTrace_945987
  have hstable : (prefixWord ++ tailWord_945987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945987).length < 2 ^ (prefixWord ++ tailWord_945987).sum := by decide
  have hdescent : baseEnd_945987 < baseStart_945987 := by decide
  rcases family_descends (prefixWord ++ tailWord_945987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946068 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_946068 : Nat := 118140960795 + 946068 * 2 ^ 59
def prefixEnd_946068 : Nat := 4983230072969 + 3 ^ 40 * 946068 * 2
def baseEnd_946068 : Nat := 485787615837909738299119

theorem tailTrace_946068 : CollatzResearch.WordTrace tailWord_946068 prefixEnd_946068 485787615837909738299119 := by
  unfold tailWord_946068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17252967368282343197911429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23003956491043124263881905 17252967368282343197911429)
  ·
    refine ⟨3234931381552939349608393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17252967368282343197911429 3234931381552939349608393)
    ·
      refine ⟨2426198536164704512206295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234931381552939349608393 2426198536164704512206295)
      ·
        refine ⟨3639297804247056768309443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426198536164704512206295 3639297804247056768309443)
        ·
          refine ⟨5458946706370585152464165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639297804247056768309443 5458946706370585152464165)
          ·
            refine ⟨1023552507444484716087031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5458946706370585152464165 1023552507444484716087031)
            ·
              refine ⟨1535328761166727074130547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023552507444484716087031 1535328761166727074130547)
              ·
                refine ⟨2302993141750090611195821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535328761166727074130547 2302993141750090611195821)
                ·
                  refine ⟨863622428156283979198433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2302993141750090611195821 863622428156283979198433)
                  ·
                    refine ⟨647716821117212984398825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863622428156283979198433 647716821117212984398825)
                    ·
                      refine ⟨485787615837909738299119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647716821117212984398825 485787615837909738299119)
                      ·
                        rfl

theorem cell23_946068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_946068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946068 prefixEnd_946068 := by exact prefixLift 946068
  have htrace : WordTrace (prefixWord ++ tailWord_946068) baseStart_946068 baseEnd_946068 := by
    simpa [prefixWord, tailWord_946068, baseEnd_946068] using wordTrace_append hprefix tailTrace_946068
  have hstable : (prefixWord ++ tailWord_946068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946068).length < 2 ^ (prefixWord ++ tailWord_946068).sum := by decide
  have hdescent : baseEnd_946068 < baseStart_946068 := by decide
  rcases family_descends (prefixWord ++ tailWord_946068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946078 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_946078 : Nat := 118140960795 + 946078 * 2 ^ 59
def prefixEnd_946078 : Nat := 4983230072969 + 3 ^ 40 * 946078 * 2
def baseEnd_946078 : Nat := 161930916881484899724691

theorem tailTrace_946078 : CollatzResearch.WordTrace tailWord_946078 prefixEnd_946078 161930916881484899724691 := by
  unfold tailWord_946078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313287433316057262960861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23004199644352305402457925 4313287433316057262960861)
  ·
    refine ⟨1617482787493521473610323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4313287433316057262960861 1617482787493521473610323)
    ·
      refine ⟨2426224181240282210415485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1617482787493521473610323 2426224181240282210415485)
      ·
        refine ⟨909834067965105828905807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2426224181240282210415485 909834067965105828905807)
        ·
          refine ⟨1364751101947658743358711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909834067965105828905807 1364751101947658743358711)
          ·
            refine ⟨2047126652921488115038067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364751101947658743358711 2047126652921488115038067)
            ·
              refine ⟨3070689979382232172557101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047126652921488115038067 3070689979382232172557101)
              ·
                refine ⟨1151508742268337064708913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3070689979382232172557101 1151508742268337064708913)
                ·
                  refine ⟨863631556701252798531685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151508742268337064708913 863631556701252798531685)
                  ·
                    refine ⟨161930916881484899724691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863631556701252798531685 161930916881484899724691)
                    ·
                      rfl

theorem cell23_946078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_946078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946078 prefixEnd_946078 := by exact prefixLift 946078
  have htrace : WordTrace (prefixWord ++ tailWord_946078) baseStart_946078 baseEnd_946078 := by
    simpa [prefixWord, tailWord_946078, baseEnd_946078] using wordTrace_append hprefix tailTrace_946078
  have hstable : (prefixWord ++ tailWord_946078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946078).length < 2 ^ (prefixWord ++ tailWord_946078).sum := by decide
  have hdescent : baseEnd_946078 < baseStart_946078 := by decide
  rcases family_descends (prefixWord ++ tailWord_946078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946107 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 3, 4, 2]
def baseStart_946107 : Nat := 118140960795 + 946107 * 2 ^ 59
def prefixEnd_946107 : Nat := 4983230072969 + 3 ^ 40 * 946107 * 2
def baseEnd_946107 : Nat := 485807641583435085711439

theorem tailTrace_946107 : CollatzResearch.WordTrace tailWord_946107 prefixEnd_946107 485807641583435085711439 := by
  unfold tailWord_946107
  simp only [CollatzResearch.WordTrace]
  refine ⟨34507357183423396056492575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23004904788948930704328383 34507357183423396056492575)
  ·
    refine ⟨51761035775135094084738863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34507357183423396056492575 51761035775135094084738863)
    ·
      refine ⟨77641553662702641127108295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51761035775135094084738863 77641553662702641127108295)
      ·
        refine ⟨116462330494053961690662443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77641553662702641127108295 116462330494053961690662443)
        ·
          refine ⟨174693495741080942535993665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116462330494053961690662443 174693495741080942535993665)
          ·
            refine ⟨131020121805810706901995249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174693495741080942535993665 131020121805810706901995249)
            ·
              refine ⟨98265091354358030176496437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131020121805810706901995249 98265091354358030176496437)
              ·
                refine ⟨9212352314471065329046541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98265091354358030176496437 9212352314471065329046541)
                ·
                  refine ⟨3454632117926649498392453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9212352314471065329046541 3454632117926649498392453)
                  ·
                    refine ⟨647743522111246780948585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454632117926649498392453 647743522111246780948585)
                    ·
                      refine ⟨485807641583435085711439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647743522111246780948585 485807641583435085711439)
                      ·
                        rfl

theorem cell23_946107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4, 2].length) (baseStart_946107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946107 prefixEnd_946107 := by exact prefixLift 946107
  have htrace : WordTrace (prefixWord ++ tailWord_946107) baseStart_946107 baseEnd_946107 := by
    simpa [prefixWord, tailWord_946107, baseEnd_946107] using wordTrace_append hprefix tailTrace_946107
  have hstable : (prefixWord ++ tailWord_946107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946107).length < 2 ^ (prefixWord ++ tailWord_946107).sum := by decide
  have hdescent : baseEnd_946107 < baseStart_946107 := by decide
  rcases family_descends (prefixWord ++ tailWord_946107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946111 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 1, 3, 2]
def baseStart_946111 : Nat := 118140960795 + 946111 * 2 ^ 59
def prefixEnd_946111 : Nat := 4983230072969 + 3 ^ 40 * 946111 * 2
def baseEnd_946111 : Nat := 485809695506053070061421

theorem tailTrace_946111 : CollatzResearch.WordTrace tailWord_946111 prefixEnd_946111 485809695506053070061421 := by
  unfold tailWord_946111
  simp only [CollatzResearch.WordTrace]
  refine ⟨34507503075408904739638187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23005002050272603159758791 34507503075408904739638187)
  ·
    refine ⟨51761254613113357109457281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34507503075408904739638187 51761254613113357109457281)
    ·
      refine ⟨38820940959835017832092961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51761254613113357109457281 38820940959835017832092961)
      ·
        refine ⟨29115705719876263374069721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38820940959835017832092961 29115705719876263374069721)
        ·
          refine ⟨21836779289907197530552291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29115705719876263374069721 21836779289907197530552291)
          ·
            refine ⟨32755168934860796295828437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21836779289907197530552291 32755168934860796295828437)
            ·
              refine ⟨767699271910799913183479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32755168934860796295828437 767699271910799913183479)
              ·
                refine ⟨1151548907866199869775219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767699271910799913183479 1151548907866199869775219)
                ·
                  refine ⟨1727323361799299804662829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151548907866199869775219 1727323361799299804662829)
                  ·
                    refine ⟨647746260674737426748561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727323361799299804662829 647746260674737426748561)
                    ·
                      refine ⟨485809695506053070061421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647746260674737426748561 485809695506053070061421)
                      ·
                        rfl

theorem cell23_946111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_946111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946111 prefixEnd_946111 := by exact prefixLift 946111
  have htrace : WordTrace (prefixWord ++ tailWord_946111) baseStart_946111 baseEnd_946111 := by
    simpa [prefixWord, tailWord_946111, baseEnd_946111] using wordTrace_append hprefix tailTrace_946111
  have hstable : (prefixWord ++ tailWord_946111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946111).length < 2 ^ (prefixWord ++ tailWord_946111).sum := by decide
  have hdescent : baseEnd_946111 < baseStart_946111 := by decide
  rcases family_descends (prefixWord ++ tailWord_946111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946147 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 7]
def baseStart_946147 : Nat := 118140960795 + 946147 * 2 ^ 59
def prefixEnd_946147 : Nat := 4983230072969 + 3 ^ 40 * 946147 * 2
def baseEnd_946147 : Nat := 53980908978846103245695

theorem tailTrace_946147 : CollatzResearch.WordTrace tailWord_946147 prefixEnd_946147 53980908978846103245695 := by
  unfold tailWord_946147
  simp only [CollatzResearch.WordTrace]
  refine ⟨34508816103278482887948695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23005877402185655258632463 34508816103278482887948695)
  ·
    refine ⟨51763224154917724331923043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34508816103278482887948695 51763224154917724331923043)
    ·
      refine ⟨77644836232376586497884565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51763224154917724331923043 77644836232376586497884565)
      ·
        refine ⟨3639601698392652492088339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77644836232376586497884565 3639601698392652492088339)
        ·
          refine ⟨5459402547588978738132509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639601698392652492088339 5459402547588978738132509)
          ·
            refine ⟨2047275955345867026799691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5459402547588978738132509 2047275955345867026799691)
            ·
              refine ⟨3070913933018800540199537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047275955345867026799691 3070913933018800540199537)
              ·
                refine ⟨2303185449764100405149653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070913933018800540199537 2303185449764100405149653)
                ·
                  refine ⟨53980908978846103245695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2303185449764100405149653 53980908978846103245695)
                  ·
                    rfl

theorem cell23_946147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 7].length) (baseStart_946147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946147 prefixEnd_946147 := by exact prefixLift 946147
  have htrace : WordTrace (prefixWord ++ tailWord_946147) baseStart_946147 baseEnd_946147 := by
    simpa [prefixWord, tailWord_946147, baseEnd_946147] using wordTrace_append hprefix tailTrace_946147
  have hstable : (prefixWord ++ tailWord_946147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946147).length < 2 ^ (prefixWord ++ tailWord_946147).sum := by decide
  have hdescent : baseEnd_946147 < baseStart_946147 := by decide
  rcases family_descends (prefixWord ++ tailWord_946147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
