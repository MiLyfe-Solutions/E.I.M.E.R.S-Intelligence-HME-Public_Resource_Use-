import V185TrunkScan23Chunk0205

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1218754 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1218754 : Nat := 118140960795 + 1218754 * 2 ^ 59
def prefixEnd_1218754 : Nat := 4983230072969 + 3 ^ 40 * 1218754 * 2
def baseEnd_1218754 : Nat := 625806601589829853070059

theorem tailTrace_1218754 : CollatzResearch.WordTrace tailWord_1218754 prefixEnd_1218754 625806601589829853070059 := by
  unfold tailWord_1218754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112902556667469864227829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29634406817779919637940877 11112902556667469864227829)
  ·
    refine ⟨1041834614687575299771359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11112902556667469864227829 1041834614687575299771359)
    ·
      refine ⟨1562751922031362949657039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041834614687575299771359 1562751922031362949657039)
      ·
        refine ⟨2344127883047044424485559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562751922031362949657039 2344127883047044424485559)
        ·
          refine ⟨3516191824570566636728339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344127883047044424485559 3516191824570566636728339)
          ·
            refine ⟨5274287736855849955092509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516191824570566636728339 5274287736855849955092509)
            ·
              refine ⟨1977857901320943733159691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5274287736855849955092509 1977857901320943733159691)
              ·
                refine ⟨2966786851981415599739537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977857901320943733159691 2966786851981415599739537)
                ·
                  refine ⟨2225090138986061699804653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966786851981415599739537 2225090138986061699804653)
                  ·
                    refine ⟨834408802119773137426745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225090138986061699804653 834408802119773137426745)
                    ·
                      refine ⟨625806601589829853070059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834408802119773137426745 625806601589829853070059)
                      ·
                        rfl

theorem cell23_1218754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1218754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218754 prefixEnd_1218754 := by exact prefixLift 1218754
  have htrace : WordTrace (prefixWord ++ tailWord_1218754) baseStart_1218754 baseEnd_1218754 := by
    simpa [prefixWord, tailWord_1218754, baseEnd_1218754] using wordTrace_append hprefix tailTrace_1218754
  have hstable : (prefixWord ++ tailWord_1218754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218754).length < 2 ^ (prefixWord ++ tailWord_1218754).sum := by decide
  have hdescent : baseEnd_1218754 < baseStart_1218754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218764 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_1218764 : Nat := 118140960795 + 1218764 * 2 ^ 59
def prefixEnd_1218764 : Nat := 4983230072969 + 3 ^ 40 * 1218764 * 2
def baseEnd_1218764 : Nat := 208603912132124937981671

theorem tailTrace_1218764 : CollatzResearch.WordTrace tailWord_1218764 prefixEnd_1218764 208603912132124937981671 := by
  unfold tailWord_1218764
  simp only [CollatzResearch.WordTrace]
  refine ⟨22225987478316825582387673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29634649971089100776516897 22225987478316825582387673)
  ·
    refine ⟨16669490608737619186790755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22225987478316825582387673 16669490608737619186790755)
    ·
      refine ⟨25004235913106428780186133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16669490608737619186790755 25004235913106428780186133)
      ·
        refine ⟨1172073558426863849071225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25004235913106428780186133 1172073558426863849071225)
        ·
          refine ⟨879055168820147886803419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172073558426863849071225 879055168820147886803419)
          ·
            refine ⟨1318582753230221830205129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879055168820147886803419 1318582753230221830205129)
            ·
              refine ⟨988937064922666372653847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318582753230221830205129 988937064922666372653847)
              ·
                refine ⟨1483405597383999558980771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988937064922666372653847 1483405597383999558980771)
                ·
                  refine ⟨2225108396075999338471157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483405597383999558980771 2225108396075999338471157)
                  ·
                    refine ⟨208603912132124937981671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2225108396075999338471157 208603912132124937981671)
                    ·
                      rfl

theorem cell23_1218764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_1218764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218764 prefixEnd_1218764 := by exact prefixLift 1218764
  have htrace : WordTrace (prefixWord ++ tailWord_1218764) baseStart_1218764 baseEnd_1218764 := by
    simpa [prefixWord, tailWord_1218764, baseEnd_1218764] using wordTrace_append hprefix tailTrace_1218764
  have hstable : (prefixWord ++ tailWord_1218764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218764).length < 2 ^ (prefixWord ++ tailWord_1218764).sum := by decide
  have hdescent : baseEnd_1218764 < baseStart_1218764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218767 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 1, 2, 2]
def baseStart_1218767 : Nat := 118140960795 + 1218767 * 2 ^ 59
def prefixEnd_1218767 : Nat := 4983230072969 + 3 ^ 40 * 1218767 * 2
def baseEnd_1218767 : Nat := 625813276838338302207499

theorem tailTrace_1218767 : CollatzResearch.WordTrace tailWord_1218767 prefixEnd_1218767 625813276838338302207499 := by
  unfold tailWord_1218767
  simp only [CollatzResearch.WordTrace]
  refine ⟨44452084375622782677134555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29634722917081855118089703 44452084375622782677134555)
  ·
    refine ⟨66678126563434174015701833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44452084375622782677134555 66678126563434174015701833)
    ·
      refine ⟨50008594922575630511776375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66678126563434174015701833 50008594922575630511776375)
      ·
        refine ⟨75012892383863445767664563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50008594922575630511776375 75012892383863445767664563)
        ·
          refine ⟨112519338575795168651496845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75012892383863445767664563 112519338575795168651496845)
          ·
            refine ⟨42194751965923188244311317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112519338575795168651496845 42194751965923188244311317)
            ·
              refine ⟨1977878998402649448952093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42194751965923188244311317 1977878998402649448952093)
              ·
                refine ⟨741704624400993543357035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977878998402649448952093 741704624400993543357035)
                ·
                  refine ⟨1112556936601490315035553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741704624400993543357035 1112556936601490315035553)
                  ·
                    refine ⟨834417702451117736276665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112556936601490315035553 834417702451117736276665)
                    ·
                      refine ⟨625813276838338302207499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834417702451117736276665 625813276838338302207499)
                      ·
                        rfl

theorem cell23_1218767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 2, 2].length) (baseStart_1218767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218767 prefixEnd_1218767 := by exact prefixLift 1218767
  have htrace : WordTrace (prefixWord ++ tailWord_1218767) baseStart_1218767 baseEnd_1218767 := by
    simpa [prefixWord, tailWord_1218767, baseEnd_1218767] using wordTrace_append hprefix tailTrace_1218767
  have hstable : (prefixWord ++ tailWord_1218767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218767).length < 2 ^ (prefixWord ++ tailWord_1218767).sum := by decide
  have hdescent : baseEnd_1218767 < baseStart_1218767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218770 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1218770 : Nat := 118140960795 + 1218770 * 2 ^ 59
def prefixEnd_1218770 : Nat := 4983230072969 + 3 ^ 40 * 1218770 * 2
def baseEnd_1218770 : Nat := 625814817280301790469985

theorem tailTrace_1218770 : CollatzResearch.WordTrace tailWord_1218770 prefixEnd_1218770 625814817280301790469985 := by
  unfold tailWord_1218770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113048448652978547373441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29634795863074609459662509 11113048448652978547373441)
  ·
    refine ⟨8334786336489733910530081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11113048448652978547373441 8334786336489733910530081)
    ·
      refine ⟨6251089752367300432897561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8334786336489733910530081 6251089752367300432897561)
      ·
        refine ⟨4688317314275475324673171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6251089752367300432897561 4688317314275475324673171)
        ·
          refine ⟨7032475971413212987009757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688317314275475324673171 7032475971413212987009757)
          ·
            refine ⟨2637178489279954870128659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7032475971413212987009757 2637178489279954870128659)
            ·
              refine ⟨3955767733919932305192989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637178489279954870128659 3955767733919932305192989)
              ·
                refine ⟨1483412900219974614447371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3955767733919932305192989 1483412900219974614447371)
                ·
                  refine ⟨2225119350329961921671057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483412900219974614447371 2225119350329961921671057)
                  ·
                    refine ⟨1668839512747471441253293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225119350329961921671057 1668839512747471441253293)
                    ·
                      refine ⟨625814817280301790469985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1668839512747471441253293 625814817280301790469985)
                      ·
                        rfl

theorem cell23_1218770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1218770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218770 prefixEnd_1218770 := by exact prefixLift 1218770
  have htrace : WordTrace (prefixWord ++ tailWord_1218770) baseStart_1218770 baseEnd_1218770 := by
    simpa [prefixWord, tailWord_1218770, baseEnd_1218770] using wordTrace_append hprefix tailTrace_1218770
  have hstable : (prefixWord ++ tailWord_1218770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218770).length < 2 ^ (prefixWord ++ tailWord_1218770).sum := by decide
  have hdescent : baseEnd_1218770 < baseStart_1218770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218797 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1218797 : Nat := 118140960795 + 1218797 * 2 ^ 59
def prefixEnd_1218797 : Nat := 4983230072969 + 3 ^ 40 * 1218797 * 2
def baseEnd_1218797 : Nat := 625828681257973184832361

theorem tailTrace_1218797 : CollatzResearch.WordTrace tailWord_1218797 prefixEnd_1218797 625828681257973184832361 := by
  unfold tailWord_1218797
  simp only [CollatzResearch.WordTrace]
  refine ⟨44453178565514097800726645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29635452377009398533817763 44453178565514097800726645)
  ·
    refine ⟨4167485490516946668818123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44453178565514097800726645 4167485490516946668818123)
    ·
      refine ⟨6251228235775420003227185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4167485490516946668818123 6251228235775420003227185)
      ·
        refine ⟨4688421176831565002420389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6251228235775420003227185 4688421176831565002420389)
        ·
          refine ⟨879078970655918437953823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4688421176831565002420389 879078970655918437953823)
          ·
            refine ⟨1318618455983877656930735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879078970655918437953823 1318618455983877656930735)
            ·
              refine ⟨1977927683975816485396103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318618455983877656930735 1977927683975816485396103)
              ·
                refine ⟨2966891525963724728094155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977927683975816485396103 2966891525963724728094155)
                ·
                  refine ⟨4450337288945587092141233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966891525963724728094155 4450337288945587092141233)
                  ·
                    refine ⟨3337752966709190319105925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4450337288945587092141233 3337752966709190319105925)
                    ·
                      refine ⟨625828681257973184832361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3337752966709190319105925 625828681257973184832361)
                      ·
                        rfl

theorem cell23_1218797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1218797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218797 prefixEnd_1218797 := by exact prefixLift 1218797
  have htrace : WordTrace (prefixWord ++ tailWord_1218797) baseStart_1218797 baseEnd_1218797 := by
    simpa [prefixWord, tailWord_1218797, baseEnd_1218797] using wordTrace_append hprefix tailTrace_1218797
  have hstable : (prefixWord ++ tailWord_1218797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218797).length < 2 ^ (prefixWord ++ tailWord_1218797).sum := by decide
  have hdescent : baseEnd_1218797 < baseStart_1218797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218810 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_1218810 : Nat := 118140960795 + 1218810 * 2 ^ 59
def prefixEnd_1218810 : Nat := 4983230072969 + 3 ^ 40 * 1218810 * 2
def baseEnd_1218810 : Nat := 625835356506481633969801

theorem tailTrace_1218810 : CollatzResearch.WordTrace tailWord_1218810 prefixEnd_1218810 625835356506481633969801 := by
  unfold tailWord_1218810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113413178616750255237471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29635768476311334013966589 11113413178616750255237471)
  ·
    refine ⟨16670119767925125382856207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11113413178616750255237471 16670119767925125382856207)
    ·
      refine ⟨25005179651887688074284311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16670119767925125382856207 25005179651887688074284311)
      ·
        refine ⟨37507769477831532111426467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25005179651887688074284311 37507769477831532111426467)
        ·
          refine ⟨56261654216747298167139701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37507769477831532111426467 56261654216747298167139701)
          ·
            refine ⟨5274530082820059203169347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56261654216747298167139701 5274530082820059203169347)
            ·
              refine ⟨7911795124230088804754021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274530082820059203169347 7911795124230088804754021)
              ·
                refine ⟨1483461585793141650891379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7911795124230088804754021 1483461585793141650891379)
                ·
                  refine ⟨2225192378689712476337069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483461585793141650891379 2225192378689712476337069)
                  ·
                    refine ⟨834447142008642178626401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225192378689712476337069 834447142008642178626401)
                    ·
                      refine ⟨625835356506481633969801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834447142008642178626401 625835356506481633969801)
                      ·
                        rfl

theorem cell23_1218810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_1218810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218810 prefixEnd_1218810 := by exact prefixLift 1218810
  have htrace : WordTrace (prefixWord ++ tailWord_1218810) baseStart_1218810 baseEnd_1218810 := by
    simpa [prefixWord, tailWord_1218810, baseEnd_1218810] using wordTrace_append hprefix tailTrace_1218810
  have hstable : (prefixWord ++ tailWord_1218810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218810).length < 2 ^ (prefixWord ++ tailWord_1218810).sum := by decide
  have hdescent : baseEnd_1218810 < baseStart_1218810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218826 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1218826 : Nat := 118140960795 + 1218826 * 2 ^ 59
def prefixEnd_1218826 : Nat := 4983230072969 + 3 ^ 40 * 1218826 * 2
def baseEnd_1218826 : Nat := 625843572196953571369727

theorem tailTrace_1218826 : CollatzResearch.WordTrace tailWord_1218826 prefixEnd_1218826 625843572196953571369727 := by
  unfold tailWord_1218826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113559070602258938383083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29636157521606023835688221 11113559070602258938383083)
  ·
    refine ⟨16670338605903388407574625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11113559070602258938383083 16670338605903388407574625)
    ·
      refine ⟨12502753954427541305680969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16670338605903388407574625 12502753954427541305680969)
      ·
        refine ⟨9377065465820655979260727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12502753954427541305680969 9377065465820655979260727)
        ·
          refine ⟨14065598198730983968891091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377065465820655979260727 14065598198730983968891091)
          ·
            refine ⟨21098397298096475953336637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14065598198730983968891091 21098397298096475953336637)
            ·
              refine ⟨7911898986786178482501239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21098397298096475953336637 7911898986786178482501239)
              ·
                refine ⟨11867848480179267723751859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7911898986786178482501239 11867848480179267723751859)
                ·
                  refine ⟨17801772720268901585627789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11867848480179267723751859 17801772720268901585627789)
                  ·
                    refine ⟨6675664770100838094610421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17801772720268901585627789 6675664770100838094610421)
                    ·
                      refine ⟨625843572196953571369727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6675664770100838094610421 625843572196953571369727)
                      ·
                        rfl

theorem cell23_1218826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1218826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218826 prefixEnd_1218826 := by exact prefixLift 1218826
  have htrace : WordTrace (prefixWord ++ tailWord_1218826) baseStart_1218826 baseEnd_1218826 := by
    simpa [prefixWord, tailWord_1218826, baseEnd_1218826] using wordTrace_append hprefix tailTrace_1218826
  have hstable : (prefixWord ++ tailWord_1218826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218826).length < 2 ^ (prefixWord ++ tailWord_1218826).sum := by decide
  have hdescent : baseEnd_1218826 < baseStart_1218826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218840 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1218840 : Nat := 118140960795 + 1218840 * 2 ^ 59
def prefixEnd_1218840 : Nat := 4983230072969 + 3 ^ 40 * 1218840 * 2
def baseEnd_1218840 : Nat := 625850760926116516594663

theorem tailTrace_1218840 : CollatzResearch.WordTrace tailWord_1218840 prefixEnd_1218840 625850760926116516594663 := by
  unfold tailWord_1218840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22227373452179158072270987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29636497936238877429694649 22227373452179158072270987)
  ·
    refine ⟨33341060178268737108406481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22227373452179158072270987 33341060178268737108406481)
    ·
      refine ⟨25005795133701552831304861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33341060178268737108406481 25005795133701552831304861)
      ·
        refine ⟨9377173175138082311739323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25005795133701552831304861 9377173175138082311739323)
        ·
          refine ⟨14065759762707123467608985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377173175138082311739323 14065759762707123467608985)
          ·
            refine ⟨10549319822030342600706739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14065759762707123467608985 10549319822030342600706739)
            ·
              refine ⟨15823979733045513901060109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549319822030342600706739 15823979733045513901060109)
              ·
                refine ⟨5933992399892067712897541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15823979733045513901060109 5933992399892067712897541)
                ·
                  refine ⟨1112623574979762696168289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5933992399892067712897541 1112623574979762696168289)
                  ·
                    refine ⟨834467681234822022126217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112623574979762696168289 834467681234822022126217)
                    ·
                      refine ⟨625850760926116516594663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834467681234822022126217 625850760926116516594663)
                      ·
                        rfl

theorem cell23_1218840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1218840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218840 prefixEnd_1218840 := by exact prefixLift 1218840
  have htrace : WordTrace (prefixWord ++ tailWord_1218840) baseStart_1218840 baseEnd_1218840 := by
    simpa [prefixWord, tailWord_1218840, baseEnd_1218840] using wordTrace_append hprefix tailTrace_1218840
  have hstable : (prefixWord ++ tailWord_1218840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218840).length < 2 ^ (prefixWord ++ tailWord_1218840).sum := by decide
  have hdescent : baseEnd_1218840 < baseStart_1218840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218861 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1218861 : Nat := 118140960795 + 1218861 * 2 ^ 59
def prefixEnd_1218861 : Nat := 4983230072969 + 3 ^ 40 * 1218861 * 2
def baseEnd_1218861 : Nat := 625861544019860934432067

theorem tailTrace_1218861 : CollatzResearch.WordTrace tailWord_1218861 prefixEnd_1218861 625861544019860934432067 := by
  unfold tailWord_1218861
  simp only [CollatzResearch.WordTrace]
  refine ⟨44455512837282236731056437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29637008558188157820704291 44455512837282236731056437)
  ·
    refine ⟨4167704328495209693536541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44455512837282236731056437 4167704328495209693536541)
    ·
      refine ⟨1562889123185703635076203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4167704328495209693536541 1562889123185703635076203)
      ·
        refine ⟨2344333684778555452614305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562889123185703635076203 2344333684778555452614305)
        ·
          refine ⟨1758250263583916589460729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344333684778555452614305 1758250263583916589460729)
          ·
            refine ⟨1318687697687937442095547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758250263583916589460729 1318687697687937442095547)
            ·
              refine ⟨1978031546531906163143321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318687697687937442095547 1978031546531906163143321)
              ·
                refine ⟨1483523659898929622357491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978031546531906163143321 1483523659898929622357491)
                ·
                  refine ⟨2225285489848394433536237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483523659898929622357491 2225285489848394433536237)
                  ·
                    refine ⟨834482058693147912576089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225285489848394433536237 834482058693147912576089)
                    ·
                      refine ⟨625861544019860934432067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834482058693147912576089 625861544019860934432067)
                      ·
                        rfl

theorem cell23_1218861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1218861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218861 prefixEnd_1218861 := by exact prefixLift 1218861
  have htrace : WordTrace (prefixWord ++ tailWord_1218861) baseStart_1218861 baseEnd_1218861 := by
    simpa [prefixWord, tailWord_1218861, baseEnd_1218861] using wordTrace_append hprefix tailTrace_1218861
  have hstable : (prefixWord ++ tailWord_1218861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218861).length < 2 ^ (prefixWord ++ tailWord_1218861).sum := by decide
  have hdescent : baseEnd_1218861 < baseStart_1218861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218897 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 5]
def baseStart_1218897 : Nat := 118140960795 + 1218897 * 2 ^ 59
def prefixEnd_1218897 : Nat := 4983230072969 + 3 ^ 40 * 1218897 * 2
def baseEnd_1218897 : Nat := 69542225480380310397989

theorem tailTrace_1218897 : CollatzResearch.WordTrace tailWord_1218897 prefixEnd_1218897 69542225480380310397989 := by
  unfold tailWord_1218897
  simp only [CollatzResearch.WordTrace]
  refine ⟨44456825865151814879366945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29637883910101209919577963 44456825865151814879366945)
  ·
    refine ⟨33342619398863861159525209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44456825865151814879366945 33342619398863861159525209)
    ·
      refine ⟨25006964549147895869643907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33342619398863861159525209 25006964549147895869643907)
      ·
        refine ⟨37510446823721843804465861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25006964549147895869643907 37510446823721843804465861)
        ·
          refine ⟨7033208779447845713337349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37510446823721843804465861 7033208779447845713337349)
          ·
            refine ⟨1318726646146471071250753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7033208779447845713337349 1318726646146471071250753)
            ·
              refine ⟨989044984609853303438065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318726646146471071250753 989044984609853303438065)
              ·
                refine ⟨741783738457389977578549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989044984609853303438065 741783738457389977578549)
                ·
                  refine ⟨69542225480380310397989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741783738457389977578549 69542225480380310397989)
                  ·
                    rfl

theorem cell23_1218897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 5].length) (baseStart_1218897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218897 prefixEnd_1218897 := by exact prefixLift 1218897
  have htrace : WordTrace (prefixWord ++ tailWord_1218897) baseStart_1218897 baseEnd_1218897 := by
    simpa [prefixWord, tailWord_1218897, baseEnd_1218897] using wordTrace_append hprefix tailTrace_1218897
  have hstable : (prefixWord ++ tailWord_1218897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218897).length < 2 ^ (prefixWord ++ tailWord_1218897).sum := by decide
  have hdescent : baseEnd_1218897 < baseStart_1218897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218900 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_1218900 : Nat := 118140960795 + 1218900 * 2 ^ 59
def prefixEnd_1218900 : Nat := 4983230072969 + 3 ^ 40 * 1218900 * 2
def baseEnd_1218900 : Nat := 625881569765386281844387

theorem tailTrace_1218900 : CollatzResearch.WordTrace tailWord_1218900 prefixEnd_1218900 625881569765386281844387 := by
  unfold tailWord_1218900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22228467642070473195863077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29637956856093964261150769 22228467642070473195863077)
  ·
    refine ⟨4167837682888213724224327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22228467642070473195863077 4167837682888213724224327)
    ·
      refine ⟨6251756524332320586336491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4167837682888213724224327 6251756524332320586336491)
      ·
        refine ⟨9377634786498480879504737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251756524332320586336491 9377634786498480879504737)
        ·
          refine ⟨7033226089873860659628553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9377634786498480879504737 7033226089873860659628553)
          ·
            refine ⟨5274919567405395494721415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7033226089873860659628553 5274919567405395494721415)
            ·
              refine ⟨7912379351108093242082123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274919567405395494721415 7912379351108093242082123)
              ·
                refine ⟨11868569026662139863123185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912379351108093242082123 11868569026662139863123185)
                ·
                  refine ⟨8901426769996604897342389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11868569026662139863123185 8901426769996604897342389)
                  ·
                    refine ⟨834508759687181709125849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8901426769996604897342389 834508759687181709125849)
                    ·
                      refine ⟨625881569765386281844387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834508759687181709125849 625881569765386281844387)
                      ·
                        rfl

theorem cell23_1218900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_1218900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218900 prefixEnd_1218900 := by exact prefixLift 1218900
  have htrace : WordTrace (prefixWord ++ tailWord_1218900) baseStart_1218900 baseEnd_1218900 := by
    simpa [prefixWord, tailWord_1218900, baseEnd_1218900] using wordTrace_append hprefix tailTrace_1218900
  have hstable : (prefixWord ++ tailWord_1218900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218900).length < 2 ^ (prefixWord ++ tailWord_1218900).sum := by decide
  have hdescent : baseEnd_1218900 < baseStart_1218900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218906 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_1218906 : Nat := 118140960795 + 1218906 * 2 ^ 59
def prefixEnd_1218906 : Nat := 4983230072969 + 3 ^ 40 * 1218906 * 2
def baseEnd_1218906 : Nat := 208628216883104419456453

theorem tailTrace_1218906 : CollatzResearch.WordTrace tailWord_1218906 prefixEnd_1218906 208628216883104419456453 := by
  unfold tailWord_1218906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114288530529802354111143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29638102748079472944296381 11114288530529802354111143)
  ·
    refine ⟨16671432795794703531166715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11114288530529802354111143 16671432795794703531166715)
    ·
      refine ⟨25007149193692055296750073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16671432795794703531166715 25007149193692055296750073)
      ·
        refine ⟨18755361895269041472562555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25007149193692055296750073 18755361895269041472562555)
        ·
          refine ⟨28133042842903562208843833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18755361895269041472562555 28133042842903562208843833)
          ·
            refine ⟨21099782132177671656632875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28133042842903562208843833 21099782132177671656632875)
            ·
              refine ⟨31649673198266507484949313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21099782132177671656632875 31649673198266507484949313)
              ·
                refine ⟨23737254898699880613711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31649673198266507484949313 23737254898699880613711985)
                ·
                  refine ⟨17802941174024910460283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23737254898699880613711985 17802941174024910460283989)
                  ·
                    refine ⟨208628216883104419456453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17802941174024910460283989 208628216883104419456453)
                    ·
                      rfl

theorem cell23_1218906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_1218906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218906 prefixEnd_1218906 := by exact prefixLift 1218906
  have htrace : WordTrace (prefixWord ++ tailWord_1218906) baseStart_1218906 baseEnd_1218906 := by
    simpa [prefixWord, tailWord_1218906, baseEnd_1218906] using wordTrace_append hprefix tailTrace_1218906
  have hstable : (prefixWord ++ tailWord_1218906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218906).length < 2 ^ (prefixWord ++ tailWord_1218906).sum := by decide
  have hdescent : baseEnd_1218906 < baseStart_1218906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218923 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 3, 4]
def baseStart_1218923 : Nat := 118140960795 + 1218923 * 2 ^ 59
def prefixEnd_1218923 : Nat := 4983230072969 + 3 ^ 40 * 1218923 * 2
def baseEnd_1218923 : Nat := 208631126606813230618927

theorem tailTrace_1218923 : CollatzResearch.WordTrace tailWord_1218923 prefixEnd_1218923 208631126606813230618927 := by
  unfold tailWord_1218923
  simp only [CollatzResearch.WordTrace]
  refine ⟨44457774163057621319813423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29638516108705080879875615 44457774163057621319813423)
  ·
    refine ⟨66686661244586431979720135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44457774163057621319813423 66686661244586431979720135)
    ·
      refine ⟨100029991866879647969580203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66686661244586431979720135 100029991866879647969580203)
      ·
        refine ⟨150044987800319471954370305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100029991866879647969580203 150044987800319471954370305)
        ·
          refine ⟨112533740850239603965777729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150044987800319471954370305 112533740850239603965777729)
          ·
            refine ⟨84400305637679702974333297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112533740850239603965777729 84400305637679702974333297)
            ·
              refine ⟨63300229228259777230749973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84400305637679702974333297 63300229228259777230749973)
              ·
                refine ⟨2967198245074677057691405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63300229228259777230749973 2967198245074677057691405)
                ·
                  refine ⟨1112699341903003896634277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2967198245074677057691405 1112699341903003896634277)
                  ·
                    refine ⟨208631126606813230618927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1112699341903003896634277 208631126606813230618927)
                    ·
                      rfl

theorem cell23_1218923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 4].length) (baseStart_1218923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218923 prefixEnd_1218923 := by exact prefixLift 1218923
  have htrace : WordTrace (prefixWord ++ tailWord_1218923) baseStart_1218923 baseEnd_1218923 := by
    simpa [prefixWord, tailWord_1218923, baseEnd_1218923] using wordTrace_append hprefix tailTrace_1218923
  have hstable : (prefixWord ++ tailWord_1218923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218923).length < 2 ^ (prefixWord ++ tailWord_1218923).sum := by decide
  have hdescent : baseEnd_1218923 < baseStart_1218923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218930 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1218930 : Nat := 118140960795 + 1218930 * 2 ^ 59
def prefixEnd_1218930 : Nat := 4983230072969 + 3 ^ 40 * 1218930 * 2
def baseEnd_1218930 : Nat := 625896974185021164469249

theorem tailTrace_1218930 : CollatzResearch.WordTrace tailWord_1218930 prefixEnd_1218930 625896974185021164469249 := by
  unfold tailWord_1218930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114507368508065378829561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29638686316021507676878829 11114507368508065378829561)
  ·
    refine ⟨8335880526381049034122171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11114507368508065378829561 8335880526381049034122171)
    ·
      refine ⟨12503820789571573551183257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8335880526381049034122171 12503820789571573551183257)
      ·
        refine ⟨9377865592178680163387443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12503820789571573551183257 9377865592178680163387443)
        ·
          refine ⟨14066798388268020245081165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377865592178680163387443 14066798388268020245081165)
          ·
            refine ⟨5275049395600507591905437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14066798388268020245081165 5275049395600507591905437)
            ·
              refine ⟨1978143523350190346964539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5275049395600507591905437 1978143523350190346964539)
              ·
                refine ⟨2967215285025285520446809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978143523350190346964539 2967215285025285520446809)
                ·
                  refine ⟨2225411463768964140335107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2967215285025285520446809 2225411463768964140335107)
                  ·
                    refine ⟨3338117195653446210502661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225411463768964140335107 3338117195653446210502661)
                    ·
                      refine ⟨625896974185021164469249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3338117195653446210502661 625896974185021164469249)
                      ·
                        rfl

theorem cell23_1218930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1218930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218930 prefixEnd_1218930 := by exact prefixLift 1218930
  have htrace : WordTrace (prefixWord ++ tailWord_1218930) baseStart_1218930 baseEnd_1218930 := by
    simpa [prefixWord, tailWord_1218930, baseEnd_1218930] using wordTrace_append hprefix tailTrace_1218930
  have hstable : (prefixWord ++ tailWord_1218930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218930).length < 2 ^ (prefixWord ++ tailWord_1218930).sum := by decide
  have hdescent : baseEnd_1218930 < baseStart_1218930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218953 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 8]
def baseStart_1218953 : Nat := 118140960795 + 1218953 * 2 ^ 59
def prefixEnd_1218953 : Nat := 4983230072969 + 3 ^ 40 * 1218953 * 2
def baseEnd_1218953 : Nat := 69545420471119397164627

theorem tailTrace_1218953 : CollatzResearch.WordTrace tailWord_1218953 prefixEnd_1218953 69545420471119397164627 := by
  unfold tailWord_1218953
  simp only [CollatzResearch.WordTrace]
  refine ⟨44458868352948936443405513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29639245568632624295603675 44458868352948936443405513)
  ·
    refine ⟨33344151264711702332554135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44458868352948936443405513 33344151264711702332554135)
    ·
      refine ⟨50016226897067553498831203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33344151264711702332554135 50016226897067553498831203)
      ·
        refine ⟨75024340345601330248246805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50016226897067553498831203 75024340345601330248246805)
        ·
          refine ⟨3516765953700062355386569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75024340345601330248246805 3516765953700062355386569)
          ·
            refine ⟨2637574465275046766539927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3516765953700062355386569 2637574465275046766539927)
            ·
              refine ⟨3956361697912570149809891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637574465275046766539927 3956361697912570149809891)
              ·
                refine ⟨5934542546868855224714837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956361697912570149809891 5934542546868855224714837)
                ·
                  refine ⟨69545420471119397164627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5934542546868855224714837 69545420471119397164627)
                  ·
                    rfl

theorem cell23_1218953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_1218953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218953 prefixEnd_1218953 := by exact prefixLift 1218953
  have htrace : WordTrace (prefixWord ++ tailWord_1218953) baseStart_1218953 baseEnd_1218953 := by
    simpa [prefixWord, tailWord_1218953, baseEnd_1218953] using wordTrace_append hprefix tailTrace_1218953
  have hstable : (prefixWord ++ tailWord_1218953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218953).length < 2 ^ (prefixWord ++ tailWord_1218953).sum := by decide
  have hdescent : baseEnd_1218953 < baseStart_1218953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219023 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_1219023 : Nat := 118140960795 + 1219023 * 2 ^ 59
def prefixEnd_1219023 : Nat := 4983230072969 + 3 ^ 40 * 1219023 * 2
def baseEnd_1219023 : Nat := 625944727885889300606321

theorem tailTrace_1219023 : CollatzResearch.WordTrace tailWord_1219023 prefixEnd_1219023 625944727885889300606321 := by
  unfold tailWord_1219023
  simp only [CollatzResearch.WordTrace]
  refine ⟨44461421462695338398453723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29640947641796892265635815 44461421462695338398453723)
  ·
    refine ⟨66692132194043007597680585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44461421462695338398453723 66692132194043007597680585)
    ·
      refine ⟨50019099145532255698260439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66692132194043007597680585 50019099145532255698260439)
      ·
        refine ⟨75028648718298383547390659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50019099145532255698260439 75028648718298383547390659)
        ·
          refine ⟨112542973077447575321085989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75028648718298383547390659 112542973077447575321085989)
          ·
            refine ⟨21101807452021420372703623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112542973077447575321085989 21101807452021420372703623)
            ·
              refine ⟨31652711178032130559055435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21101807452021420372703623 31652711178032130559055435)
              ·
                refine ⟨47479066767048195838583153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31652711178032130559055435 47479066767048195838583153)
                ·
                  refine ⟨35609300075286146878937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47479066767048195838583153 35609300075286146878937365)
                  ·
                    refine ⟨1669185941029038134950189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35609300075286146878937365 1669185941029038134950189)
                    ·
                      refine ⟨625944727885889300606321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1669185941029038134950189 625944727885889300606321)
                      ·
                        rfl

theorem cell23_1219023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_1219023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219023 prefixEnd_1219023 := by exact prefixLift 1219023
  have htrace : WordTrace (prefixWord ++ tailWord_1219023) baseStart_1219023 baseEnd_1219023 := by
    simpa [prefixWord, tailWord_1219023, baseEnd_1219023] using wordTrace_append hprefix tailTrace_1219023
  have hstable : (prefixWord ++ tailWord_1219023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219023).length < 2 ^ (prefixWord ++ tailWord_1219023).sum := by decide
  have hdescent : baseEnd_1219023 < baseStart_1219023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219033 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_1219033 : Nat := 118140960795 + 1219033 * 2 ^ 59
def prefixEnd_1219033 : Nat := 4983230072969 + 3 ^ 40 * 1219033 * 2
def baseEnd_1219033 : Nat := 625949862692434261481275

theorem tailTrace_1219033 : CollatzResearch.WordTrace tailWord_1219033 prefixEnd_1219033 625949862692434261481275 := by
  unfold tailWord_1219033
  simp only [CollatzResearch.WordTrace]
  refine ⟨44461786192659110106317753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29641190795106073404211835 44461786192659110106317753)
  ·
    refine ⟨33346339644494332579738315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44461786192659110106317753 33346339644494332579738315)
    ·
      refine ⟨50019509466741498869607473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33346339644494332579738315 50019509466741498869607473)
      ·
        refine ⟨37514632100056124152205605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50019509466741498869607473 37514632100056124152205605)
        ·
          refine ⟨7033993518760523278538551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37514632100056124152205605 7033993518760523278538551)
          ·
            refine ⟨10550990278140784917807827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7033993518760523278538551 10550990278140784917807827)
            ·
              refine ⟨15826485417211177376711741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10550990278140784917807827 15826485417211177376711741)
              ·
                refine ⟨5934932031454191516266903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15826485417211177376711741 5934932031454191516266903)
                ·
                  refine ⟨8902398047181287274400355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5934932031454191516266903 8902398047181287274400355)
                  ·
                    refine ⟨13353597070771930911600533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8902398047181287274400355 13353597070771930911600533)
                    ·
                      refine ⟨625949862692434261481275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13353597070771930911600533 625949862692434261481275)
                      ·
                        rfl

theorem cell23_1219033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_1219033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219033 prefixEnd_1219033 := by exact prefixLift 1219033
  have htrace : WordTrace (prefixWord ++ tailWord_1219033) baseStart_1219033 baseEnd_1219033 := by
    simpa [prefixWord, tailWord_1219033, baseEnd_1219033] using wordTrace_append hprefix tailTrace_1219033
  have hstable : (prefixWord ++ tailWord_1219033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219033).length < 2 ^ (prefixWord ++ tailWord_1219033).sum := by decide
  have hdescent : baseEnd_1219033 < baseStart_1219033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219040 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_1219040 : Nat := 118140960795 + 1219040 * 2 ^ 59
def prefixEnd_1219040 : Nat := 4983230072969 + 3 ^ 40 * 1219040 * 2
def baseEnd_1219040 : Nat := 625953457057015734093743

theorem tailTrace_1219040 : CollatzResearch.WordTrace tailWord_1219040 prefixEnd_1219040 625953457057015734093743 := by
  unfold tailWord_1219040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22231020751816875150911287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29641361002422500201215049 22231020751816875150911287)
  ·
    refine ⟨33346531127725312726366931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22231020751816875150911287 33346531127725312726366931)
    ·
      refine ⟨50019796691587969089550397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33346531127725312726366931 50019796691587969089550397)
      ·
        refine ⟨18757423759345488408581399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50019796691587969089550397 18757423759345488408581399)
        ·
          refine ⟨28136135639018232612872099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18757423759345488408581399 28136135639018232612872099)
          ·
            refine ⟨42204203458527348919308149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28136135639018232612872099 42204203458527348919308149)
            ·
              refine ⟨3956644074236938961185139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42204203458527348919308149 3956644074236938961185139)
              ·
                refine ⟨5934966111355408441777709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956644074236938961185139 5934966111355408441777709)
                ·
                  refine ⟨2225612291758278165666641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5934966111355408441777709 2225612291758278165666641)
                  ·
                    refine ⟨1669209218818708624249981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225612291758278165666641 1669209218818708624249981)
                    ·
                      refine ⟨625953457057015734093743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1669209218818708624249981 625953457057015734093743)
                      ·
                        rfl

theorem cell23_1219040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_1219040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219040 prefixEnd_1219040 := by exact prefixLift 1219040
  have htrace : WordTrace (prefixWord ++ tailWord_1219040) baseStart_1219040 baseEnd_1219040 := by
    simpa [prefixWord, tailWord_1219040, baseEnd_1219040] using wordTrace_append hprefix tailTrace_1219040
  have hstable : (prefixWord ++ tailWord_1219040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219040).length < 2 ^ (prefixWord ++ tailWord_1219040).sum := by decide
  have hdescent : baseEnd_1219040 < baseStart_1219040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219050 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1219050 : Nat := 118140960795 + 1219050 * 2 ^ 59
def prefixEnd_1219050 : Nat := 4983230072969 + 3 ^ 40 * 1219050 * 2
def baseEnd_1219050 : Nat := 625958591863560694968697

theorem tailTrace_1219050 : CollatzResearch.WordTrace tailWord_1219050 prefixEnd_1219050 625958591863560694968697 := by
  unfold tailWord_1219050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115601558399380502421651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29641604155731681339791069 11115601558399380502421651)
  ·
    refine ⟨16673402337599070753632477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11115601558399380502421651 16673402337599070753632477)
    ·
      refine ⟨6252525876599651532612179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16673402337599070753632477 6252525876599651532612179)
      ·
        refine ⟨9378788814899477298918269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6252525876599651532612179 9378788814899477298918269)
        ·
          refine ⟨3517045805587303987094351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9378788814899477298918269 3517045805587303987094351)
          ·
            refine ⟨5275568708380955980641527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517045805587303987094351 5275568708380955980641527)
            ·
              refine ⟨7913353062571433970962291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275568708380955980641527 7913353062571433970962291)
              ·
                refine ⟨11870029593857150956443437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913353062571433970962291 11870029593857150956443437)
                ·
                  refine ⟨4451261097696431608666289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11870029593857150956443437 4451261097696431608666289)
                  ·
                    refine ⟨3338445823272323706499717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4451261097696431608666289 3338445823272323706499717)
                    ·
                      refine ⟨625958591863560694968697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3338445823272323706499717 625958591863560694968697)
                      ·
                        rfl

theorem cell23_1219050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1219050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219050 prefixEnd_1219050 := by exact prefixLift 1219050
  have htrace : WordTrace (prefixWord ++ tailWord_1219050) baseStart_1219050 baseEnd_1219050 := by
    simpa [prefixWord, tailWord_1219050, baseEnd_1219050] using wordTrace_append hprefix tailTrace_1219050
  have hstable : (prefixWord ++ tailWord_1219050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219050).length < 2 ^ (prefixWord ++ tailWord_1219050).sum := by decide
  have hdescent : baseEnd_1219050 < baseStart_1219050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219054 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_1219054 : Nat := 118140960795 + 1219054 * 2 ^ 59
def prefixEnd_1219054 : Nat := 4983230072969 + 3 ^ 40 * 1219054 * 2
def baseEnd_1219054 : Nat := 625960645786178679318679

theorem tailTrace_1219054 : CollatzResearch.WordTrace tailWord_1219054 prefixEnd_1219054 625960645786178679318679 := by
  unfold tailWord_1219054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557819015697878836604027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29641701417055353795221477 5557819015697878836604027)
  ·
    refine ⟨8336728523546818254906041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5557819015697878836604027 8336728523546818254906041)
    ·
      refine ⟨6252546392660113691179531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8336728523546818254906041 6252546392660113691179531)
      ·
        refine ⟨9378819588990170536769297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6252546392660113691179531 9378819588990170536769297)
        ·
          refine ⟨7034114691742627902576973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9378819588990170536769297 7034114691742627902576973)
          ·
            refine ⟨2637793009403485463466365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7034114691742627902576973 2637793009403485463466365)
            ·
              refine ⟨989172378526307048799887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2637793009403485463466365 989172378526307048799887)
              ·
                refine ⟨1483758567789460573199831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989172378526307048799887 1483758567789460573199831)
                ·
                  refine ⟨2225637851684190859799747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483758567789460573199831 2225637851684190859799747)
                  ·
                    refine ⟨3338456777526286289699621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225637851684190859799747 3338456777526286289699621)
                    ·
                      refine ⟨625960645786178679318679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3338456777526286289699621 625960645786178679318679)
                      ·
                        rfl

theorem cell23_1219054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_1219054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219054 prefixEnd_1219054 := by exact prefixLift 1219054
  have htrace : WordTrace (prefixWord ++ tailWord_1219054) baseStart_1219054 baseEnd_1219054 := by
    simpa [prefixWord, tailWord_1219054, baseEnd_1219054] using wordTrace_append hprefix tailTrace_1219054
  have hstable : (prefixWord ++ tailWord_1219054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219054).length < 2 ^ (prefixWord ++ tailWord_1219054).sum := by decide
  have hdescent : baseEnd_1219054 < baseStart_1219054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219103 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 8]
def baseStart_1219103 : Nat := 118140960795 + 1219103 * 2 ^ 59
def prefixEnd_1219103 : Nat := 4983230072969 + 3 ^ 40 * 1219103 * 2
def baseEnd_1219103 : Nat := 208661935446082995868651

theorem tailTrace_1219103 : CollatzResearch.WordTrace tailWord_1219103 prefixEnd_1219103 208661935446082995868651 := by
  unfold tailWord_1219103
  simp only [CollatzResearch.WordTrace]
  refine ⟨44464339302405512061365963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29642892868270341374243975 44464339302405512061365963)
  ·
    refine ⟨66696508953608268092048945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44464339302405512061365963 66696508953608268092048945)
    ·
      refine ⟨50022381715206201069036709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66696508953608268092048945 50022381715206201069036709)
      ·
        refine ⟨9379196571601162700444383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50022381715206201069036709 9379196571601162700444383)
        ·
          refine ⟨14068794857401744050666575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9379196571601162700444383 14068794857401744050666575)
          ·
            refine ⟨21103192286102616075999863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14068794857401744050666575 21103192286102616075999863)
            ·
              refine ⟨31654788429153924113999795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21103192286102616075999863 31654788429153924113999795)
              ·
                refine ⟨47482182643730886170999693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31654788429153924113999795 47482182643730886170999693)
                ·
                  refine ⟨17805818491399082314124885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47482182643730886170999693 17805818491399082314124885)
                  ·
                    refine ⟨208661935446082995868651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17805818491399082314124885 208661935446082995868651)
                    ·
                      rfl

theorem cell23_1219103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_1219103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219103 prefixEnd_1219103 := by exact prefixLift 1219103
  have htrace : WordTrace (prefixWord ++ tailWord_1219103) baseStart_1219103 baseEnd_1219103 := by
    simpa [prefixWord, tailWord_1219103, baseEnd_1219103] using wordTrace_append hprefix tailTrace_1219103
  have hstable : (prefixWord ++ tailWord_1219103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219103).length < 2 ^ (prefixWord ++ tailWord_1219103).sum := by decide
  have hdescent : baseEnd_1219103 < baseStart_1219103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219108 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1219108 : Nat := 118140960795 + 1219108 * 2 ^ 59
def prefixEnd_1219108 : Nat := 4983230072969 + 3 ^ 40 * 1219108 * 2
def baseEnd_1219108 : Nat := 625988373741521468043431

theorem tailTrace_1219108 : CollatzResearch.WordTrace tailWord_1219108 prefixEnd_1219108 625988373741521468043431 := by
  unfold tailWord_1219108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232260833693698957648989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29643014444924931943531985 22232260833693698957648989)
  ·
    refine ⟨8337097812635137109118371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22232260833693698957648989 8337097812635137109118371)
    ·
      refine ⟨12505646718952705663677557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8337097812635137109118371 12505646718952705663677557)
      ·
        refine ⟨1172404379901816155969771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12505646718952705663677557 1172404379901816155969771)
        ·
          refine ⟨1758606569852724233954657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172404379901816155969771 1758606569852724233954657)
          ·
            refine ⟨1318954927389543175465993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758606569852724233954657 1318954927389543175465993)
            ·
              refine ⟨989216195542157381599495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318954927389543175465993 989216195542157381599495)
              ·
                refine ⟨1483824293313236072399243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989216195542157381599495 1483824293313236072399243)
                ·
                  refine ⟨2225736439969854108598865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483824293313236072399243 2225736439969854108598865)
                  ·
                    refine ⟨1669302329977390581449149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225736439969854108598865 1669302329977390581449149)
                    ·
                      refine ⟨625988373741521468043431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1669302329977390581449149 625988373741521468043431)
                      ·
                        rfl

theorem cell23_1219108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1219108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219108 prefixEnd_1219108 := by exact prefixLift 1219108
  have htrace : WordTrace (prefixWord ++ tailWord_1219108) baseStart_1219108 baseEnd_1219108 := by
    simpa [prefixWord, tailWord_1219108, baseEnd_1219108] using wordTrace_append hprefix tailTrace_1219108
  have hstable : (prefixWord ++ tailWord_1219108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219108).length < 2 ^ (prefixWord ++ tailWord_1219108).sum := by decide
  have hdescent : baseEnd_1219108 < baseStart_1219108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219144 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_1219144 : Nat := 118140960795 + 1219144 * 2 ^ 59
def prefixEnd_1219144 : Nat := 4983230072969 + 3 ^ 40 * 1219144 * 2
def baseEnd_1219144 : Nat := 626006859045083327193265

theorem tailTrace_1219144 : CollatzResearch.WordTrace tailWord_1219144 prefixEnd_1219144 626006859045083327193265 := by
  unfold tailWord_1219144
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232917347628488031804243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29643889796837984042405657 22232917347628488031804243)
  ·
    refine ⟨33349376021442732047706365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22232917347628488031804243 33349376021442732047706365)
    ·
      refine ⟨12506016008041024517889887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33349376021442732047706365 12506016008041024517889887)
      ·
        refine ⟨18759024012061536776834831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12506016008041024517889887 18759024012061536776834831)
        ·
          refine ⟨28138536018092305165252247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759024012061536776834831 28138536018092305165252247)
          ·
            refine ⟨42207804027138457747878371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28138536018092305165252247 42207804027138457747878371)
            ·
              refine ⟨63311706040707686621817557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42207804027138457747878371 63311706040707686621817557)
              ·
                refine ⟨1483868110329086405198849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63311706040707686621817557 1483868110329086405198849)
                ·
                  refine ⟨1112901082746814803899137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1483868110329086405198849 1112901082746814803899137)
                  ·
                    refine ⟨834675812060111102924353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112901082746814803899137 834675812060111102924353)
                    ·
                      refine ⟨626006859045083327193265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834675812060111102924353 626006859045083327193265)
                      ·
                        rfl

theorem cell23_1219144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_1219144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219144 prefixEnd_1219144 := by exact prefixLift 1219144
  have htrace : WordTrace (prefixWord ++ tailWord_1219144) baseStart_1219144 baseEnd_1219144 := by
    simpa [prefixWord, tailWord_1219144, baseEnd_1219144] using wordTrace_append hprefix tailTrace_1219144
  have hstable : (prefixWord ++ tailWord_1219144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219144).length < 2 ^ (prefixWord ++ tailWord_1219144).sum := by decide
  have hdescent : baseEnd_1219144 < baseStart_1219144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219150 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_1219150 : Nat := 118140960795 + 1219150 * 2 ^ 59
def prefixEnd_1219150 : Nat := 4983230072969 + 3 ^ 40 * 1219150 * 2
def baseEnd_1219150 : Nat := 69556659992112255968693

theorem tailTrace_1219150 : CollatzResearch.WordTrace tailWord_1219150 prefixEnd_1219150 69556659992112255968693 := by
  unfold tailWord_1219150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558256691654404886040863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29644035688823492725551269 5558256691654404886040863)
  ·
    refine ⟨8337385037481607329061295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5558256691654404886040863 8337385037481607329061295)
    ·
      refine ⟨12506077556222410993591943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8337385037481607329061295 12506077556222410993591943)
      ·
        refine ⟨18759116334333616490387915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12506077556222410993591943 18759116334333616490387915)
        ·
          refine ⟨28138674501500424735581873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759116334333616490387915 28138674501500424735581873)
          ·
            refine ⟨21104005876125318551686405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28138674501500424735581873 21104005876125318551686405)
            ·
              refine ⟨3957001101773497228441201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21104005876125318551686405 3957001101773497228441201)
              ·
                refine ⟨2967750826330122921330901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957001101773497228441201 2967750826330122921330901)
                ·
                  refine ⟨69556659992112255968693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2967750826330122921330901 69556659992112255968693)
                  ·
                    rfl

theorem cell23_1219150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_1219150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219150 prefixEnd_1219150 := by exact prefixLift 1219150
  have htrace : WordTrace (prefixWord ++ tailWord_1219150) baseStart_1219150 baseEnd_1219150 := by
    simpa [prefixWord, tailWord_1219150, baseEnd_1219150] using wordTrace_append hprefix tailTrace_1219150
  have hstable : (prefixWord ++ tailWord_1219150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219150).length < 2 ^ (prefixWord ++ tailWord_1219150).sum := by decide
  have hdescent : baseEnd_1219150 < baseStart_1219150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219160 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1219160 : Nat := 118140960795 + 1219160 * 2 ^ 59
def prefixEnd_1219160 : Nat := 4983230072969 + 3 ^ 40 * 1219160 * 2
def baseEnd_1219160 : Nat := 626015074735555264593191

theorem tailTrace_1219160 : CollatzResearch.WordTrace tailWord_1219160 prefixEnd_1219160 626015074735555264593191 := by
  unfold tailWord_1219160
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233209131599505398095467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29644278842132673864127289 22233209131599505398095467)
  ·
    refine ⟨33349813697399258097143201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22233209131599505398095467 33349813697399258097143201)
    ·
      refine ⟨25012360273049443572857401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33349813697399258097143201 25012360273049443572857401)
      ·
        refine ⟨18759270204787082679643051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25012360273049443572857401 18759270204787082679643051)
        ·
          refine ⟨28138905307180624019464577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759270204787082679643051 28138905307180624019464577)
          ·
            refine ⟨21104178980385468014598433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28138905307180624019464577 21104178980385468014598433)
            ·
              refine ⟨15828134235289101010948825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21104178980385468014598433 15828134235289101010948825)
              ·
                refine ⟨11871100676466825758211619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15828134235289101010948825 11871100676466825758211619)
                ·
                  refine ⟨17806651014700238637317429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871100676466825758211619 17806651014700238637317429)
                  ·
                    refine ⟨1669373532628147372248509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17806651014700238637317429 1669373532628147372248509)
                    ·
                      refine ⟨626015074735555264593191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1669373532628147372248509 626015074735555264593191)
                      ·
                        rfl

theorem cell23_1219160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1219160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219160 prefixEnd_1219160 := by exact prefixLift 1219160
  have htrace : WordTrace (prefixWord ++ tailWord_1219160) baseStart_1219160 baseEnd_1219160 := by
    simpa [prefixWord, tailWord_1219160, baseEnd_1219160] using wordTrace_append hprefix tailTrace_1219160
  have hstable : (prefixWord ++ tailWord_1219160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219160).length < 2 ^ (prefixWord ++ tailWord_1219160).sum := by decide
  have hdescent : baseEnd_1219160 < baseStart_1219160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219180 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_1219180 : Nat := 118140960795 + 1219180 * 2 ^ 59
def prefixEnd_1219180 : Nat := 4983230072969 + 3 ^ 40 * 1219180 * 2
def baseEnd_1219180 : Nat := 208675114782881728781033

theorem tailTrace_1219180 : CollatzResearch.WordTrace tailWord_1219180 prefixEnd_1219180 208675114782881728781033 := by
  unfold tailWord_1219180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233573861563277105959497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29644765148751036141279329 22233573861563277105959497)
  ·
    refine ⟨16675180396172457829469623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22233573861563277105959497 16675180396172457829469623)
    ·
      refine ⟨25012770594258686744204435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16675180396172457829469623 25012770594258686744204435)
      ·
        refine ⟨37519155891388030116306653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25012770594258686744204435 37519155891388030116306653)
        ·
          refine ⟨14069683459270511293614995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37519155891388030116306653 14069683459270511293614995)
          ·
            refine ⟨21104525188905766940422493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14069683459270511293614995 21104525188905766940422493)
            ·
              refine ⟨7914196945839662602658435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21104525188905766940422493 7914196945839662602658435)
              ·
                refine ⟨11871295418759493903987653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914196945839662602658435 11871295418759493903987653)
                ·
                  refine ⟨2225867891017405106997685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11871295418759493903987653 2225867891017405106997685)
                  ·
                    refine ⟨208675114782881728781033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2225867891017405106997685 208675114782881728781033)
                    ·
                      rfl

theorem cell23_1219180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_1219180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219180 prefixEnd_1219180 := by exact prefixLift 1219180
  have htrace : WordTrace (prefixWord ++ tailWord_1219180) baseStart_1219180 baseEnd_1219180 := by
    simpa [prefixWord, tailWord_1219180, baseEnd_1219180] using wordTrace_append hprefix tailTrace_1219180
  have hstable : (prefixWord ++ tailWord_1219180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219180).length < 2 ^ (prefixWord ++ tailWord_1219180).sum := by decide
  have hdescent : baseEnd_1219180 < baseStart_1219180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219184 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 7]
def baseStart_1219184 : Nat := 118140960795 + 1219184 * 2 ^ 59
def prefixEnd_1219184 : Nat := 4983230072969 + 3 ^ 40 * 1219184 * 2
def baseEnd_1219184 : Nat := 69558599807918130077009

theorem tailTrace_1219184 : CollatzResearch.WordTrace tailWord_1219184 prefixEnd_1219184 69558599807918130077009 := by
  unfold tailWord_1219184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233646807556031447532303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29644862410074708596709737 22233646807556031447532303)
  ·
    refine ⟨33350470211334047171298455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22233646807556031447532303 33350470211334047171298455)
    ·
      refine ⟨50025705317001070756947683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33350470211334047171298455 50025705317001070756947683)
      ·
        refine ⟨75038557975501606135421525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50025705317001070756947683 75038557975501606135421525)
        ·
          refine ⟨879358101275409446899471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 75038557975501606135421525 879358101275409446899471)
          ·
            refine ⟨1319037151913114170349207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879358101275409446899471 1319037151913114170349207)
            ·
              refine ⟨1978555727869671255523811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319037151913114170349207 1978555727869671255523811)
              ·
                refine ⟨2967833591804506883285717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978555727869671255523811 2967833591804506883285717)
                ·
                  refine ⟨69558599807918130077009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2967833591804506883285717 69558599807918130077009)
                  ·
                    rfl

theorem cell23_1219184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 7].length) (baseStart_1219184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219184 prefixEnd_1219184 := by exact prefixLift 1219184
  have htrace : WordTrace (prefixWord ++ tailWord_1219184) baseStart_1219184 baseEnd_1219184 := by
    simpa [prefixWord, tailWord_1219184, baseEnd_1219184] using wordTrace_append hprefix tailTrace_1219184
  have hstable : (prefixWord ++ tailWord_1219184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219184).length < 2 ^ (prefixWord ++ tailWord_1219184).sum := by decide
  have hdescent : baseEnd_1219184 < baseStart_1219184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219301 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1219301 : Nat := 118140960795 + 1219301 * 2 ^ 59
def prefixEnd_1219301 : Nat := 4983230072969 + 3 ^ 40 * 1219301 * 2
def baseEnd_1219301 : Nat := 626087475507839212930043

theorem tailTrace_1219301 : CollatzResearch.WordTrace tailWord_1219301 prefixEnd_1219301 626087475507839212930043 := by
  unfold tailWord_1219301
  simp only [CollatzResearch.WordTrace]
  refine ⟨44471560955688191877073757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29647707303792127918049171 44471560955688191877073757)
  ·
    refine ⟨16676835358383071953902659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44471560955688191877073757 16676835358383071953902659)
    ·
      refine ⟨25015253037574607930853989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16676835358383071953902659 25015253037574607930853989)
      ·
        refine ⟨4690359944545238987035123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25015253037574607930853989 4690359944545238987035123)
        ·
          refine ⟨7035539916817858480552685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690359944545238987035123 7035539916817858480552685)
          ·
            refine ⟨2638327468806696930207257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7035539916817858480552685 2638327468806696930207257)
            ·
              refine ⟨1978745601605022697655443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638327468806696930207257 1978745601605022697655443)
              ·
                refine ⟨2968118402407534046483165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978745601605022697655443 2968118402407534046483165)
                ·
                  refine ⟨1113044400902825267431187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2968118402407534046483165 1113044400902825267431187)
                  ·
                    refine ⟨1669566601354237901146781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1113044400902825267431187 1669566601354237901146781)
                    ·
                      refine ⟨626087475507839212930043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1669566601354237901146781 626087475507839212930043)
                      ·
                        rfl

theorem cell23_1219301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1219301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219301 prefixEnd_1219301 := by exact prefixLift 1219301
  have htrace : WordTrace (prefixWord ++ tailWord_1219301) baseStart_1219301 baseEnd_1219301 := by
    simpa [prefixWord, tailWord_1219301, baseEnd_1219301] using wordTrace_append hprefix tailTrace_1219301
  have hstable : (prefixWord ++ tailWord_1219301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219301).length < 2 ^ (prefixWord ++ tailWord_1219301).sum := by decide
  have hdescent : baseEnd_1219301 < baseStart_1219301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219324 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_1219324 : Nat := 118140960795 + 1219324 * 2 ^ 59
def prefixEnd_1219324 : Nat := 4983230072969 + 3 ^ 40 * 1219324 * 2
def baseEnd_1219324 : Nat := 626099285562892622942437

theorem tailTrace_1219324 : CollatzResearch.WordTrace tailWord_1219324 prefixEnd_1219324 626099285562892622942437 := by
  unfold tailWord_1219324
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236199917302433402580513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29648266556403244536774017 22236199917302433402580513)
  ·
    refine ⟨16677149937976825051935385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22236199917302433402580513 16677149937976825051935385)
    ·
      refine ⟨12507862453482618788951539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16677149937976825051935385 12507862453482618788951539)
      ·
        refine ⟨18761793680223928183427309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12507862453482618788951539 18761793680223928183427309)
        ·
          refine ⟨7035672630083973068785241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18761793680223928183427309 7035672630083973068785241)
          ·
            refine ⟨5276754472562979801588931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7035672630083973068785241 5276754472562979801588931)
            ·
              refine ⟨7915131708844469702383397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276754472562979801588931 7915131708844469702383397)
              ·
                refine ⟨1484087195408338069196887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7915131708844469702383397 1484087195408338069196887)
                ·
                  refine ⟨2226130793112507103795331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484087195408338069196887 2226130793112507103795331)
                  ·
                    refine ⟨3339196189668760655692997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226130793112507103795331 3339196189668760655692997)
                    ·
                      refine ⟨626099285562892622942437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3339196189668760655692997 626099285562892622942437)
                      ·
                        rfl

theorem cell23_1219324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_1219324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219324 prefixEnd_1219324 := by exact prefixLift 1219324
  have htrace : WordTrace (prefixWord ++ tailWord_1219324) baseStart_1219324 baseEnd_1219324 := by
    simpa [prefixWord, tailWord_1219324, baseEnd_1219324] using wordTrace_append hprefix tailTrace_1219324
  have hstable : (prefixWord ++ tailWord_1219324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219324).length < 2 ^ (prefixWord ++ tailWord_1219324).sum := by decide
  have hdescent : baseEnd_1219324 < baseStart_1219324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219335 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1219335 : Nat := 118140960795 + 1219335 * 2 ^ 59
def prefixEnd_1219335 : Nat := 4983230072969 + 3 ^ 40 * 1219335 * 2
def baseEnd_1219335 : Nat := 626104933850092079904887

theorem tailTrace_1219335 : CollatzResearch.WordTrace tailWord_1219335 prefixEnd_1219335 626104933850092079904887 := by
  unfold tailWord_1219335
  simp only [CollatzResearch.WordTrace]
  refine ⟨44472801037565015683811459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29648534025043343789207639 44472801037565015683811459)
  ·
    refine ⟨66709201556347523525717189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44472801037565015683811459 66709201556347523525717189)
    ·
      refine ⟨12507975291815160661071973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66709201556347523525717189 12507975291815160661071973)
      ·
        refine ⟨2345245367215342623950995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12507975291815160661071973 2345245367215342623950995)
        ·
          refine ⟨3517868050823013935926493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345245367215342623950995 3517868050823013935926493)
          ·
            refine ⟨1319200519058630225972435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3517868050823013935926493 1319200519058630225972435)
            ·
              refine ⟨1978800778587945338958653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319200519058630225972435 1978800778587945338958653)
              ·
                refine ⟨742050291970479502109495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1978800778587945338958653 742050291970479502109495)
                ·
                  refine ⟨1113075437955719253164243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742050291970479502109495 1113075437955719253164243)
                  ·
                    refine ⟨1669613156933578879746365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1113075437955719253164243 1669613156933578879746365)
                    ·
                      refine ⟨626104933850092079904887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1669613156933578879746365 626104933850092079904887)
                      ·
                        rfl

theorem cell23_1219335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1219335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219335 prefixEnd_1219335 := by exact prefixLift 1219335
  have htrace : WordTrace (prefixWord ++ tailWord_1219335) baseStart_1219335 baseEnd_1219335 := by
    simpa [prefixWord, tailWord_1219335, baseEnd_1219335] using wordTrace_append hprefix tailTrace_1219335
  have hstable : (prefixWord ++ tailWord_1219335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219335).length < 2 ^ (prefixWord ++ tailWord_1219335).sum := by decide
  have hdescent : baseEnd_1219335 < baseStart_1219335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219337 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_1219337 : Nat := 118140960795 + 1219337 * 2 ^ 59
def prefixEnd_1219337 : Nat := 4983230072969 + 3 ^ 40 * 1219337 * 2
def baseEnd_1219337 : Nat := 626105960811401072079877

theorem tailTrace_1219337 : CollatzResearch.WordTrace tailWord_1219337 prefixEnd_1219337 626105960811401072079877 := by
  unfold tailWord_1219337
  simp only [CollatzResearch.WordTrace]
  refine ⟨44472873983557770025384265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29648582655705180016922843 44472873983557770025384265)
  ·
    refine ⟨33354655487668327519038199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44472873983557770025384265 33354655487668327519038199)
    ·
      refine ⟨50031983231502491278557299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33354655487668327519038199 50031983231502491278557299)
      ·
        refine ⟨75047974847253736917835949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50031983231502491278557299 75047974847253736917835949)
        ·
          refine ⟨28142990567720151344188481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75047974847253736917835949 28142990567720151344188481)
          ·
            refine ⟨21107242925790113508141361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28142990567720151344188481 21107242925790113508141361)
            ·
              refine ⟨15830432194342585131106021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21107242925790113508141361 15830432194342585131106021)
              ·
                refine ⟨2968206036439234712082379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15830432194342585131106021 2968206036439234712082379)
                ·
                  refine ⟨4452309054658852068123569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968206036439234712082379 4452309054658852068123569)
                  ·
                    refine ⟨3339231790994139051092677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4452309054658852068123569 3339231790994139051092677)
                    ·
                      refine ⟨626105960811401072079877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3339231790994139051092677 626105960811401072079877)
                      ·
                        rfl

theorem cell23_1219337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_1219337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219337 prefixEnd_1219337 := by exact prefixLift 1219337
  have htrace : WordTrace (prefixWord ++ tailWord_1219337) baseStart_1219337 baseEnd_1219337 := by
    simpa [prefixWord, tailWord_1219337, baseEnd_1219337] using wordTrace_append hprefix tailTrace_1219337
  have hstable : (prefixWord ++ tailWord_1219337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219337).length < 2 ^ (prefixWord ++ tailWord_1219337).sum := by decide
  have hdescent : baseEnd_1219337 < baseStart_1219337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219364 : List Nat := [2, 3, 1, 3, 3, 1, 2, 8]
def baseStart_1219364 : Nat := 118140960795 + 1219364 * 2 ^ 59
def prefixEnd_1219364 : Nat := 4983230072969 + 3 ^ 40 * 1219364 * 2
def baseEnd_1219364 : Nat := 23189623140336017275639

theorem tailTrace_1219364 : CollatzResearch.WordTrace tailWord_1219364 prefixEnd_1219364 23189623140336017275639 := by
  unfold tailWord_1219364
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236929377229976818308573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29649239169639969091078097 22236929377229976818308573)
  ·
    refine ⟨8338848516461241306865715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22236929377229976818308573 8338848516461241306865715)
    ·
      refine ⟨12508272774691861960298573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8338848516461241306865715 12508272774691861960298573)
      ·
        refine ⟨4690602290509448235111965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12508272774691861960298573 4690602290509448235111965)
        ·
          refine ⟨1758975858941043088166987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4690602290509448235111965 1758975858941043088166987)
          ·
            refine ⟨2638463788411564632250481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758975858941043088166987 2638463788411564632250481)
            ·
              refine ⟨1978847841308673474187861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638463788411564632250481 1978847841308673474187861)
              ·
                refine ⟨23189623140336017275639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1978847841308673474187861 23189623140336017275639)
                ·
                  rfl

theorem cell23_1219364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 8].length) (baseStart_1219364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219364 prefixEnd_1219364 := by exact prefixLift 1219364
  have htrace : WordTrace (prefixWord ++ tailWord_1219364) baseStart_1219364 baseEnd_1219364 := by
    simpa [prefixWord, tailWord_1219364, baseEnd_1219364] using wordTrace_append hprefix tailTrace_1219364
  have hstable : (prefixWord ++ tailWord_1219364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219364).length < 2 ^ (prefixWord ++ tailWord_1219364).sum := by decide
  have hdescent : baseEnd_1219364 < baseStart_1219364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219409 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 1, 2, 2]
def baseStart_1219409 : Nat := 118140960795 + 1219409 * 2 ^ 59
def prefixEnd_1219409 : Nat := 4983230072969 + 3 ^ 40 * 1219409 * 2
def baseEnd_1219409 : Nat := 626142931418524790379547

theorem tailTrace_1219409 : CollatzResearch.WordTrace tailWord_1219409 prefixEnd_1219409 626142931418524790379547 := by
  unfold tailWord_1219409
  simp only [CollatzResearch.WordTrace]
  refine ⟨44475500039296926322005281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29650333359531284214670187 44475500039296926322005281)
  ·
    refine ⟨33356625029472694741503961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44475500039296926322005281 33356625029472694741503961)
    ·
      refine ⟨25017468772104521056127971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33356625029472694741503961 25017468772104521056127971)
      ·
        refine ⟨37526203158156781584191957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25017468772104521056127971 37526203158156781584191957)
        ·
          refine ⟨879520386519299568379499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37526203158156781584191957 879520386519299568379499)
          ·
            refine ⟨1319280579778949352569249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879520386519299568379499 1319280579778949352569249)
            ·
              refine ⟨989460434834212014426937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319280579778949352569249 989460434834212014426937)
              ·
                refine ⟨742095326125659010820203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989460434834212014426937 742095326125659010820203)
                ·
                  refine ⟨1113142989188488516230305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742095326125659010820203 1113142989188488516230305)
                  ·
                    refine ⟨834857241891366387172729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113142989188488516230305 834857241891366387172729)
                    ·
                      refine ⟨626142931418524790379547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834857241891366387172729 626142931418524790379547)
                      ·
                        rfl

theorem cell23_1219409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_1219409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219409 prefixEnd_1219409 := by exact prefixLift 1219409
  have htrace : WordTrace (prefixWord ++ tailWord_1219409) baseStart_1219409 baseEnd_1219409 := by
    simpa [prefixWord, tailWord_1219409, baseEnd_1219409] using wordTrace_append hprefix tailTrace_1219409
  have hstable : (prefixWord ++ tailWord_1219409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219409).length < 2 ^ (prefixWord ++ tailWord_1219409).sum := by decide
  have hdescent : baseEnd_1219409 < baseStart_1219409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219431 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_1219431 : Nat := 118140960795 + 1219431 * 2 ^ 59
def prefixEnd_1219431 : Nat := 4983230072969 + 3 ^ 40 * 1219431 * 2
def baseEnd_1219431 : Nat := 626154227992923704304445

theorem tailTrace_1219431 : CollatzResearch.WordTrace tailWord_1219431 prefixEnd_1219431 626154227992923704304445 := by
  unfold tailWord_1219431
  simp only [CollatzResearch.WordTrace]
  refine ⟨44476302445217224079306147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29650868296811482719537431 44476302445217224079306147)
  ·
    refine ⟨66714453667825836118959221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44476302445217224079306147 66714453667825836118959221)
    ·
      refine ⟨6254480031358672136152427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66714453667825836118959221 6254480031358672136152427)
      ·
        refine ⟨9381720047038008204228641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254480031358672136152427 9381720047038008204228641)
        ·
          refine ⟨7036290035278506153171481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9381720047038008204228641 7036290035278506153171481)
          ·
            refine ⟨5277217526458879614878611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7036290035278506153171481 5277217526458879614878611)
            ·
              refine ⟨7915826289688319422317917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277217526458879614878611 7915826289688319422317917)
              ·
                refine ⟨2968434858633119783369219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7915826289688319422317917 2968434858633119783369219)
                ·
                  refine ⟨4452652287949679675053829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968434858633119783369219 4452652287949679675053829)
                  ·
                    refine ⟨834872303990564939072593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452652287949679675053829 834872303990564939072593)
                    ·
                      refine ⟨626154227992923704304445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834872303990564939072593 626154227992923704304445)
                      ·
                        rfl

theorem cell23_1219431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_1219431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219431 prefixEnd_1219431 := by exact prefixLift 1219431
  have htrace : WordTrace (prefixWord ++ tailWord_1219431) baseStart_1219431 baseEnd_1219431 := by
    simpa [prefixWord, tailWord_1219431, baseEnd_1219431] using wordTrace_append hprefix tailTrace_1219431
  have hstable : (prefixWord ++ tailWord_1219431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219431).length < 2 ^ (prefixWord ++ tailWord_1219431).sum := by decide
  have hdescent : baseEnd_1219431 < baseStart_1219431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219465 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 2, 2, 2]
def baseStart_1219465 : Nat := 118140960795 + 1219465 * 2 ^ 59
def prefixEnd_1219465 : Nat := 4983230072969 + 3 ^ 40 * 1219465 * 2
def baseEnd_1219465 : Nat := 626171686335176571279289

theorem tailTrace_1219465 : CollatzResearch.WordTrace tailWord_1219465 prefixEnd_1219465 626171686335176571279289 := by
  unfold tailWord_1219465
  simp only [CollatzResearch.WordTrace]
  refine ⟨44477542527094047886043849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29651695018062698590695899 44477542527094047886043849)
  ·
    refine ⟨33358156895320535914532887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44477542527094047886043849 33358156895320535914532887)
    ·
      refine ⟨50037235342980803871799331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33358156895320535914532887 50037235342980803871799331)
      ·
        refine ⟨75055853014471205807698997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50037235342980803871799331 75055853014471205807698997)
        ·
          refine ⟨7036486220106675544471781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75055853014471205807698997 7036486220106675544471781)
          ·
            refine ⟨1319341166270001664588459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7036486220106675544471781 1319341166270001664588459)
            ·
              refine ⟨1979011749405002496882689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319341166270001664588459 1979011749405002496882689)
              ·
                refine ⟨1484258812053751872662017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979011749405002496882689 1484258812053751872662017)
                ·
                  refine ⟨1113194109040313904496513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484258812053751872662017 1113194109040313904496513)
                  ·
                    refine ⟨834895581780235428372385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113194109040313904496513 834895581780235428372385)
                    ·
                      refine ⟨626171686335176571279289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834895581780235428372385 626171686335176571279289)
                      ·
                        rfl

theorem cell23_1219465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2, 2].length) (baseStart_1219465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219465 prefixEnd_1219465 := by exact prefixLift 1219465
  have htrace : WordTrace (prefixWord ++ tailWord_1219465) baseStart_1219465 baseEnd_1219465 := by
    simpa [prefixWord, tailWord_1219465, baseEnd_1219465] using wordTrace_append hprefix tailTrace_1219465
  have hstable : (prefixWord ++ tailWord_1219465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219465).length < 2 ^ (prefixWord ++ tailWord_1219465).sum := by decide
  have hdescent : baseEnd_1219465 < baseStart_1219465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219482 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_1219482 : Nat := 118140960795 + 1219482 * 2 ^ 59
def prefixEnd_1219482 : Nat := 4983230072969 + 3 ^ 40 * 1219482 * 2
def baseEnd_1219482 : Nat := 626180415506303004766711

theorem tailTrace_1219482 : CollatzResearch.WordTrace tailWord_1219482 prefixEnd_1219482 626180415506303004766711 := by
  unfold tailWord_1219482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119540642008114947353175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29652108378688306526275133 11119540642008114947353175)
  ·
    refine ⟨16679310963012172421029763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11119540642008114947353175 16679310963012172421029763)
    ·
      refine ⟨25018966444518258631544645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16679310963012172421029763 25018966444518258631544645)
      ·
        refine ⟨4691056208347173493414621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25018966444518258631544645 4691056208347173493414621)
        ·
          refine ⟨1759146078130190060030483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4691056208347173493414621 1759146078130190060030483)
          ·
            refine ⟨2638719117195285090045725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759146078130190060030483 2638719117195285090045725)
            ·
              refine ⟨989519668948231908767147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2638719117195285090045725 989519668948231908767147)
              ·
                refine ⟨1484279503422347863150721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989519668948231908767147 1484279503422347863150721)
                ·
                  refine ⟨1113209627566760897363041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484279503422347863150721 1113209627566760897363041)
                  ·
                    refine ⟨834907220675070673022281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113209627566760897363041 834907220675070673022281)
                    ·
                      refine ⟨626180415506303004766711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834907220675070673022281 626180415506303004766711)
                      ·
                        rfl

theorem cell23_1219482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_1219482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219482 prefixEnd_1219482 := by exact prefixLift 1219482
  have htrace : WordTrace (prefixWord ++ tailWord_1219482) baseStart_1219482 baseEnd_1219482 := by
    simpa [prefixWord, tailWord_1219482, baseEnd_1219482] using wordTrace_append hprefix tailTrace_1219482
  have hstable : (prefixWord ++ tailWord_1219482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219482).length < 2 ^ (prefixWord ++ tailWord_1219482).sum := by decide
  have hdescent : baseEnd_1219482 < baseStart_1219482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219497 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_1219497 : Nat := 118140960795 + 1219497 * 2 ^ 59
def prefixEnd_1219497 : Nat := 4983230072969 + 3 ^ 40 * 1219497 * 2
def baseEnd_1219497 : Nat := 208729372572040148693047

theorem tailTrace_1219497 : CollatzResearch.WordTrace tailWord_1219497 prefixEnd_1219497 208729372572040148693047 := by
  unfold tailWord_1219497
  simp only [CollatzResearch.WordTrace]
  refine ⟨44478709662978117351208745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29652473108652078234139163 44478709662978117351208745)
  ·
    refine ⟨33359032247233588013406559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44478709662978117351208745 33359032247233588013406559)
    ·
      refine ⟨50038548370850382020109839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33359032247233588013406559 50038548370850382020109839)
      ·
        refine ⟨75057822556275573030164759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50038548370850382020109839 75057822556275573030164759)
        ·
          refine ⟨112586733834413359545247139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75057822556275573030164759 112586733834413359545247139)
          ·
            refine ⟨168880100751620039317870709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112586733834413359545247139 168880100751620039317870709)
            ·
              refine ⟨15832509445464378686050379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168880100751620039317870709 15832509445464378686050379)
              ·
                refine ⟨23748764168196568029075569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15832509445464378686050379 23748764168196568029075569)
                ·
                  refine ⟨17811573126147426021806677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23748764168196568029075569 17811573126147426021806677)
                  ·
                    refine ⟨208729372572040148693047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17811573126147426021806677 208729372572040148693047)
                    ·
                      rfl

theorem cell23_1219497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_1219497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219497 prefixEnd_1219497 := by exact prefixLift 1219497
  have htrace : WordTrace (prefixWord ++ tailWord_1219497) baseStart_1219497 baseEnd_1219497 := by
    simpa [prefixWord, tailWord_1219497, baseEnd_1219497] using wordTrace_append hprefix tailTrace_1219497
  have hstable : (prefixWord ++ tailWord_1219497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219497).length < 2 ^ (prefixWord ++ tailWord_1219497).sum := by decide
  have hdescent : baseEnd_1219497 < baseStart_1219497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219505 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 5]
def baseStart_1219505 : Nat := 118140960795 + 1219505 * 2 ^ 59
def prefixEnd_1219505 : Nat := 4983230072969 + 3 ^ 40 * 1219505 * 2
def baseEnd_1219505 : Nat := 69576913951261823864345

theorem tailTrace_1219505 : CollatzResearch.WordTrace tailWord_1219505 prefixEnd_1219505 69576913951261823864345 := by
  unfold tailWord_1219505
  simp only [CollatzResearch.WordTrace]
  refine ⟨44479001446949134717499969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29652667631299423144999979 44479001446949134717499969)
  ·
    refine ⟨33359251085211851038124977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44479001446949134717499969 33359251085211851038124977)
    ·
      refine ⟨25019438313908888278593733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33359251085211851038124977 25019438313908888278593733)
      ·
        refine ⟨4691144683857916552236325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25019438313908888278593733 4691144683857916552236325)
        ·
          refine ⟨879589628223359353544311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4691144683857916552236325 879589628223359353544311)
          ·
            refine ⟨1319384442335039030316467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879589628223359353544311 1319384442335039030316467)
            ·
              refine ⟨1979076663502558545474701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319384442335039030316467 1979076663502558545474701)
              ·
                refine ⟨742153748813459454553013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1979076663502558545474701 742153748813459454553013)
                ·
                  refine ⟨69576913951261823864345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742153748813459454553013 69576913951261823864345)
                  ·
                    rfl

theorem cell23_1219505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 5].length) (baseStart_1219505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219505 prefixEnd_1219505 := by exact prefixLift 1219505
  have htrace : WordTrace (prefixWord ++ tailWord_1219505) baseStart_1219505 baseEnd_1219505 := by
    simpa [prefixWord, tailWord_1219505, baseEnd_1219505] using wordTrace_append hprefix tailTrace_1219505
  have hstable : (prefixWord ++ tailWord_1219505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219505).length < 2 ^ (prefixWord ++ tailWord_1219505).sum := by decide
  have hdescent : baseEnd_1219505 < baseStart_1219505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219531 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 3, 4]
def baseStart_1219531 : Nat := 118140960795 + 1219531 * 2 ^ 59
def prefixEnd_1219531 : Nat := 4983230072969 + 3 ^ 40 * 1219531 * 2
def baseEnd_1219531 : Nat := 208735192019457771017995

theorem tailTrace_1219531 : CollatzResearch.WordTrace tailWord_1219531 prefixEnd_1219531 208735192019457771017995 := by
  unfold tailWord_1219531
  simp only [CollatzResearch.WordTrace]
  refine ⟨44479949744854941157946447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29653299829903294105297631 44479949744854941157946447)
  ·
    refine ⟨66719924617282411736919671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44479949744854941157946447 66719924617282411736919671)
    ·
      refine ⟨100079886925923617605379507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66719924617282411736919671 100079886925923617605379507)
      ·
        refine ⟨150119830388885426408069261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100079886925923617605379507 150119830388885426408069261)
        ·
          refine ⟨56294936395832034903025973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150119830388885426408069261 56294936395832034903025973)
          ·
            refine ⟨5277650287109253272158685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56294936395832034903025973 5277650287109253272158685)
            ·
              refine ⟨1979118857665969977059507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5277650287109253272158685 1979118857665969977059507)
              ·
                refine ⟨2968678286498954965589261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979118857665969977059507 2968678286498954965589261)
                ·
                  refine ⟨1113254357437108112095973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2968678286498954965589261 1113254357437108112095973)
                  ·
                    refine ⟨208735192019457771017995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113254357437108112095973 208735192019457771017995)
                    ·
                      rfl

theorem cell23_1219531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 4].length) (baseStart_1219531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219531 prefixEnd_1219531 := by exact prefixLift 1219531
  have htrace : WordTrace (prefixWord ++ tailWord_1219531) baseStart_1219531 baseEnd_1219531 := by
    simpa [prefixWord, tailWord_1219531, baseEnd_1219531] using wordTrace_append hprefix tailTrace_1219531
  have hstable : (prefixWord ++ tailWord_1219531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219531).length < 2 ^ (prefixWord ++ tailWord_1219531).sum := by decide
  have hdescent : baseEnd_1219531 < baseStart_1219531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219533 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1219533 : Nat := 118140960795 + 1219533 * 2 ^ 59
def prefixEnd_1219533 : Nat := 4983230072969 + 3 ^ 40 * 1219533 * 2
def baseEnd_1219533 : Nat := 626206603019682305228977

theorem tailTrace_1219533 : CollatzResearch.WordTrace tailWord_1219533 prefixEnd_1219533 626206603019682305228977 := by
  unfold tailWord_1219533
  simp only [CollatzResearch.WordTrace]
  refine ⟨44480022690847695499519253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29653348460565130333012835 44480022690847695499519253)
  ·
    refine ⟨2085001063633485726539965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44480022690847695499519253 2085001063633485726539965)
    ·
      refine ⟨781875398862557147452487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2085001063633485726539965 781875398862557147452487)
      ·
        refine ⟨1172813098293835721178731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781875398862557147452487 1172813098293835721178731)
        ·
          refine ⟨1759219647440753581768097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172813098293835721178731 1759219647440753581768097)
          ·
            refine ⟨1319414735580565186326073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759219647440753581768097 1319414735580565186326073)
            ·
              refine ⟨989561051685423889744555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319414735580565186326073 989561051685423889744555)
              ·
                refine ⟨1484341577528135834616833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989561051685423889744555 1484341577528135834616833)
                ·
                  refine ⟨1113256183146101875962625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484341577528135834616833 1113256183146101875962625)
                  ·
                    refine ⟨834942137359576406971969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113256183146101875962625 834942137359576406971969)
                    ·
                      refine ⟨626206603019682305228977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834942137359576406971969 626206603019682305228977)
                      ·
                        rfl

theorem cell23_1219533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1219533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219533 prefixEnd_1219533 := by exact prefixLift 1219533
  have htrace : WordTrace (prefixWord ++ tailWord_1219533) baseStart_1219533 baseEnd_1219533 := by
    simpa [prefixWord, tailWord_1219533, baseEnd_1219533] using wordTrace_append hprefix tailTrace_1219533
  have hstable : (prefixWord ++ tailWord_1219533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219533).length < 2 ^ (prefixWord ++ tailWord_1219533).sum := by decide
  have hdescent : baseEnd_1219533 < baseStart_1219533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219581 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_1219581 : Nat := 118140960795 + 1219581 * 2 ^ 59
def prefixEnd_1219581 : Nat := 4983230072969 + 3 ^ 40 * 1219581 * 2
def baseEnd_1219581 : Nat := 626231250091098117428755

theorem tailTrace_1219581 : CollatzResearch.WordTrace tailWord_1219581 prefixEnd_1219581 626231250091098117428755 := by
  unfold tailWord_1219581
  simp only [CollatzResearch.WordTrace]
  refine ⟨44481773394673799697266597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29654515596449199798177731 44481773394673799697266597)
  ·
    refine ⟨8340332511501337443237487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44481773394673799697266597 8340332511501337443237487)
    ·
      refine ⟨12510498767252006164856231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8340332511501337443237487 12510498767252006164856231)
      ·
        refine ⟨18765748150878009247284347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12510498767252006164856231 18765748150878009247284347)
        ·
          refine ⟨28148622226317013870926521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18765748150878009247284347 28148622226317013870926521)
          ·
            refine ⟨21111466669737760403194891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28148622226317013870926521 21111466669737760403194891)
            ·
              refine ⟨31667200004606640604792337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21111466669737760403194891 31667200004606640604792337)
              ·
                refine ⟨23750400003454980453594253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31667200004606640604792337 23750400003454980453594253)
                ·
                  refine ⟨8906400001295617670097845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23750400003454980453594253 8906400001295617670097845)
                  ·
                    refine ⟨834975000121464156571673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8906400001295617670097845 834975000121464156571673)
                    ·
                      refine ⟨626231250091098117428755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834975000121464156571673 626231250091098117428755)
                      ·
                        rfl

theorem cell23_1219581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_1219581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219581 prefixEnd_1219581 := by exact prefixLift 1219581
  have htrace : WordTrace (prefixWord ++ tailWord_1219581) baseStart_1219581 baseEnd_1219581 := by
    simpa [prefixWord, tailWord_1219581, baseEnd_1219581] using wordTrace_append hprefix tailTrace_1219581
  have hstable : (prefixWord ++ tailWord_1219581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219581).length < 2 ^ (prefixWord ++ tailWord_1219581).sum := by decide
  have hdescent : baseEnd_1219581 < baseStart_1219581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219582 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1219582 : Nat := 118140960795 + 1219582 * 2 ^ 59
def prefixEnd_1219582 : Nat := 4983230072969 + 3 ^ 40 * 1219582 * 2
def baseEnd_1219582 : Nat := 208743921190584204505417

theorem tailTrace_1219582 : CollatzResearch.WordTrace tailWord_1219582 prefixEnd_1219582 208743921190584204505417 := by
  unfold tailWord_1219582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560226233458772108506625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29654539911780117912035333 5560226233458772108506625)
  ·
    refine ⟨4170169675094079081379969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5560226233458772108506625 4170169675094079081379969)
    ·
      refine ⟨3127627256320559311034977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4170169675094079081379969 3127627256320559311034977)
      ·
        refine ⟨2345720442240419483276233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3127627256320559311034977 2345720442240419483276233)
        ·
          refine ⟨1759290331680314612457175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345720442240419483276233 1759290331680314612457175)
          ·
            refine ⟨2638935497520471918685763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759290331680314612457175 2638935497520471918685763)
            ·
              refine ⟨3958403246280707878028645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638935497520471918685763 3958403246280707878028645)
              ·
                refine ⟨742200608677632727130371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3958403246280707878028645 742200608677632727130371)
                ·
                  refine ⟨1113300913016449090695557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742200608677632727130371 1113300913016449090695557)
                  ·
                    refine ⟨208743921190584204505417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113300913016449090695557 208743921190584204505417)
                    ·
                      rfl

theorem cell23_1219582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1219582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219582 prefixEnd_1219582 := by exact prefixLift 1219582
  have htrace : WordTrace (prefixWord ++ tailWord_1219582) baseStart_1219582 baseEnd_1219582 := by
    simpa [prefixWord, tailWord_1219582, baseEnd_1219582] using wordTrace_append hprefix tailTrace_1219582
  have hstable : (prefixWord ++ tailWord_1219582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219582).length < 2 ^ (prefixWord ++ tailWord_1219582).sum := by decide
  have hdescent : baseEnd_1219582 < baseStart_1219582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219615 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 2, 3, 2]
def baseStart_1219615 : Nat := 118140960795 + 1219615 * 2 ^ 59
def prefixEnd_1219615 : Nat := 4983230072969 + 3 ^ 40 * 1219615 * 2
def baseEnd_1219615 : Nat := 626248708433350984403599

theorem tailTrace_1219615 : CollatzResearch.WordTrace tailWord_1219615 prefixEnd_1219615 626248708433350984403599 := by
  unfold tailWord_1219615
  simp only [CollatzResearch.WordTrace]
  refine ⟨44483013476550623504004299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29655342317700415669336199 44483013476550623504004299)
  ·
    refine ⟨66724520214825935256006449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44483013476550623504004299 66724520214825935256006449)
    ·
      refine ⟨50043390161119451442004837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66724520214825935256006449 50043390161119451442004837)
      ·
        refine ⟨9383135655209897145375907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50043390161119451442004837 9383135655209897145375907)
        ·
          refine ⟨14074703482814845718063861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9383135655209897145375907 14074703482814845718063861)
          ·
            refine ⟨1319503451513891786068487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14074703482814845718063861 1319503451513891786068487)
            ·
              refine ⟨1979255177270837679102731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319503451513891786068487 1979255177270837679102731)
              ·
                refine ⟨2968882765906256518654097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979255177270837679102731 2968882765906256518654097)
                ·
                  refine ⟨2226662074429692388990573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968882765906256518654097 2226662074429692388990573)
                  ·
                    refine ⟨834998277911134645871465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226662074429692388990573 834998277911134645871465)
                    ·
                      refine ⟨626248708433350984403599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834998277911134645871465 626248708433350984403599)
                      ·
                        rfl

theorem cell23_1219615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_1219615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219615 prefixEnd_1219615 := by exact prefixLift 1219615
  have htrace : WordTrace (prefixWord ++ tailWord_1219615) baseStart_1219615 baseEnd_1219615 := by
    simpa [prefixWord, tailWord_1219615, baseEnd_1219615] using wordTrace_append hprefix tailTrace_1219615
  have hstable : (prefixWord ++ tailWord_1219615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219615).length < 2 ^ (prefixWord ++ tailWord_1219615).sum := by decide
  have hdescent : baseEnd_1219615 < baseStart_1219615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219621 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_1219621 : Nat := 118140960795 + 1219621 * 2 ^ 59
def prefixEnd_1219621 : Nat := 4983230072969 + 3 ^ 40 * 1219621 * 2
def baseEnd_1219621 : Nat := 208750596439092653642857

theorem tailTrace_1219621 : CollatzResearch.WordTrace tailWord_1219621 prefixEnd_1219621 208750596439092653642857 := by
  unfold tailWord_1219621
  simp only [CollatzResearch.WordTrace]
  refine ⟨44483232314528886528722717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29655488209685924352481811 44483232314528886528722717)
  ·
    refine ⟨16681212117948332448271019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44483232314528886528722717 16681212117948332448271019)
    ·
      refine ⟨25021818176922498672406529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16681212117948332448271019 25021818176922498672406529)
      ·
        refine ⟨18766363632691874004304897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25021818176922498672406529 18766363632691874004304897)
        ·
          refine ⟨14074772724518905503228673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18766363632691874004304897 14074772724518905503228673)
          ·
            refine ⟨10556079543389179127421505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14074772724518905503228673 10556079543389179127421505)
            ·
              refine ⟨7917059657541884345566129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10556079543389179127421505 7917059657541884345566129)
              ·
                refine ⟨5937794743156413259174597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917059657541884345566129 5937794743156413259174597)
                ·
                  refine ⟨1113336514341827486095237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5937794743156413259174597 1113336514341827486095237)
                  ·
                    refine ⟨208750596439092653642857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113336514341827486095237 208750596439092653642857)
                    ·
                      rfl

theorem cell23_1219621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_1219621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219621 prefixEnd_1219621 := by exact prefixLift 1219621
  have htrace : WordTrace (prefixWord ++ tailWord_1219621) baseStart_1219621 baseEnd_1219621 := by
    simpa [prefixWord, tailWord_1219621, baseEnd_1219621] using wordTrace_append hprefix tailTrace_1219621
  have hstable : (prefixWord ++ tailWord_1219621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219621).length < 2 ^ (prefixWord ++ tailWord_1219621).sum := by decide
  have hdescent : baseEnd_1219621 < baseStart_1219621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219628 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_1219628 : Nat := 118140960795 + 1219628 * 2 ^ 59
def prefixEnd_1219628 : Nat := 4983230072969 + 3 ^ 40 * 1219628 * 2
def baseEnd_1219628 : Nat := 626255383681859433541039

theorem tailTrace_1219628 : CollatzResearch.WordTrace tailWord_1219628 prefixEnd_1219628 626255383681859433541039 := by
  unfold tailWord_1219628
  simp only [CollatzResearch.WordTrace]
  refine ⟨22241743812751763362113769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29655658417002351149485025 22241743812751763362113769)
  ·
    refine ⟨16681307859563822521585327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22241743812751763362113769 16681307859563822521585327)
    ·
      refine ⟨25021961789345733782377991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16681307859563822521585327 25021961789345733782377991)
      ·
        refine ⟨37532942684018600673566987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25021961789345733782377991 37532942684018600673566987)
        ·
          refine ⟨56299414026027901010350481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37532942684018600673566987 56299414026027901010350481)
          ·
            refine ⟨42224560519520925757762861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56299414026027901010350481 42224560519520925757762861)
            ·
              refine ⟨15834210194820347159161073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42224560519520925757762861 15834210194820347159161073)
              ·
                refine ⟨11875657646115260369370805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15834210194820347159161073 11875657646115260369370805)
                ·
                  refine ⟨1113342904323305659628513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11875657646115260369370805 1113342904323305659628513)
                  ·
                    refine ⟨835007178242479244721385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113342904323305659628513 835007178242479244721385)
                    ·
                      refine ⟨626255383681859433541039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835007178242479244721385 626255383681859433541039)
                      ·
                        rfl

theorem cell23_1219628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_1219628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219628 prefixEnd_1219628 := by exact prefixLift 1219628
  have htrace : WordTrace (prefixWord ++ tailWord_1219628) baseStart_1219628 baseEnd_1219628 := by
    simpa [prefixWord, tailWord_1219628, baseEnd_1219628] using wordTrace_append hprefix tailTrace_1219628
  have hstable : (prefixWord ++ tailWord_1219628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219628).length < 2 ^ (prefixWord ++ tailWord_1219628).sum := by decide
  have hdescent : baseEnd_1219628 < baseStart_1219628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219634 : List Nat := [3, 2, 1, 1, 2, 2, 12]
def baseStart_1219634 : Nat := 118140960795 + 1219634 * 2 ^ 59
def prefixEnd_1219634 : Nat := 4983230072969 + 3 ^ 40 * 1219634 * 2
def baseEnd_1219634 : Nat := 7731585982293659383531

theorem tailTrace_1219634 : CollatzResearch.WordTrace tailWord_1219634 prefixEnd_1219634 7731585982293659383531 := by
  unfold tailWord_1219634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120926615870447437236489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29655804308987859832630637 11120926615870447437236489)
  ·
    refine ⟨8340694961902835577927367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11120926615870447437236489 8340694961902835577927367)
    ·
      refine ⟨12511042442854253366891051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8340694961902835577927367 12511042442854253366891051)
      ·
        refine ⟨18766563664281380050336577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12511042442854253366891051 18766563664281380050336577)
        ·
          refine ⟨14074922748211035037752433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18766563664281380050336577 14074922748211035037752433)
          ·
            refine ⟨10556192061158276278314325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14074922748211035037752433 10556192061158276278314325)
            ·
              refine ⟨7731585982293659383531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10556192061158276278314325 7731585982293659383531)
              ·
                rfl

theorem cell23_1219634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 12].length) (baseStart_1219634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219634 prefixEnd_1219634 := by exact prefixLift 1219634
  have htrace : WordTrace (prefixWord ++ tailWord_1219634) baseStart_1219634 baseEnd_1219634 := by
    simpa [prefixWord, tailWord_1219634, baseEnd_1219634] using wordTrace_append hprefix tailTrace_1219634
  have hstable : (prefixWord ++ tailWord_1219634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219634).length < 2 ^ (prefixWord ++ tailWord_1219634).sum := by decide
  have hdescent : baseEnd_1219634 < baseStart_1219634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219645 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_1219645 : Nat := 118140960795 + 1219645 * 2 ^ 59
def prefixEnd_1219645 : Nat := 4983230072969 + 3 ^ 40 * 1219645 * 2
def baseEnd_1219645 : Nat := 626264112852985867028461

theorem tailTrace_1219645 : CollatzResearch.WordTrace tailWord_1219645 prefixEnd_1219645 626264112852985867028461 := by
  unfold tailWord_1219645
  simp only [CollatzResearch.WordTrace]
  refine ⟨44484107666441938627596389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29656071777627959085064259 44484107666441938627596389)
  ·
    refine ⟨8340770187457863492674323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44484107666441938627596389 8340770187457863492674323)
    ·
      refine ⟨12511155281186795239011485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8340770187457863492674323 12511155281186795239011485)
      ·
        refine ⟨4691683230445048214629307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12511155281186795239011485 4691683230445048214629307)
        ·
          refine ⟨7037524845667572321943961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691683230445048214629307 7037524845667572321943961)
          ·
            refine ⟨5278143634250679241457971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7037524845667572321943961 5278143634250679241457971)
            ·
              refine ⟨7917215451376018862186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278143634250679241457971 7917215451376018862186957)
              ·
                refine ⟨2968955794266007073320109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7917215451376018862186957 2968955794266007073320109)
                ·
                  refine ⟨1113358422849752652495041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2968955794266007073320109 1113358422849752652495041)
                  ·
                    refine ⟨835018817137314489371281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113358422849752652495041 835018817137314489371281)
                    ·
                      refine ⟨626264112852985867028461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835018817137314489371281 626264112852985867028461)
                      ·
                        rfl

theorem cell23_1219645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_1219645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219645 prefixEnd_1219645 := by exact prefixLift 1219645
  have htrace : WordTrace (prefixWord ++ tailWord_1219645) baseStart_1219645 baseEnd_1219645 := by
    simpa [prefixWord, tailWord_1219645, baseEnd_1219645] using wordTrace_append hprefix tailTrace_1219645
  have hstable : (prefixWord ++ tailWord_1219645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219645).length < 2 ^ (prefixWord ++ tailWord_1219645).sum := by decide
  have hdescent : baseEnd_1219645 < baseStart_1219645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219655 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 2, 4]
def baseStart_1219655 : Nat := 118140960795 + 1219655 * 2 ^ 59
def prefixEnd_1219655 : Nat := 4983230072969 + 3 ^ 40 * 1219655 * 2
def baseEnd_1219655 : Nat := 208756415886510275967805

theorem tailTrace_1219655 : CollatzResearch.WordTrace tailWord_1219655 prefixEnd_1219655 208756415886510275967805 := by
  unfold tailWord_1219655
  simp only [CollatzResearch.WordTrace]
  refine ⟨44484472396405710335460419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29656314930937140223640279 44484472396405710335460419)
  ·
    refine ⟨66726708594608565503190629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44484472396405710335460419 66726708594608565503190629)
    ·
      refine ⟨12511257861489106031848243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66726708594608565503190629 12511257861489106031848243)
      ·
        refine ⟨18766886792233659047772365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12511257861489106031848243 18766886792233659047772365)
        ·
          refine ⟨7037582547087622142914637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18766886792233659047772365 7037582547087622142914637)
          ·
            refine ⟨2639093455157858303592989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7037582547087622142914637 2639093455157858303592989)
            ·
              refine ⟨989660045684196863847371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2639093455157858303592989 989660045684196863847371)
              ·
                refine ⟨1484490068526295295771057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989660045684196863847371 1484490068526295295771057)
                ·
                  refine ⟨1113367551394721471828293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484490068526295295771057 1113367551394721471828293)
                  ·
                    refine ⟨208756415886510275967805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113367551394721471828293 208756415886510275967805)
                    ·
                      rfl

theorem cell23_1219655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_1219655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219655 prefixEnd_1219655 := by exact prefixLift 1219655
  have htrace : WordTrace (prefixWord ++ tailWord_1219655) baseStart_1219655 baseEnd_1219655 := by
    simpa [prefixWord, tailWord_1219655, baseEnd_1219655] using wordTrace_append hprefix tailTrace_1219655
  have hstable : (prefixWord ++ tailWord_1219655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219655).length < 2 ^ (prefixWord ++ tailWord_1219655).sum := by decide
  have hdescent : baseEnd_1219655 < baseStart_1219655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219664 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_1219664 : Nat := 118140960795 + 1219664 * 2 ^ 59
def prefixEnd_1219664 : Nat := 4983230072969 + 3 ^ 40 * 1219664 * 2
def baseEnd_1219664 : Nat := 208757956328473764230291

theorem tailTrace_1219664 : CollatzResearch.WordTrace tailWord_1219664 prefixEnd_1219664 208757956328473764230291 := by
  unfold tailWord_1219664
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242400326686552436269023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29656533768915403248358697 22242400326686552436269023)
  ·
    refine ⟨33363600490029828654403535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22242400326686552436269023 33363600490029828654403535)
    ·
      refine ⟨50045400735044742981605303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33363600490029828654403535 50045400735044742981605303)
      ·
        refine ⟨75068101102567114472407955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50045400735044742981605303 75068101102567114472407955)
        ·
          refine ⟨112602151653850671708611933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75068101102567114472407955 112602151653850671708611933)
          ·
            refine ⟨42225806870194001890729475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112602151653850671708611933 42225806870194001890729475)
            ·
              refine ⟨63338710305291002836094213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42225806870194001890729475 63338710305291002836094213)
              ·
                refine ⟨11876008182242063031767665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63338710305291002836094213 11876008182242063031767665)
                ·
                  refine ⟨8907006136681547273825749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11876008182242063031767665 8907006136681547273825749)
                  ·
                    refine ⟨208757956328473764230291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8907006136681547273825749 208757956328473764230291)
                    ·
                      rfl

theorem cell23_1219664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_1219664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219664 prefixEnd_1219664 := by exact prefixLift 1219664
  have htrace : WordTrace (prefixWord ++ tailWord_1219664) baseStart_1219664 baseEnd_1219664 := by
    simpa [prefixWord, tailWord_1219664, baseEnd_1219664] using wordTrace_append hprefix tailTrace_1219664
  have hstable : (prefixWord ++ tailWord_1219664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219664).length < 2 ^ (prefixWord ++ tailWord_1219664).sum := by decide
  have hdescent : baseEnd_1219664 < baseStart_1219664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219721 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_1219721 : Nat := 118140960795 + 1219721 * 2 ^ 59
def prefixEnd_1219721 : Nat := 4983230072969 + 3 ^ 40 * 1219721 * 2
def baseEnd_1219721 : Nat := 626303137382727569678111

theorem tailTrace_1219721 : CollatzResearch.WordTrace tailWord_1219721 prefixEnd_1219721 626303137382727569678111 := by
  unfold tailWord_1219721
  simp only [CollatzResearch.WordTrace]
  refine ⟨44486879614166603607363017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29657919742777735738242011 44486879614166603607363017)
  ·
    refine ⟨33365159710624952705522263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44486879614166603607363017 33365159710624952705522263)
    ·
      refine ⟨50047739565937429058283395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33365159710624952705522263 50047739565937429058283395)
      ·
        refine ⟨75071609348906143587425093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50047739565937429058283395 75071609348906143587425093)
        ·
          refine ⟨14075926752919901922642205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75071609348906143587425093 14075926752919901922642205)
          ·
            refine ⟨5278472532344963220990827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14075926752919901922642205 5278472532344963220990827)
            ·
              refine ⟨7917708798517444831486241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278472532344963220990827 7917708798517444831486241)
              ·
                refine ⟨5938281598888083623614681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917708798517444831486241 5938281598888083623614681)
                ·
                  refine ⟨4453711199166062717711011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5938281598888083623614681 4453711199166062717711011)
                  ·
                    refine ⟨6680566798749094076566517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453711199166062717711011 6680566798749094076566517)
                    ·
                      refine ⟨626303137382727569678111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6680566798749094076566517 626303137382727569678111)
                      ·
                        rfl

theorem cell23_1219721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_1219721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219721 prefixEnd_1219721 := by exact prefixLift 1219721
  have htrace : WordTrace (prefixWord ++ tailWord_1219721) baseStart_1219721 baseEnd_1219721 := by
    simpa [prefixWord, tailWord_1219721, baseEnd_1219721] using wordTrace_append hprefix tailTrace_1219721
  have hstable : (prefixWord ++ tailWord_1219721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219721).length < 2 ^ (prefixWord ++ tailWord_1219721).sum := by decide
  have hdescent : baseEnd_1219721 < baseStart_1219721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219735 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_1219735 : Nat := 118140960795 + 1219735 * 2 ^ 59
def prefixEnd_1219735 : Nat := 4983230072969 + 3 ^ 40 * 1219735 * 2
def baseEnd_1219735 : Nat := 626310326111890514903047

theorem tailTrace_1219735 : CollatzResearch.WordTrace tailWord_1219735 prefixEnd_1219735 626310326111890514903047 := by
  unfold tailWord_1219735
  simp only [CollatzResearch.WordTrace]
  refine ⟨44487390236115883998372659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29658260157410589332248439 44487390236115883998372659)
  ·
    refine ⟨66731085354173825997558989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44487390236115883998372659 66731085354173825997558989)
    ·
      refine ⟨25024157007815184749084621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66731085354173825997558989 25024157007815184749084621)
      ·
        refine ⟨9384058877930694280906733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25024157007815184749084621 9384058877930694280906733)
        ·
          refine ⟨3519022079224010355340025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9384058877930694280906733 3519022079224010355340025)
          ·
            refine ⟨2639266559418007766505019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3519022079224010355340025 2639266559418007766505019)
            ·
              refine ⟨3958899839127011649757529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639266559418007766505019 3958899839127011649757529)
              ·
                refine ⟨2969174879345258737318147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958899839127011649757529 2969174879345258737318147)
                ·
                  refine ⟨4453762319017888105977221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969174879345258737318147 4453762319017888105977221)
                  ·
                    refine ⟨835080434815854019870729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453762319017888105977221 835080434815854019870729)
                    ·
                      refine ⟨626310326111890514903047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835080434815854019870729 626310326111890514903047)
                      ·
                        rfl

theorem cell23_1219735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_1219735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219735 prefixEnd_1219735 := by exact prefixLift 1219735
  have htrace : WordTrace (prefixWord ++ tailWord_1219735) baseStart_1219735 baseEnd_1219735 := by
    simpa [prefixWord, tailWord_1219735, baseEnd_1219735] using wordTrace_append hprefix tailTrace_1219735
  have hstable : (prefixWord ++ tailWord_1219735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219735).length < 2 ^ (prefixWord ++ tailWord_1219735).sum := by decide
  have hdescent : baseEnd_1219735 < baseStart_1219735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219738 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1219738 : Nat := 118140960795 + 1219738 * 2 ^ 59
def prefixEnd_1219738 : Nat := 4983230072969 + 3 ^ 40 * 1219738 * 2
def baseEnd_1219738 : Nat := 626311866553854003165533

theorem tailTrace_1219738 : CollatzResearch.WordTrace tailWord_1219738 prefixEnd_1219738 626311866553854003165533 := by
  unfold tailWord_1219738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11121874913776253877682967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29658333103403343673821245 11121874913776253877682967)
  ·
    refine ⟨16682812370664380816524451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11121874913776253877682967 16682812370664380816524451)
    ·
      refine ⟨25024218555996571224786677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16682812370664380816524451 25024218555996571224786677)
      ·
        refine ⟨2346020489624678552323751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25024218555996571224786677 2346020489624678552323751)
        ·
          refine ⟨3519030734437017828485627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346020489624678552323751 3519030734437017828485627)
          ·
            refine ⟨5278546101655526742728441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519030734437017828485627 5278546101655526742728441)
            ·
              refine ⟨3958909576241645057046331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278546101655526742728441 3958909576241645057046331)
              ·
                refine ⟨5938364364362467585569497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958909576241645057046331 5938364364362467585569497)
                ·
                  refine ⟨4453773273271850689177123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5938364364362467585569497 4453773273271850689177123)
                  ·
                    refine ⟨6680659909907776033765685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453773273271850689177123 6680659909907776033765685)
                    ·
                      refine ⟨626311866553854003165533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6680659909907776033765685 626311866553854003165533)
                      ·
                        rfl

theorem cell23_1219738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1219738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219738 prefixEnd_1219738 := by exact prefixLift 1219738
  have htrace : WordTrace (prefixWord ++ tailWord_1219738) baseStart_1219738 baseEnd_1219738 := by
    simpa [prefixWord, tailWord_1219738, baseEnd_1219738] using wordTrace_append hprefix tailTrace_1219738
  have hstable : (prefixWord ++ tailWord_1219738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219738).length < 2 ^ (prefixWord ++ tailWord_1219738).sum := by decide
  have hdescent : baseEnd_1219738 < baseStart_1219738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219852 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_1219852 : Nat := 118140960795 + 1219852 * 2 ^ 59
def prefixEnd_1219852 : Nat := 4983230072969 + 3 ^ 40 * 1219852 * 2
def baseEnd_1219852 : Nat := 208790134449488852380003

theorem tailTrace_1219852 : CollatzResearch.WordTrace tailWord_1219852 prefixEnd_1219852 208790134449488852380003 := by
  unfold tailWord_1219852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22245828788346006490190905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29661105051128008653587873 22245828788346006490190905)
  ·
    refine ⟨16684371591259504867643179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22245828788346006490190905 16684371591259504867643179)
    ·
      refine ⟨25026557386889257301464769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16684371591259504867643179 25026557386889257301464769)
      ·
        refine ⟨18769918040166942976098577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25026557386889257301464769 18769918040166942976098577)
        ·
          refine ⟨14077438530125207232073933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18769918040166942976098577 14077438530125207232073933)
          ·
            refine ⟨5279039448796952712027725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14077438530125207232073933 5279039448796952712027725)
            ·
              refine ⟨1979639793298857267010397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5279039448796952712027725 1979639793298857267010397)
              ·
                refine ⟨742364922487071475128899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1979639793298857267010397 742364922487071475128899)
                ·
                  refine ⟨1113547383730607212693349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742364922487071475128899 1113547383730607212693349)
                  ·
                    refine ⟨208790134449488852380003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113547383730607212693349 208790134449488852380003)
                    ·
                      rfl

theorem cell23_1219852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_1219852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219852 prefixEnd_1219852 := by exact prefixLift 1219852
  have htrace : WordTrace (prefixWord ++ tailWord_1219852) baseStart_1219852 baseEnd_1219852 := by
    simpa [prefixWord, tailWord_1219852, baseEnd_1219852] using wordTrace_append hprefix tailTrace_1219852
  have hstable : (prefixWord ++ tailWord_1219852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219852).length < 2 ^ (prefixWord ++ tailWord_1219852).sum := by decide
  have hdescent : baseEnd_1219852 < baseStart_1219852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219882 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_1219882 : Nat := 118140960795 + 1219882 * 2 ^ 59
def prefixEnd_1219882 : Nat := 4983230072969 + 3 ^ 40 * 1219882 * 2
def baseEnd_1219882 : Nat := 69598423085344604418319

theorem tailTrace_1219882 : CollatzResearch.WordTrace tailWord_1219882 prefixEnd_1219882 69598423085344604418319 := by
  unfold tailWord_1219882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11123187941645832025993475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29661834511055552069315933 11123187941645832025993475)
  ·
    refine ⟨16684781912468748038990213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11123187941645832025993475 16684781912468748038990213)
    ·
      refine ⟨3128396608587890257310665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16684781912468748038990213 3128396608587890257310665)
      ·
        refine ⟨2346297456440917692982999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3128396608587890257310665 2346297456440917692982999)
        ·
          refine ⟨3519446184661376539474499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346297456440917692982999 3519446184661376539474499)
          ·
            refine ⟨5279169276992064809211749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519446184661376539474499 5279169276992064809211749)
            ·
              refine ⟨989844239436012151727203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5279169276992064809211749 989844239436012151727203)
              ·
                refine ⟨1484766359154018227590805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989844239436012151727203 1484766359154018227590805)
                ·
                  refine ⟨69598423085344604418319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1484766359154018227590805 69598423085344604418319)
                  ·
                    rfl

theorem cell23_1219882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_1219882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219882 prefixEnd_1219882 := by exact prefixLift 1219882
  have htrace : WordTrace (prefixWord ++ tailWord_1219882) baseStart_1219882 baseEnd_1219882 := by
    simpa [prefixWord, tailWord_1219882, baseEnd_1219882] using wordTrace_append hprefix tailTrace_1219882
  have hstable : (prefixWord ++ tailWord_1219882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219882).length < 2 ^ (prefixWord ++ tailWord_1219882).sum := by decide
  have hdescent : baseEnd_1219882 < baseStart_1219882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219892 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1219892 : Nat := 118140960795 + 1219892 * 2 ^ 59
def prefixEnd_1219892 : Nat := 4983230072969 + 3 ^ 40 * 1219892 * 2
def baseEnd_1219892 : Nat := 626390942574646400639825

theorem tailTrace_1219892 : CollatzResearch.WordTrace tailWord_1219892 prefixEnd_1219892 626390942574646400639825 := by
  unfold tailWord_1219892
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246558248273549905918965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29662077664364733207891953 22246558248273549905918965)
  ·
    refine ⟨2085614835775645303679903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22246558248273549905918965 2085614835775645303679903)
    ·
      refine ⟨3128422253663467955519855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085614835775645303679903 3128422253663467955519855)
      ·
        refine ⟨4692633380495201933279783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128422253663467955519855 4692633380495201933279783)
        ·
          refine ⟨7038950070742802899919675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692633380495201933279783 7038950070742802899919675)
          ·
            refine ⟨10558425106114204349879513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038950070742802899919675 10558425106114204349879513)
            ·
              refine ⟨7918818829585653262409635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10558425106114204349879513 7918818829585653262409635)
              ·
                refine ⟨11878228244378479893614453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918818829585653262409635 11878228244378479893614453)
                ·
                  refine ⟨1113583897910482490026355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11878228244378479893614453 1113583897910482490026355)
                  ·
                    refine ⟨1670375846865723735039533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1113583897910482490026355 1670375846865723735039533)
                    ·
                      refine ⟨626390942574646400639825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670375846865723735039533 626390942574646400639825)
                      ·
                        rfl

theorem cell23_1219892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1219892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219892 prefixEnd_1219892 := by exact prefixLift 1219892
  have htrace : WordTrace (prefixWord ++ tailWord_1219892) baseStart_1219892 baseEnd_1219892 := by
    simpa [prefixWord, tailWord_1219892, baseEnd_1219892] using wordTrace_append hprefix tailTrace_1219892
  have hstable : (prefixWord ++ tailWord_1219892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219892).length < 2 ^ (prefixWord ++ tailWord_1219892).sum := by decide
  have hdescent : baseEnd_1219892 < baseStart_1219892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219928 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1219928 : Nat := 118140960795 + 1219928 * 2 ^ 59
def prefixEnd_1219928 : Nat := 4983230072969 + 3 ^ 40 * 1219928 * 2
def baseEnd_1219928 : Nat := 626409427878208259789659

theorem tailTrace_1219928 : CollatzResearch.WordTrace tailWord_1219928 prefixEnd_1219928 626409427878208259789659 := by
  unfold tailWord_1219928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247214762208338980074219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29662953016277785306765625 22247214762208338980074219)
  ·
    refine ⟨33370822143312508470111329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22247214762208338980074219 33370822143312508470111329)
    ·
      refine ⟨25028116607484381352583497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33370822143312508470111329 25028116607484381352583497)
      ·
        refine ⟨18771087455613286014437623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25028116607484381352583497 18771087455613286014437623)
        ·
          refine ⟨28156631183419929021656435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18771087455613286014437623 28156631183419929021656435)
          ·
            refine ⟨42234946775129893532484653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28156631183419929021656435 42234946775129893532484653)
            ·
              refine ⟨15838105040673710074681745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42234946775129893532484653 15838105040673710074681745)
              ·
                refine ⟨11878578780505282556011309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15838105040673710074681745 11878578780505282556011309)
                ·
                  refine ⟨4454467042689480958504241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11878578780505282556011309 4454467042689480958504241)
                  ·
                    refine ⟨3340850282017110718878181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454467042689480958504241 3340850282017110718878181)
                    ·
                      refine ⟨626409427878208259789659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3340850282017110718878181 626409427878208259789659)
                      ·
                        rfl

theorem cell23_1219928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1219928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219928 prefixEnd_1219928 := by exact prefixLift 1219928
  have htrace : WordTrace (prefixWord ++ tailWord_1219928) baseStart_1219928 baseEnd_1219928 := by
    simpa [prefixWord, tailWord_1219928, baseEnd_1219928] using wordTrace_append hprefix tailTrace_1219928
  have hstable : (prefixWord ++ tailWord_1219928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219928).length < 2 ^ (prefixWord ++ tailWord_1219928).sum := by decide
  have hdescent : baseEnd_1219928 < baseStart_1219928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219949 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1219949 : Nat := 118140960795 + 1219949 * 2 ^ 59
def prefixEnd_1219949 : Nat := 4983230072969 + 3 ^ 40 * 1219949 * 2
def baseEnd_1219949 : Nat := 626420210971952677627063

theorem tailTrace_1219949 : CollatzResearch.WordTrace tailWord_1219949 prefixEnd_1219949 626420210971952677627063 := by
  unfold tailWord_1219949
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495195457340598546662901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29663463638227065697775267 44495195457340598546662901)
  ·
    refine ⟨4171424574125681113749647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44495195457340598546662901 4171424574125681113749647)
    ·
      refine ⟨6257136861188521670624471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4171424574125681113749647 6257136861188521670624471)
      ·
        refine ⟨9385705291782782505936707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257136861188521670624471 9385705291782782505936707)
        ·
          refine ⟨14078557937674173758905061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385705291782782505936707 14078557937674173758905061)
          ·
            refine ⟨2639729613313907579794699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14078557937674173758905061 2639729613313907579794699)
            ·
              refine ⟨3959594419970861369692049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639729613313907579794699 3959594419970861369692049)
              ·
                refine ⟨2969695814978146027269037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3959594419970861369692049 2969695814978146027269037)
                ·
                  refine ⟨1113635930616804760225889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2969695814978146027269037 1113635930616804760225889)
                  ·
                    refine ⟨835226947962603570169417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113635930616804760225889 835226947962603570169417)
                    ·
                      refine ⟨626420210971952677627063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835226947962603570169417 626420210971952677627063)
                      ·
                        rfl

theorem cell23_1219949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1219949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219949 prefixEnd_1219949 := by exact prefixLift 1219949
  have htrace : WordTrace (prefixWord ++ tailWord_1219949) baseStart_1219949 baseEnd_1219949 := by
    simpa [prefixWord, tailWord_1219949, baseEnd_1219949] using wordTrace_append hprefix tailTrace_1219949
  have hstable : (prefixWord ++ tailWord_1219949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219949).length < 2 ^ (prefixWord ++ tailWord_1219949).sum := by decide
  have hdescent : baseEnd_1219949 < baseStart_1219949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219965 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1219965 : Nat := 118140960795 + 1219965 * 2 ^ 59
def prefixEnd_1219965 : Nat := 4983230072969 + 3 ^ 40 * 1219965 * 2
def baseEnd_1219965 : Nat := 626428426662424615026989

theorem tailTrace_1219965 : CollatzResearch.WordTrace tailWord_1219965 prefixEnd_1219965 626428426662424615026989 := by
  unfold tailWord_1219965
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495779025282633279245349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29663852683521755519496899 44495779025282633279245349)
  ·
    refine ⟨8342958567240493739858503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44495779025282633279245349 8342958567240493739858503)
    ·
      refine ⟨12514437850860740609787755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8342958567240493739858503 12514437850860740609787755)
      ·
        refine ⟨18771656776291110914681633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12514437850860740609787755 18771656776291110914681633)
        ·
          refine ⟨14078742582218333186011225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18771656776291110914681633 14078742582218333186011225)
          ·
            refine ⟨10559056936663749889508419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14078742582218333186011225 10559056936663749889508419)
            ·
              refine ⟨15838585404995624834262629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10559056936663749889508419 15838585404995624834262629)
              ·
                refine ⟨2969734763436679656424243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15838585404995624834262629 2969734763436679656424243)
                ·
                  refine ⟨4454602145155019484636365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969734763436679656424243 4454602145155019484636365)
                  ·
                    refine ⟨1670475804433132306738637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4454602145155019484636365 1670475804433132306738637)
                    ·
                      refine ⟨626428426662424615026989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670475804433132306738637 626428426662424615026989)
                      ·
                        rfl

theorem cell23_1219965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1219965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219965 prefixEnd_1219965 := by exact prefixLift 1219965
  have htrace : WordTrace (prefixWord ++ tailWord_1219965) baseStart_1219965 baseEnd_1219965 := by
    simpa [prefixWord, tailWord_1219965, baseEnd_1219965] using wordTrace_append hprefix tailTrace_1219965
  have hstable : (prefixWord ++ tailWord_1219965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219965).length < 2 ^ (prefixWord ++ tailWord_1219965).sum := by decide
  have hdescent : baseEnd_1219965 < baseStart_1219965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219966 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1219966 : Nat := 118140960795 + 1219966 * 2 ^ 59
def prefixEnd_1219966 : Nat := 4983230072969 + 3 ^ 40 * 1219966 * 2
def baseEnd_1219966 : Nat := 626428940143079111114485

theorem tailTrace_1219966 : CollatzResearch.WordTrace tailWord_1219966 prefixEnd_1219966 626428940143079111114485 := by
  unfold tailWord_1219966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5561976937284876306253969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29663876998852673633354501 5561976937284876306253969)
  ·
    refine ⟨4171482702963657229690477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5561976937284876306253969 4171482702963657229690477)
    ·
      refine ⟨1564306013611371461133929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4171482702963657229690477 1564306013611371461133929)
      ·
        refine ⟨1173229510208528595850447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1564306013611371461133929 1173229510208528595850447)
        ·
          refine ⟨1759844265312792893775671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173229510208528595850447 1759844265312792893775671)
          ·
            refine ⟨2639766397969189340663507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759844265312792893775671 2639766397969189340663507)
            ·
              refine ⟨3959649596953784010995261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639766397969189340663507 3959649596953784010995261)
              ·
                refine ⟨1484868598857669004123223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959649596953784010995261 1484868598857669004123223)
                ·
                  refine ⟨2227302898286503506184835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484868598857669004123223 2227302898286503506184835)
                  ·
                    refine ⟨3340954347429755259277253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227302898286503506184835 3340954347429755259277253)
                    ·
                      refine ⟨626428940143079111114485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3340954347429755259277253 626428940143079111114485)
                      ·
                        rfl

theorem cell23_1219966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1219966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219966 prefixEnd_1219966 := by exact prefixLift 1219966
  have htrace : WordTrace (prefixWord ++ tailWord_1219966) baseStart_1219966 baseEnd_1219966 := by
    simpa [prefixWord, tailWord_1219966, baseEnd_1219966] using wordTrace_append hprefix tailTrace_1219966
  have hstable : (prefixWord ++ tailWord_1219966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219966).length < 2 ^ (prefixWord ++ tailWord_1219966).sum := by decide
  have hdescent : baseEnd_1219966 < baseStart_1219966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219969 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1219969 : Nat := 118140960795 + 1219969 * 2 ^ 59
def prefixEnd_1219969 : Nat := 4983230072969 + 3 ^ 40 * 1219969 * 2
def baseEnd_1219969 : Nat := 626430480585042599376971

theorem tailTrace_1219969 : CollatzResearch.WordTrace tailWord_1219969 prefixEnd_1219969 626430480585042599376971 := by
  unfold tailWord_1219969
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495924917268141962390961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29663949944845427974927307 44495924917268141962390961)
  ·
    refine ⟨33371943687951106471793221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44495924917268141962390961 33371943687951106471793221)
    ·
      refine ⟨6257239441490832463461229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33371943687951106471793221 6257239441490832463461229)
      ·
        refine ⟨2346464790559062173797961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6257239441490832463461229 2346464790559062173797961)
        ·
          refine ⟨1759848592919296630348471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346464790559062173797961 1759848592919296630348471)
          ·
            refine ⟨2639772889378944945522707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759848592919296630348471 2639772889378944945522707)
            ·
              refine ⟨3959659334068417418284061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639772889378944945522707 3959659334068417418284061)
              ·
                refine ⟨1484872250275656531856523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959659334068417418284061 1484872250275656531856523)
                ·
                  refine ⟨2227308375413484797784785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484872250275656531856523 2227308375413484797784785)
                  ·
                    refine ⟨1670481281560113598338589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2227308375413484797784785 1670481281560113598338589)
                    ·
                      refine ⟨626430480585042599376971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670481281560113598338589 626430480585042599376971)
                      ·
                        rfl

theorem cell23_1219969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1219969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219969 prefixEnd_1219969 := by exact prefixLift 1219969
  have htrace : WordTrace (prefixWord ++ tailWord_1219969) baseStart_1219969 baseEnd_1219969 := by
    simpa [prefixWord, tailWord_1219969, baseEnd_1219969] using wordTrace_append hprefix tailTrace_1219969
  have hstable : (prefixWord ++ tailWord_1219969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219969).length < 2 ^ (prefixWord ++ tailWord_1219969).sum := by decide
  have hdescent : baseEnd_1219969 < baseStart_1219969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219996 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1219996 : Nat := 118140960795 + 1219996 * 2 ^ 59
def prefixEnd_1219996 : Nat := 4983230072969 + 3 ^ 40 * 1219996 * 2
def baseEnd_1219996 : Nat := 626444344562713993739347

theorem tailTrace_1219996 : CollatzResearch.WordTrace tailWord_1219996 prefixEnd_1219996 626444344562713993739347 := by
  unfold tailWord_1219996
  simp only [CollatzResearch.WordTrace]
  refine ⟨22248454844085162786811921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29664606458780217049082561 22248454844085162786811921)
  ·
    refine ⟨16686341133063872090108941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22248454844085162786811921 16686341133063872090108941)
    ·
      refine ⟨6257377924898952033790853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16686341133063872090108941 6257377924898952033790853)
      ·
        refine ⟨1173258360918553506335785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6257377924898952033790853 1173258360918553506335785)
        ·
          refine ⟨879943770688915129751839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173258360918553506335785 879943770688915129751839)
          ·
            refine ⟨1319915656033372694627759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879943770688915129751839 1319915656033372694627759)
            ·
              refine ⟨1979873484050059041941639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319915656033372694627759 1979873484050059041941639)
              ·
                refine ⟨2969810226075088562912459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979873484050059041941639 2969810226075088562912459)
                ·
                  refine ⟨4454715339112632844368689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969810226075088562912459 4454715339112632844368689)
                  ·
                    refine ⟨3341036504334474633276517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454715339112632844368689 3341036504334474633276517)
                    ·
                      refine ⟨626444344562713993739347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3341036504334474633276517 626444344562713993739347)
                      ·
                        rfl

theorem cell23_1219996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1219996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1219996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1219996 prefixEnd_1219996 := by exact prefixLift 1219996
  have htrace : WordTrace (prefixWord ++ tailWord_1219996) baseStart_1219996 baseEnd_1219996 := by
    simpa [prefixWord, tailWord_1219996, baseEnd_1219996] using wordTrace_append hprefix tailTrace_1219996
  have hstable : (prefixWord ++ tailWord_1219996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219996).length < 2 ^ (prefixWord ++ tailWord_1219996).sum := by decide
  have hdescent : baseEnd_1219996 < baseStart_1219996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220034 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1220034 : Nat := 118140960795 + 1220034 * 2 ^ 59
def prefixEnd_1220034 : Nat := 4983230072969 + 3 ^ 40 * 1220034 * 2
def baseEnd_1220034 : Nat := 626463856827584845064173

theorem tailTrace_1220034 : CollatzResearch.WordTrace tailWord_1220034 prefixEnd_1220034 626463856827584845064173 := by
  unfold tailWord_1220034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124573915508164515876789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29665530441355105375671437 11124573915508164515876789)
  ·
    refine ⟨1042928804578890423363449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11124573915508164515876789 1042928804578890423363449)
    ·
      refine ⟨782196603434167817522587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1042928804578890423363449 782196603434167817522587)
      ·
        refine ⟨1173294905151251726283881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782196603434167817522587 1173294905151251726283881)
        ·
          refine ⟨879971178863438794712911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173294905151251726283881 879971178863438794712911)
          ·
            refine ⟨1319956768295158192069367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879971178863438794712911 1319956768295158192069367)
            ·
              refine ⟨1979935152442737288104051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319956768295158192069367 1979935152442737288104051)
              ·
                refine ⟨2969902728664105932156077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979935152442737288104051 2969902728664105932156077)
                ·
                  refine ⟨1113713523249039724558529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2969902728664105932156077 1113713523249039724558529)
                  ·
                    refine ⟨835285142436779793418897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113713523249039724558529 835285142436779793418897)
                    ·
                      refine ⟨626463856827584845064173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835285142436779793418897 626463856827584845064173)
                      ·
                        rfl

theorem cell23_1220034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1220034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220034 prefixEnd_1220034 := by exact prefixLift 1220034
  have htrace : WordTrace (prefixWord ++ tailWord_1220034) baseStart_1220034 baseEnd_1220034 := by
    simpa [prefixWord, tailWord_1220034, baseEnd_1220034] using wordTrace_append hprefix tailTrace_1220034
  have hstable : (prefixWord ++ tailWord_1220034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220034).length < 2 ^ (prefixWord ++ tailWord_1220034).sum := by decide
  have hdescent : baseEnd_1220034 < baseStart_1220034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220039 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_1220039 : Nat := 118140960795 + 1220039 * 2 ^ 59
def prefixEnd_1220039 : Nat := 4983230072969 + 3 ^ 40 * 1220039 * 2
def baseEnd_1220039 : Nat := 626466424230857325501649

theorem tailTrace_1220039 : CollatzResearch.WordTrace tailWord_1220039 prefixEnd_1220039 626466424230857325501649 := by
  unfold tailWord_1220039
  simp only [CollatzResearch.WordTrace]
  refine ⟨44498478027014543917439171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29665652018009695944959447 44498478027014543917439171)
  ·
    refine ⟨66747717040521815876158757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44498478027014543917439171 66747717040521815876158757)
    ·
      refine ⟨12515196945097840476779767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66747717040521815876158757 12515196945097840476779767)
      ·
        refine ⟨18772795417646760715169651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12515196945097840476779767 18772795417646760715169651)
        ·
          refine ⟨28159193126470141072754477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18772795417646760715169651 28159193126470141072754477)
          ·
            refine ⟨10559697422426302902282929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28159193126470141072754477 10559697422426302902282929)
            ·
              refine ⟨7919773066819727176712197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10559697422426302902282929 7919773066819727176712197)
              ·
                refine ⟨1484957450028698845633537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7919773066819727176712197 1484957450028698845633537)
                ·
                  refine ⟨1113718087521524134225153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484957450028698845633537 1113718087521524134225153)
                  ·
                    refine ⟨835288565641143100668865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113718087521524134225153 835288565641143100668865)
                    ·
                      refine ⟨626466424230857325501649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835288565641143100668865 626466424230857325501649)
                      ·
                        rfl

theorem cell23_1220039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_1220039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220039 prefixEnd_1220039 := by exact prefixLift 1220039
  have htrace : WordTrace (prefixWord ++ tailWord_1220039) baseStart_1220039 baseEnd_1220039 := by
    simpa [prefixWord, tailWord_1220039, baseEnd_1220039] using wordTrace_append hprefix tailTrace_1220039
  have hstable : (prefixWord ++ tailWord_1220039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220039).length < 2 ^ (prefixWord ++ tailWord_1220039).sum := by decide
  have hdescent : baseEnd_1220039 < baseStart_1220039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220055 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_1220055 : Nat := 118140960795 + 1220055 * 2 ^ 59
def prefixEnd_1220055 : Nat := 4983230072969 + 3 ^ 40 * 1220055 * 2
def baseEnd_1220055 : Nat := 626474639921329262901575

theorem tailTrace_1220055 : CollatzResearch.WordTrace tailWord_1220055 prefixEnd_1220055 626474639921329262901575 := by
  unfold tailWord_1220055
  simp only [CollatzResearch.WordTrace]
  refine ⟨44499061594956578650021619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29666041063304385766681079 44499061594956578650021619)
  ·
    refine ⟨66748592392434867975032429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44499061594956578650021619 66748592392434867975032429)
    ·
      refine ⟨25030722147163075490637161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66748592392434867975032429 25030722147163075490637161)
      ·
        refine ⟨18773041610372306617977871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25030722147163075490637161 18773041610372306617977871)
        ·
          refine ⟨28159562415558459926966807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18773041610372306617977871 28159562415558459926966807)
          ·
            refine ⟨42239343623337689890450211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28159562415558459926966807 42239343623337689890450211)
            ·
              refine ⟨63359015435006534835675317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42239343623337689890450211 63359015435006534835675317)
              ·
                refine ⟨5939907697031862640844561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63359015435006534835675317 5939907697031862640844561)
                ·
                  refine ⟨4454930772773896980633421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5939907697031862640844561 4454930772773896980633421)
                  ·
                    refine ⟨1670599039790211367737533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4454930772773896980633421 1670599039790211367737533)
                    ·
                      refine ⟨626474639921329262901575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670599039790211367737533 626474639921329262901575)
                      ·
                        rfl

theorem cell23_1220055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_1220055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220055 prefixEnd_1220055 := by exact prefixLift 1220055
  have htrace : WordTrace (prefixWord ++ tailWord_1220055) baseStart_1220055 baseEnd_1220055 := by
    simpa [prefixWord, tailWord_1220055, baseEnd_1220055] using wordTrace_append hprefix tailTrace_1220055
  have hstable : (prefixWord ++ tailWord_1220055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220055).length < 2 ^ (prefixWord ++ tailWord_1220055).sum := by decide
  have hdescent : baseEnd_1220055 < baseStart_1220055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220056 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_1220056 : Nat := 118140960795 + 1220056 * 2 ^ 59
def prefixEnd_1220056 : Nat := 4983230072969 + 3 ^ 40 * 1220056 * 2
def baseEnd_1220056 : Nat := 626475153401983758989071

theorem tailTrace_1220056 : CollatzResearch.WordTrace tailWord_1220056 prefixEnd_1220056 626475153401983758989071 := by
  unfold tailWord_1220056
  simp only [CollatzResearch.WordTrace]
  refine ⟨22249549033976477910404011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29666065378635303880538681 22249549033976477910404011)
  ·
    refine ⟨33374323550964716865606017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22249549033976477910404011 33374323550964716865606017)
    ·
      refine ⟨25030742663223537649204513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33374323550964716865606017 25030742663223537649204513)
      ·
        refine ⟨18773056997417653236903385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25030742663223537649204513 18773056997417653236903385)
        ·
          refine ⟨14079792748063239927677539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18773056997417653236903385 14079792748063239927677539)
          ·
            refine ⟨21119689122094859891516309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14079792748063239927677539 21119689122094859891516309)
            ·
              refine ⟨989985427598196557414827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21119689122094859891516309 989985427598196557414827)
              ·
                refine ⟨1484978141397294836122241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989985427598196557414827 1484978141397294836122241)
                ·
                  refine ⟨1113733606047971127091681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484978141397294836122241 1113733606047971127091681)
                  ·
                    refine ⟨835300204535978345318761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113733606047971127091681 835300204535978345318761)
                    ·
                      refine ⟨626475153401983758989071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835300204535978345318761 626475153401983758989071)
                      ·
                        rfl

theorem cell23_1220056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_1220056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220056 prefixEnd_1220056 := by exact prefixLift 1220056
  have htrace : WordTrace (prefixWord ++ tailWord_1220056) baseStart_1220056 baseEnd_1220056 := by
    simpa [prefixWord, tailWord_1220056, baseEnd_1220056] using wordTrace_append hprefix tailTrace_1220056
  have hstable : (prefixWord ++ tailWord_1220056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220056).length < 2 ^ (prefixWord ++ tailWord_1220056).sum := by decide
  have hdescent : baseEnd_1220056 < baseStart_1220056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220095 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_1220095 : Nat := 118140960795 + 1220095 * 2 ^ 59
def prefixEnd_1220095 : Nat := 4983230072969 + 3 ^ 40 * 1220095 * 2
def baseEnd_1220095 : Nat := 626495179147509106401391

theorem tailTrace_1220095 : CollatzResearch.WordTrace tailWord_1220095 prefixEnd_1220095 626495179147509106401391 := by
  unfold tailWord_1220095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44500520514811665481477739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29667013676541110320985159 44500520514811665481477739)
  ·
    refine ⟨66750780772217498222216609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44500520514811665481477739 66750780772217498222216609)
    ·
      refine ⟨50063085579163123666662457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66750780772217498222216609 50063085579163123666662457)
      ·
        refine ⟨37547314184372342749996843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50063085579163123666662457 37547314184372342749996843)
        ·
          refine ⟨56320971276558514124995265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37547314184372342749996843 56320971276558514124995265)
          ·
            refine ⟨42240728457418885593746449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56320971276558514124995265 42240728457418885593746449)
            ·
              refine ⟨31680546343064164195309837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42240728457418885593746449 31680546343064164195309837)
              ·
                refine ⟨11880204878649061573241189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31680546343064164195309837 11880204878649061573241189)
                ·
                  refine ⟨2227538414746699044982723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11880204878649061573241189 2227538414746699044982723)
                  ·
                    refine ⟨3341307622120048567474085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227538414746699044982723 3341307622120048567474085)
                    ·
                      refine ⟨626495179147509106401391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3341307622120048567474085 626495179147509106401391)
                      ·
                        rfl

theorem cell23_1220095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_1220095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220095 prefixEnd_1220095 := by exact prefixLift 1220095
  have htrace : WordTrace (prefixWord ++ tailWord_1220095) baseStart_1220095 baseEnd_1220095 := by
    simpa [prefixWord, tailWord_1220095, baseEnd_1220095] using wordTrace_append hprefix tailTrace_1220095
  have hstable : (prefixWord ++ tailWord_1220095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220095).length < 2 ^ (prefixWord ++ tailWord_1220095).sum := by decide
  have hdescent : baseEnd_1220095 < baseStart_1220095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220129 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1220129 : Nat := 118140960795 + 1220129 * 2 ^ 59
def prefixEnd_1220129 : Nat := 4983230072969 + 3 ^ 40 * 1220129 * 2
def baseEnd_1220129 : Nat := 626512637489761973376235

theorem tailTrace_1220129 : CollatzResearch.WordTrace tailWord_1220129 prefixEnd_1220129 626512637489761973376235 := by
  unfold tailWord_1220129
  simp only [CollatzResearch.WordTrace]
  refine ⟨44501760596688489288215441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29667840397792326192143627 44501760596688489288215441)
  ·
    refine ⟨33376320447516366966161581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44501760596688489288215441 33376320447516366966161581)
    ·
      refine ⟨12516120167818637612310593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33376320447516366966161581 12516120167818637612310593)
      ·
        refine ⟨9387090125863978209232945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12516120167818637612310593 9387090125863978209232945)
        ·
          refine ⟨7040317594397983656924709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9387090125863978209232945 7040317594397983656924709)
          ·
            refine ⟨1320059548949621935673383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7040317594397983656924709 1320059548949621935673383)
            ·
              refine ⟨1980089323424432903510075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320059548949621935673383 1980089323424432903510075)
              ·
                refine ⟨2970133985136649355265113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980089323424432903510075 2970133985136649355265113)
                ·
                  refine ⟨2227600488852487016448835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970133985136649355265113 2227600488852487016448835)
                  ·
                    refine ⟨3341400733278730524673253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227600488852487016448835 3341400733278730524673253)
                    ·
                      refine ⟨626512637489761973376235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3341400733278730524673253 626512637489761973376235)
                      ·
                        rfl

theorem cell23_1220129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1220129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220129 prefixEnd_1220129 := by exact prefixLift 1220129
  have htrace : WordTrace (prefixWord ++ tailWord_1220129) baseStart_1220129 baseEnd_1220129 := by
    simpa [prefixWord, tailWord_1220129, baseEnd_1220129] using wordTrace_append hprefix tailTrace_1220129
  have hstable : (prefixWord ++ tailWord_1220129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220129).length < 2 ^ (prefixWord ++ tailWord_1220129).sum := by decide
  have hdescent : baseEnd_1220129 < baseStart_1220129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220142 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1220142 : Nat := 118140960795 + 1220142 * 2 ^ 59
def prefixEnd_1220142 : Nat := 4983230072969 + 3 ^ 40 * 1220142 * 2
def baseEnd_1220142 : Nat := 626519312738270422513675

theorem tailTrace_1220142 : CollatzResearch.WordTrace tailWord_1220142 prefixEnd_1220142 626519312738270422513675 := by
  unfold tailWord_1220142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562779343205174063554835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29668156497094261672292453 5562779343205174063554835)
  ·
    refine ⟨8344169014807761095332253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5562779343205174063554835 8344169014807761095332253)
    ·
      refine ⟨3129063380552910410749595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8344169014807761095332253 3129063380552910410749595)
      ·
        refine ⟨4693595070829365616124393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129063380552910410749595 4693595070829365616124393)
        ·
          refine ⟨3520196303122024212093295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693595070829365616124393 3520196303122024212093295)
          ·
            refine ⟨5280294454683036318139943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520196303122024212093295 5280294454683036318139943)
            ·
              refine ⟨7920441682024554477209915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280294454683036318139943 7920441682024554477209915)
              ·
                refine ⟨11880662523036831715814873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920441682024554477209915 11880662523036831715814873)
                ·
                  refine ⟨8910496892277623786861155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11880662523036831715814873 8910496892277623786861155)
                  ·
                    refine ⟨13365745338416435680291733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8910496892277623786861155 13365745338416435680291733)
                    ·
                      refine ⟨626519312738270422513675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13365745338416435680291733 626519312738270422513675)
                      ·
                        rfl

theorem cell23_1220142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1220142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220142 prefixEnd_1220142 := by exact prefixLift 1220142
  have htrace : WordTrace (prefixWord ++ tailWord_1220142) baseStart_1220142 baseEnd_1220142 := by
    simpa [prefixWord, tailWord_1220142, baseEnd_1220142] using wordTrace_append hprefix tailTrace_1220142
  have hstable : (prefixWord ++ tailWord_1220142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220142).length < 2 ^ (prefixWord ++ tailWord_1220142).sum := by decide
  have hdescent : baseEnd_1220142 < baseStart_1220142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220152 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 6]
def baseStart_1220152 : Nat := 118140960795 + 1220152 * 2 ^ 59
def prefixEnd_1220152 : Nat := 4983230072969 + 3 ^ 40 * 1220152 * 2
def baseEnd_1220152 : Nat := 69613827504979487043181

theorem tailTrace_1220152 : CollatzResearch.WordTrace tailWord_1220152 prefixEnd_1220152 69613827504979487043181 := by
  unfold tailWord_1220152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22251299737802582108151355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29668399650403442810868473 22251299737802582108151355)
  ·
    refine ⟨33376949606703873162227033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22251299737802582108151355 33376949606703873162227033)
    ·
      refine ⟨25032712205027904871670275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33376949606703873162227033 25032712205027904871670275)
      ·
        refine ⟨37549068307541857307505413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25032712205027904871670275 37549068307541857307505413)
        ·
          refine ⟨7040450307664098245157265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37549068307541857307505413 7040450307664098245157265)
          ·
            refine ⟨5280337730748073683867949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7040450307664098245157265 5280337730748073683867949)
            ·
              refine ⟨1980126649030527631450481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5280337730748073683867949 1980126649030527631450481)
              ·
                refine ⟨1485094986772895723587861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980126649030527631450481 1485094986772895723587861)
                ·
                  refine ⟨69613827504979487043181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1485094986772895723587861 69613827504979487043181)
                  ·
                    rfl

theorem cell23_1220152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_1220152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220152 prefixEnd_1220152 := by exact prefixLift 1220152
  have htrace : WordTrace (prefixWord ++ tailWord_1220152) baseStart_1220152 baseEnd_1220152 := by
    simpa [prefixWord, tailWord_1220152, baseEnd_1220152] using wordTrace_append hprefix tailTrace_1220152
  have hstable : (prefixWord ++ tailWord_1220152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220152).length < 2 ^ (prefixWord ++ tailWord_1220152).sum := by decide
  have hdescent : baseEnd_1220152 < baseStart_1220152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220185 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_1220185 : Nat := 118140960795 + 1220185 * 2 ^ 59
def prefixEnd_1220185 : Nat := 4983230072969 + 3 ^ 40 * 1220185 * 2
def baseEnd_1220185 : Nat := 626541392406413754275977

theorem tailTrace_1220185 : CollatzResearch.WordTrace tailWord_1220185 prefixEnd_1220185 626541392406413754275977 := by
  unfold tailWord_1220185
  simp only [CollatzResearch.WordTrace]
  refine ⟨44503803084485610852254009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29669202056323740568169339 44503803084485610852254009)
  ·
    refine ⟨33377852313364208139190507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44503803084485610852254009 33377852313364208139190507)
    ·
      refine ⟨50066778470046312208785761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33377852313364208139190507 50066778470046312208785761)
      ·
        refine ⟨37550083852534734156589321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50066778470046312208785761 37550083852534734156589321)
        ·
          refine ⟨28162562889401050617441991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37550083852534734156589321 28162562889401050617441991)
          ·
            refine ⟨42243844334101575926162987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28162562889401050617441991 42243844334101575926162987)
            ·
              refine ⟨63365766501152363889244481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42243844334101575926162987 63365766501152363889244481)
              ·
                refine ⟨47524324875864272916933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63365766501152363889244481 47524324875864272916933361)
                ·
                  refine ⟨35643243656898204687700021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47524324875864272916933361 35643243656898204687700021)
                  ·
                    refine ⟨3341554092834206689471877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35643243656898204687700021 3341554092834206689471877)
                    ·
                      refine ⟨626541392406413754275977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3341554092834206689471877 626541392406413754275977)
                      ·
                        rfl

theorem cell23_1220185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_1220185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220185 prefixEnd_1220185 := by exact prefixLift 1220185
  have htrace : WordTrace (prefixWord ++ tailWord_1220185) baseStart_1220185 baseEnd_1220185 := by
    simpa [prefixWord, tailWord_1220185, baseEnd_1220185] using wordTrace_append hprefix tailTrace_1220185
  have hstable : (prefixWord ++ tailWord_1220185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220185).length < 2 ^ (prefixWord ++ tailWord_1220185).sum := by decide
  have hdescent : baseEnd_1220185 < baseStart_1220185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220213 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1220213 : Nat := 118140960795 + 1220213 * 2 ^ 59
def prefixEnd_1220213 : Nat := 4983230072969 + 3 ^ 40 * 1220213 * 2
def baseEnd_1220213 : Nat := 626555769864739644725849

theorem tailTrace_1220213 : CollatzResearch.WordTrace tailWord_1220213 prefixEnd_1220213 626555769864739644725849 := by
  unfold tailWord_1220213
  simp only [CollatzResearch.WordTrace]
  refine ⟨44504824328384171634273293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29669882885589447756182195 44504824328384171634273293)
  ·
    refine ⟨16689309123144064362852485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44504824328384171634273293 16689309123144064362852485)
    ·
      refine ⟨3129245460589512068034841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16689309123144064362852485 3129245460589512068034841)
      ·
        refine ⟨2346934095442134051026131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3129245460589512068034841 2346934095442134051026131)
        ·
          refine ⟨3520401143163201076539197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346934095442134051026131 3520401143163201076539197)
          ·
            refine ⟨1320150428686200403702199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3520401143163201076539197 1320150428686200403702199)
            ·
              refine ⟨1980225643029300605553299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320150428686200403702199 1980225643029300605553299)
              ·
                refine ⟨2970338464543950908329949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980225643029300605553299 2970338464543950908329949)
                ·
                  refine ⟨1113876924203981590623731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2970338464543950908329949 1113876924203981590623731)
                  ·
                    refine ⟨1670815386305972385935597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1113876924203981590623731 1670815386305972385935597)
                    ·
                      refine ⟨626555769864739644725849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670815386305972385935597 626555769864739644725849)
                      ·
                        rfl

theorem cell23_1220213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1220213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220213 prefixEnd_1220213 := by exact prefixLift 1220213
  have htrace : WordTrace (prefixWord ++ tailWord_1220213) baseStart_1220213 baseEnd_1220213 := by
    simpa [prefixWord, tailWord_1220213, baseEnd_1220213] using wordTrace_append hprefix tailTrace_1220213
  have hstable : (prefixWord ++ tailWord_1220213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220213).length < 2 ^ (prefixWord ++ tailWord_1220213).sum := by decide
  have hdescent : baseEnd_1220213 < baseStart_1220213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220229 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_1220229 : Nat := 118140960795 + 1220229 * 2 ^ 59
def prefixEnd_1220229 : Nat := 4983230072969 + 3 ^ 40 * 1220229 * 2
def baseEnd_1220229 : Nat := 208854661851737194041925

theorem tailTrace_1220229 : CollatzResearch.WordTrace tailWord_1220229 prefixEnd_1220229 208854661851737194041925 := by
  unfold tailWord_1220229
  simp only [CollatzResearch.WordTrace]
  refine ⟨44505407896326206366855741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29670271930884137577903827 44505407896326206366855741)
  ·
    refine ⟨16689527961122327387570903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44505407896326206366855741 16689527961122327387570903)
    ·
      refine ⟨25034291941683491081356355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16689527961122327387570903 25034291941683491081356355)
      ·
        refine ⟨37551437912525236622034533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25034291941683491081356355 37551437912525236622034533)
        ·
          refine ⟨7040894608598481866631475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37551437912525236622034533 7040894608598481866631475)
          ·
            refine ⟨10561341912897722799947213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040894608598481866631475 10561341912897722799947213)
            ·
              refine ⟨3960503217336646049980205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10561341912897722799947213 3960503217336646049980205)
              ·
                refine ⟨1485188706501242268742577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3960503217336646049980205 1485188706501242268742577)
                ·
                  refine ⟨1113891529875931701556933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485188706501242268742577 1113891529875931701556933)
                  ·
                    refine ⟨208854661851737194041925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113891529875931701556933 208854661851737194041925)
                    ·
                      rfl

theorem cell23_1220229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_1220229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220229 prefixEnd_1220229 := by exact prefixLift 1220229
  have htrace : WordTrace (prefixWord ++ tailWord_1220229) baseStart_1220229 baseEnd_1220229 := by
    simpa [prefixWord, tailWord_1220229, baseEnd_1220229] using wordTrace_append hprefix tailTrace_1220229
  have hstable : (prefixWord ++ tailWord_1220229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220229).length < 2 ^ (prefixWord ++ tailWord_1220229).sum := by decide
  have hdescent : baseEnd_1220229 < baseStart_1220229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220253 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_1220253 : Nat := 118140960795 + 1220253 * 2 ^ 59
def prefixEnd_1220253 : Nat := 4983230072969 + 3 ^ 40 * 1220253 * 2
def baseEnd_1220253 : Nat := 626576309090919488225665

theorem tailTrace_1220253 : CollatzResearch.WordTrace tailWord_1220253 prefixEnd_1220253 626576309090919488225665 := by
  unfold tailWord_1220253
  simp only [CollatzResearch.WordTrace]
  refine ⟨44506283248239258465729413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29670855498826172310486275 44506283248239258465729413)
  ·
    refine ⟨8344928109044860962324265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44506283248239258465729413 8344928109044860962324265)
    ·
      refine ⟨6258696081783645721743199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8344928109044860962324265 6258696081783645721743199)
      ·
        refine ⟨9388044122675468582614799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258696081783645721743199 9388044122675468582614799)
        ·
          refine ⟨14082066184013202873922199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388044122675468582614799 14082066184013202873922199)
          ·
            refine ⟨21123099276019804310883299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14082066184013202873922199 21123099276019804310883299)
            ·
              refine ⟨31684648914029706466324949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21123099276019804310883299 31684648914029706466324949)
              ·
                refine ⟨742608958922571245304491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31684648914029706466324949 742608958922571245304491)
                ·
                  refine ⟨1113913438383856867956737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742608958922571245304491 1113913438383856867956737)
                  ·
                    refine ⟨835435078787892650967553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113913438383856867956737 835435078787892650967553)
                    ·
                      refine ⟨626576309090919488225665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835435078787892650967553 626576309090919488225665)
                      ·
                        rfl

theorem cell23_1220253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_1220253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220253 prefixEnd_1220253 := by exact prefixLift 1220253
  have htrace : WordTrace (prefixWord ++ tailWord_1220253) baseStart_1220253 baseEnd_1220253 := by
    simpa [prefixWord, tailWord_1220253, baseEnd_1220253] using wordTrace_append hprefix tailTrace_1220253
  have hstable : (prefixWord ++ tailWord_1220253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220253).length < 2 ^ (prefixWord ++ tailWord_1220253).sum := by decide
  have hdescent : baseEnd_1220253 < baseStart_1220253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220269 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1220269 : Nat := 118140960795 + 1220269 * 2 ^ 59
def prefixEnd_1220269 : Nat := 4983230072969 + 3 ^ 40 * 1220269 * 2
def baseEnd_1220269 : Nat := 626584524781391425625591

theorem tailTrace_1220269 : CollatzResearch.WordTrace tailWord_1220269 prefixEnd_1220269 626584524781391425625591 := by
  unfold tailWord_1220269
  simp only [CollatzResearch.WordTrace]
  refine ⟨44506866816181293198311861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29671244544120862132207907 44506866816181293198311861)
  ·
    refine ⟨4172518764016996237341737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44506866816181293198311861 4172518764016996237341737)
    ·
      refine ⟨3129389073012747178006303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4172518764016996237341737 3129389073012747178006303)
      ·
        refine ⟨4694083609519120767009455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129389073012747178006303 4694083609519120767009455)
        ·
          refine ⟨7041125414278681150514183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694083609519120767009455 7041125414278681150514183)
          ·
            refine ⟨10561688121418021725771275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041125414278681150514183 10561688121418021725771275)
            ·
              refine ⟨15842532182127032588656913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10561688121418021725771275 15842532182127032588656913)
              ·
                refine ⟨11881899136595274441492685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15842532182127032588656913 11881899136595274441492685)
                ·
                  refine ⟨4455712176223227915559757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11881899136595274441492685 4455712176223227915559757)
                  ·
                    refine ⟨1670892066083710468334909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4455712176223227915559757 1670892066083710468334909)
                    ·
                      refine ⟨626584524781391425625591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670892066083710468334909 626584524781391425625591)
                      ·
                        rfl

theorem cell23_1220269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1220269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220269 prefixEnd_1220269 := by exact prefixLift 1220269
  have htrace : WordTrace (prefixWord ++ tailWord_1220269) baseStart_1220269 baseEnd_1220269 := by
    simpa [prefixWord, tailWord_1220269, baseEnd_1220269] using wordTrace_append hprefix tailTrace_1220269
  have hstable : (prefixWord ++ tailWord_1220269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220269).length < 2 ^ (prefixWord ++ tailWord_1220269).sum := by decide
  have hdescent : baseEnd_1220269 < baseStart_1220269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220286 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1220286 : Nat := 118140960795 + 1220286 * 2 ^ 59
def prefixEnd_1220286 : Nat := 4983230072969 + 3 ^ 40 * 1220286 * 2
def baseEnd_1220286 : Nat := 626593253952517859113013

theorem tailTrace_1220286 : CollatzResearch.WordTrace tailWord_1220286 prefixEnd_1220286 626593253952517859113013 := by
  unfold tailWord_1220286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563435857139963137710089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29671657904746470067787141 5563435857139963137710089)
  ·
    refine ⟨4172576892854972353282567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5563435857139963137710089 4172576892854972353282567)
    ·
      refine ⟨6258865339282458529923851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172576892854972353282567 6258865339282458529923851)
      ·
        refine ⟨9388298008923687794885777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258865339282458529923851 9388298008923687794885777)
        ·
          refine ⟨7041223506692765846164333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9388298008923687794885777 7041223506692765846164333)
          ·
            refine ⟨2640458815009787192311625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7041223506692765846164333 2640458815009787192311625)
            ·
              refine ⟨1980344111257340394233719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640458815009787192311625 1980344111257340394233719)
              ·
                refine ⟨2970516166886010591350579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980344111257340394233719 2970516166886010591350579)
                ·
                  refine ⟨4455774250329015887025869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970516166886010591350579 4455774250329015887025869)
                  ·
                    refine ⟨1670915343873380957634701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4455774250329015887025869 1670915343873380957634701)
                    ·
                      refine ⟨626593253952517859113013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1670915343873380957634701 626593253952517859113013)
                      ·
                        rfl

theorem cell23_1220286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1220286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220286 prefixEnd_1220286 := by exact prefixLift 1220286
  have htrace : WordTrace (prefixWord ++ tailWord_1220286) baseStart_1220286 baseEnd_1220286 := by
    simpa [prefixWord, tailWord_1220286, baseEnd_1220286] using wordTrace_append hprefix tailTrace_1220286
  have hstable : (prefixWord ++ tailWord_1220286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220286).length < 2 ^ (prefixWord ++ tailWord_1220286).sum := by decide
  have hdescent : baseEnd_1220286 < baseStart_1220286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220296 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_1220296 : Nat := 118140960795 + 1220296 * 2 ^ 59
def prefixEnd_1220296 : Nat := 4983230072969 + 3 ^ 40 * 1220296 * 2
def baseEnd_1220296 : Nat := 626598388759062819987967

theorem tailTrace_1220296 : CollatzResearch.WordTrace tailWord_1220296 prefixEnd_1220296 626598388759062819987967 := by
  unfold tailWord_1220296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22253925793541738404772371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29671901058055651206363161 22253925793541738404772371)
  ·
    refine ⟨33380888690312607607158557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22253925793541738404772371 33380888690312607607158557)
    ·
      refine ⟨12517833258867227852684459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33380888690312607607158557 12517833258867227852684459)
      ·
        refine ⟨18776749888300841779026689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12517833258867227852684459 18776749888300841779026689)
        ·
          refine ⟨14082562416225631334270017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18776749888300841779026689 14082562416225631334270017)
          ·
            refine ⟨10561921812169223500702513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14082562416225631334270017 10561921812169223500702513)
            ·
              refine ⟨7921441359126917625526885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10561921812169223500702513 7921441359126917625526885)
              ·
                refine ⟨1485270254836297054786291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7921441359126917625526885 1485270254836297054786291)
                ·
                  refine ⟨2227905382254445582179437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485270254836297054786291 2227905382254445582179437)
                  ·
                    refine ⟨835464518345417093317289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227905382254445582179437 835464518345417093317289)
                    ·
                      refine ⟨626598388759062819987967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835464518345417093317289 626598388759062819987967)
                      ·
                        rfl

theorem cell23_1220296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_1220296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220296 prefixEnd_1220296 := by exact prefixLift 1220296
  have htrace : WordTrace (prefixWord ++ tailWord_1220296) baseStart_1220296 baseEnd_1220296 := by
    simpa [prefixWord, tailWord_1220296, baseEnd_1220296] using wordTrace_append hprefix tailTrace_1220296
  have hstable : (prefixWord ++ tailWord_1220296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220296).length < 2 ^ (prefixWord ++ tailWord_1220296).sum := by decide
  have hdescent : baseEnd_1220296 < baseStart_1220296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220302 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1220302 : Nat := 118140960795 + 1220302 * 2 ^ 59
def prefixEnd_1220302 : Nat := 4983230072969 + 3 ^ 40 * 1220302 * 2
def baseEnd_1220302 : Nat := 208867156547663265504313

theorem tailTrace_1220302 : CollatzResearch.WordTrace tailWord_1220302 prefixEnd_1220302 208867156547663265504313 := by
  unfold tailWord_1220302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563508803132717479282895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29672046950041159889508773 5563508803132717479282895)
  ·
    refine ⟨8345263204699076218924343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563508803132717479282895 8345263204699076218924343)
    ·
      refine ⟨12517894807048614328386515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345263204699076218924343 12517894807048614328386515)
      ·
        refine ⟨18776842210572921492579773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12517894807048614328386515 18776842210572921492579773)
        ·
          refine ⟨7041315828964845559717415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18776842210572921492579773 7041315828964845559717415)
          ·
            refine ⟨10561973743447268339576123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041315828964845559717415 10561973743447268339576123)
            ·
              refine ⟨15842960615170902509364185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10561973743447268339576123 15842960615170902509364185)
              ·
                refine ⟨11882220461378176882023139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15842960615170902509364185 11882220461378176882023139)
                ·
                  refine ⟨17823330692067265323034709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11882220461378176882023139 17823330692067265323034709)
                  ·
                    refine ⟨208867156547663265504313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17823330692067265323034709 208867156547663265504313)
                    ·
                      rfl

theorem cell23_1220302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1220302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220302 prefixEnd_1220302 := by exact prefixLift 1220302
  have htrace : WordTrace (prefixWord ++ tailWord_1220302) baseStart_1220302 baseEnd_1220302 := by
    simpa [prefixWord, tailWord_1220302, baseEnd_1220302] using wordTrace_append hprefix tailTrace_1220302
  have hstable : (prefixWord ++ tailWord_1220302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220302).length < 2 ^ (prefixWord ++ tailWord_1220302).sum := by decide
  have hdescent : baseEnd_1220302 < baseStart_1220302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220312 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1220312 : Nat := 118140960795 + 1220312 * 2 ^ 59
def prefixEnd_1220312 : Nat := 4983230072969 + 3 ^ 40 * 1220312 * 2
def baseEnd_1220312 : Nat := 626606604449534757387893

theorem tailTrace_1220312 : CollatzResearch.WordTrace tailWord_1220312 prefixEnd_1220312 626606604449534757387893 := by
  unfold tailWord_1220312
  simp only [CollatzResearch.WordTrace]
  refine ⟨22254217577512755771063595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29672290103350341028084793 22254217577512755771063595)
  ·
    refine ⟨33381326366269133656595393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22254217577512755771063595 33381326366269133656595393)
    ·
      refine ⟨25035994774701850242446545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33381326366269133656595393 25035994774701850242446545)
      ·
        refine ⟨18776996081026387681834909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25035994774701850242446545 18776996081026387681834909)
        ·
          refine ⟨7041373530384895380688091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18776996081026387681834909 7041373530384895380688091)
          ·
            refine ⟨10562060295577343071032137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041373530384895380688091 10562060295577343071032137)
            ·
              refine ⟨7921545221683007303274103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10562060295577343071032137 7921545221683007303274103)
              ·
                refine ⟨11882317832524510954911155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7921545221683007303274103 11882317832524510954911155)
                ·
                  refine ⟨17823476748786766432366733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11882317832524510954911155 17823476748786766432366733)
                  ·
                    refine ⟨6683803780795037412137525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17823476748786766432366733 6683803780795037412137525)
                    ·
                      refine ⟨626606604449534757387893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6683803780795037412137525 626606604449534757387893)
                      ·
                        rfl

theorem cell23_1220312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1220312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220312 prefixEnd_1220312 := by exact prefixLift 1220312
  have htrace : WordTrace (prefixWord ++ tailWord_1220312) baseStart_1220312 baseEnd_1220312 := by
    simpa [prefixWord, tailWord_1220312, baseEnd_1220312] using wordTrace_append hprefix tailTrace_1220312
  have hstable : (prefixWord ++ tailWord_1220312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220312).length < 2 ^ (prefixWord ++ tailWord_1220312).sum := by decide
  have hdescent : baseEnd_1220312 < baseStart_1220312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220313 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 1, 3, 2]
def baseStart_1220313 : Nat := 118140960795 + 1220313 * 2 ^ 59
def prefixEnd_1220313 : Nat := 4983230072969 + 3 ^ 40 * 1220313 * 2
def baseEnd_1220313 : Nat := 626607117930189253475389

theorem tailTrace_1220313 : CollatzResearch.WordTrace tailWord_1220313 prefixEnd_1220313 626607117930189253475389 := by
  unfold tailWord_1220313
  simp only [CollatzResearch.WordTrace]
  refine ⟨44508471628021888712913593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29672314418681259141942395 44508471628021888712913593)
  ·
    refine ⟨33381353721016416534685195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44508471628021888712913593 33381353721016416534685195)
    ·
      refine ⟨50072030581524624802027793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33381353721016416534685195 50072030581524624802027793)
      ·
        refine ⟨37554022936143468601520845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50072030581524624802027793 37554022936143468601520845)
        ·
          refine ⟨14082758601053800725570317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37554022936143468601520845 14082758601053800725570317)
          ·
            refine ⟨5281034475395175272088869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14082758601053800725570317 5281034475395175272088869)
            ·
              refine ⟨990193964136595363516663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5281034475395175272088869 990193964136595363516663)
              ·
                refine ⟨1485290946204893045274995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990193964136595363516663 1485290946204893045274995)
                ·
                  refine ⟨2227936419307339567912493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485290946204893045274995 2227936419307339567912493)
                  ·
                    refine ⟨835476157240252337967185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227936419307339567912493 835476157240252337967185)
                    ·
                      refine ⟨626607117930189253475389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835476157240252337967185 626607117930189253475389)
                      ·
                        rfl

theorem cell23_1220313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_1220313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220313 prefixEnd_1220313 := by exact prefixLift 1220313
  have htrace : WordTrace (prefixWord ++ tailWord_1220313) baseStart_1220313 baseEnd_1220313 := by
    simpa [prefixWord, tailWord_1220313, baseEnd_1220313] using wordTrace_append hprefix tailTrace_1220313
  have hstable : (prefixWord ++ tailWord_1220313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220313).length < 2 ^ (prefixWord ++ tailWord_1220313).sum := by decide
  have hdescent : baseEnd_1220313 < baseStart_1220313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220332 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 7]
def baseStart_1220332 : Nat := 118140960795 + 1220332 * 2 ^ 59
def prefixEnd_1220332 : Nat := 4983230072969 + 3 ^ 40 * 1220332 * 2
def baseEnd_1220332 : Nat := 69624097118069408793089

theorem tailTrace_1220332 : CollatzResearch.WordTrace tailWord_1220332 prefixEnd_1220332 69624097118069408793089 := by
  unfold tailWord_1220332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22254582307476527478927625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29672776409968703305236833 22254582307476527478927625)
  ·
    refine ⟨16690936730607395609195719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22254582307476527478927625 16690936730607395609195719)
    ·
      refine ⟨25036405095911093413793579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16690936730607395609195719 25036405095911093413793579)
      ·
        refine ⟨37554607643866640120690369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25036405095911093413793579 37554607643866640120690369)
        ·
          refine ⟨28165955732899980090517777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37554607643866640120690369 28165955732899980090517777)
          ·
            refine ⟨21124466799674985067888333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28165955732899980090517777 21124466799674985067888333)
            ·
              refine ⟨7921675049878119400458125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21124466799674985067888333 7921675049878119400458125)
              ·
                refine ⟨2970628143704294775171797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7921675049878119400458125 2970628143704294775171797)
                ·
                  refine ⟨69624097118069408793089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2970628143704294775171797 69624097118069408793089)
                  ·
                    rfl

theorem cell23_1220332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_1220332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220332 prefixEnd_1220332 := by exact prefixLift 1220332
  have htrace : WordTrace (prefixWord ++ tailWord_1220332) baseStart_1220332 baseEnd_1220332 := by
    simpa [prefixWord, tailWord_1220332, baseEnd_1220332] using wordTrace_append hprefix tailTrace_1220332
  have hstable : (prefixWord ++ tailWord_1220332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220332).length < 2 ^ (prefixWord ++ tailWord_1220332).sum := by decide
  have hdescent : baseEnd_1220332 < baseStart_1220332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220366 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_1220366 : Nat := 118140960795 + 1220366 * 2 ^ 59
def prefixEnd_1220366 : Nat := 4983230072969 + 3 ^ 40 * 1220366 * 2
def baseEnd_1220366 : Nat := 69626036933875282901405

theorem tailTrace_1220366 : CollatzResearch.WordTrace tailWord_1220366 prefixEnd_1220366 69626036933875282901405 := by
  unfold tailWord_1220366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563800587103734845574119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29673603131219919176395301 5563800587103734845574119)
  ·
    refine ⟨8345700880655602268361179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563800587103734845574119 8345700880655602268361179)
    ·
      refine ⟨12518551320983403402541769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345700880655602268361179 12518551320983403402541769)
      ·
        refine ⟨9388913490737552551906327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12518551320983403402541769 9388913490737552551906327)
        ·
          refine ⟨14083370236106328827859491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388913490737552551906327 14083370236106328827859491)
          ·
            refine ⟨21125055354159493241789237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14083370236106328827859491 21125055354159493241789237)
            ·
              refine ⟨1980473939452452491417741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21125055354159493241789237 1980473939452452491417741)
              ·
                refine ⟨742677727294669684281653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1980473939452452491417741 742677727294669684281653)
                ·
                  refine ⟨69626036933875282901405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742677727294669684281653 69626036933875282901405)
                  ·
                    rfl

theorem cell23_1220366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_1220366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220366 prefixEnd_1220366 := by exact prefixLift 1220366
  have htrace : WordTrace (prefixWord ++ tailWord_1220366) baseStart_1220366 baseEnd_1220366 := by
    simpa [prefixWord, tailWord_1220366, baseEnd_1220366] using wordTrace_append hprefix tailTrace_1220366
  have hstable : (prefixWord ++ tailWord_1220366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220366).length < 2 ^ (prefixWord ++ tailWord_1220366).sum := by decide
  have hdescent : baseEnd_1220366 < baseStart_1220366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220369 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_1220369 : Nat := 118140960795 + 1220369 * 2 ^ 59
def prefixEnd_1220369 : Nat := 4983230072969 + 3 ^ 40 * 1220369 * 2
def baseEnd_1220369 : Nat := 626635872846841034375131

theorem tailTrace_1220369 : CollatzResearch.WordTrace tailWord_1220369 prefixEnd_1220369 626635872846841034375131 := by
  unfold tailWord_1220369
  simp only [CollatzResearch.WordTrace]
  refine ⟨44510514115819010276952161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29673676077212673517968107 44510514115819010276952161)
  ·
    refine ⟨33382885586864257707714121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44510514115819010276952161 33382885586864257707714121)
    ·
      refine ⟨25037164190148193280785591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33382885586864257707714121 25037164190148193280785591)
      ·
        refine ⟨37555746285222289921178387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25037164190148193280785591 37555746285222289921178387)
        ·
          refine ⟨56333619427833434881767581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37555746285222289921178387 56333619427833434881767581)
          ·
            refine ⟨21125107285437538080662843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56333619427833434881767581 21125107285437538080662843)
            ·
              refine ⟨31687660928156307120994265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21125107285437538080662843 31687660928156307120994265)
              ·
                refine ⟨23765745696117230340745699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31687660928156307120994265 23765745696117230340745699)
                ·
                  refine ⟨35648618544175845511118549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23765745696117230340745699 35648618544175845511118549)
                  ·
                    refine ⟨835514497129121379166841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35648618544175845511118549 835514497129121379166841)
                    ·
                      refine ⟨626635872846841034375131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835514497129121379166841 626635872846841034375131)
                      ·
                        rfl

theorem cell23_1220369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_1220369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220369 prefixEnd_1220369 := by exact prefixLift 1220369
  have htrace : WordTrace (prefixWord ++ tailWord_1220369) baseStart_1220369 baseEnd_1220369 := by
    simpa [prefixWord, tailWord_1220369, baseEnd_1220369] using wordTrace_append hprefix tailTrace_1220369
  have hstable : (prefixWord ++ tailWord_1220369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220369).length < 2 ^ (prefixWord ++ tailWord_1220369).sum := by decide
  have hdescent : baseEnd_1220369 < baseStart_1220369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220386 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_1220386 : Nat := 118140960795 + 1220386 * 2 ^ 59
def prefixEnd_1220386 : Nat := 4983230072969 + 3 ^ 40 * 1220386 * 2
def baseEnd_1220386 : Nat := 626644602017967467862553

theorem tailTrace_1220386 : CollatzResearch.WordTrace tailWord_1220386 prefixEnd_1220386 626644602017967467862553 := by
  unfold tailWord_1220386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127783539189355545080253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29674089437838281453547341 11127783539189355545080253)
  ·
    refine ⟨4172918827196008329405095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11127783539189355545080253 4172918827196008329405095)
    ·
      refine ⟨6259378240794012494107643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172918827196008329405095 6259378240794012494107643)
      ·
        refine ⟨9389067361191018741161465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6259378240794012494107643 9389067361191018741161465)
        ·
          refine ⟨7041800520893264055871099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9389067361191018741161465 7041800520893264055871099)
          ·
            refine ⟨10562700781339896083806649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041800520893264055871099 10562700781339896083806649)
            ·
              refine ⟨7922025586004922062854987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10562700781339896083806649 7922025586004922062854987)
              ·
                refine ⟨11883038379007383094282481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7922025586004922062854987 11883038379007383094282481)
                ·
                  refine ⟨8912278784255537320711861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11883038379007383094282481 8912278784255537320711861)
                  ·
                    refine ⟨835526136023956623816737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8912278784255537320711861 835526136023956623816737)
                    ·
                      refine ⟨626644602017967467862553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835526136023956623816737 626644602017967467862553)
                      ·
                        rfl

theorem cell23_1220386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_1220386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220386 prefixEnd_1220386 := by exact prefixLift 1220386
  have htrace : WordTrace (prefixWord ++ tailWord_1220386) baseStart_1220386 baseEnd_1220386 := by
    simpa [prefixWord, tailWord_1220386, baseEnd_1220386] using wordTrace_append hprefix tailTrace_1220386
  have hstable : (prefixWord ++ tailWord_1220386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220386).length < 2 ^ (prefixWord ++ tailWord_1220386).sum := by decide
  have hdescent : baseEnd_1220386 < baseStart_1220386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220389 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_1220389 : Nat := 118140960795 + 1220389 * 2 ^ 59
def prefixEnd_1220389 : Nat := 4983230072969 + 3 ^ 40 * 1220389 * 2
def baseEnd_1220389 : Nat := 626646142459930956125039

theorem tailTrace_1220389 : CollatzResearch.WordTrace tailWord_1220389 prefixEnd_1220389 626646142459930956125039 := by
  unfold tailWord_1220389
  simp only [CollatzResearch.WordTrace]
  refine ⟨44511243575746553692680221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29674162383831035795120147 44511243575746553692680221)
  ·
    refine ⟨16691716340904957634755083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44511243575746553692680221 16691716340904957634755083)
    ·
      refine ⟨25037574511357436452132625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16691716340904957634755083 25037574511357436452132625)
      ·
        refine ⟨18778180883518077339099469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25037574511357436452132625 18778180883518077339099469)
        ·
          refine ⟨7041817831319279002162301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18778180883518077339099469 7041817831319279002162301)
          ·
            refine ⟨2640681686744729625810863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7041817831319279002162301 2640681686744729625810863)
            ·
              refine ⟨3961022530117094438716295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640681686744729625810863 3961022530117094438716295)
              ·
                refine ⟨5941533795175641658074443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961022530117094438716295 5941533795175641658074443)
                ·
                  refine ⟨8912300692763462487111665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941533795175641658074443 8912300692763462487111665)
                  ·
                    refine ⟨6684225519572596865333749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8912300692763462487111665 6684225519572596865333749)
                    ·
                      refine ⟨626646142459930956125039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6684225519572596865333749 626646142459930956125039)
                      ·
                        rfl

theorem cell23_1220389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_1220389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220389 prefixEnd_1220389 := by exact prefixLift 1220389
  have htrace : WordTrace (prefixWord ++ tailWord_1220389) baseStart_1220389 baseEnd_1220389 := by
    simpa [prefixWord, tailWord_1220389, baseEnd_1220389] using wordTrace_append hprefix tailTrace_1220389
  have hstable : (prefixWord ++ tailWord_1220389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220389).length < 2 ^ (prefixWord ++ tailWord_1220389).sum := by decide
  have hdescent : baseEnd_1220389 < baseStart_1220389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220490 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_1220490 : Nat := 118140960795 + 1220490 * 2 ^ 59
def prefixEnd_1220490 : Nat := 4983230072969 + 3 ^ 40 * 1220490 * 2
def baseEnd_1220490 : Nat := 69633111556226117884675

theorem tailTrace_1220490 : CollatzResearch.WordTrace tailWord_1220490 prefixEnd_1220490 69633111556226117884675 := by
  unfold tailWord_1220490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128731837095161985526731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29676618232253765294737949 11128731837095161985526731)
  ·
    refine ⟨16693097755642742978290097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128731837095161985526731 16693097755642742978290097)
    ·
      refine ⟨12519823316732057233717573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16693097755642742978290097 12519823316732057233717573)
      ·
        refine ⟨2347466871887260731322045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12519823316732057233717573 2347466871887260731322045)
        ·
          refine ⟨880300076957722774245767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2347466871887260731322045 880300076957722774245767)
          ·
            refine ⟨1320450115436584161368651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880300076957722774245767 1320450115436584161368651)
            ·
              refine ⟨1980675173154876242052977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320450115436584161368651 1980675173154876242052977)
              ·
                refine ⟨1485506379866157181539733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980675173154876242052977 1485506379866157181539733)
                ·
                  refine ⟨69633111556226117884675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1485506379866157181539733 69633111556226117884675)
                  ·
                    rfl

theorem cell23_1220490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_1220490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220490 prefixEnd_1220490 := by exact prefixLift 1220490
  have htrace : WordTrace (prefixWord ++ tailWord_1220490) baseStart_1220490 baseEnd_1220490 := by
    simpa [prefixWord, tailWord_1220490, baseEnd_1220490] using wordTrace_append hprefix tailTrace_1220490
  have hstable : (prefixWord ++ tailWord_1220490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220490).length < 2 ^ (prefixWord ++ tailWord_1220490).sum := by decide
  have hdescent : baseEnd_1220490 < baseStart_1220490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220500 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1220500 : Nat := 118140960795 + 1220500 * 2 ^ 59
def prefixEnd_1220500 : Nat := 4983230072969 + 3 ^ 40 * 1220500 * 2
def baseEnd_1220500 : Nat := 626703138812580021837029

theorem tailTrace_1220500 : CollatzResearch.WordTrace tailWord_1220500 prefixEnd_1220500 626703138812580021837029 := by
  unfold tailWord_1220500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22257646039172209824985477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29676861385562946433313969 22257646039172209824985477)
  ·
    refine ⟨4173308632344789342184777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22257646039172209824985477 4173308632344789342184777)
    ·
      refine ⟨3129981474258592006638583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4173308632344789342184777 3129981474258592006638583)
      ·
        refine ⟨4694972211387888009957875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129981474258592006638583 4694972211387888009957875)
        ·
          refine ⟨7042458317081832014936813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694972211387888009957875 7042458317081832014936813)
          ·
            refine ⟨2640921868905687005601305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7042458317081832014936813 2640921868905687005601305)
            ·
              refine ⟨1980691401679265254200979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640921868905687005601305 1980691401679265254200979)
              ·
                refine ⟨2971037102518897881301469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980691401679265254200979 2971037102518897881301469)
                ·
                  refine ⟨1114138913444586705488051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2971037102518897881301469 1114138913444586705488051)
                  ·
                    refine ⟨1671208370166880058232077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1114138913444586705488051 1671208370166880058232077)
                    ·
                      refine ⟨626703138812580021837029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1671208370166880058232077 626703138812580021837029)
                      ·
                        rfl

theorem cell23_1220500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1220500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220500 prefixEnd_1220500 := by exact prefixLift 1220500
  have htrace : WordTrace (prefixWord ++ tailWord_1220500) baseStart_1220500 baseEnd_1220500 := by
    simpa [prefixWord, tailWord_1220500, baseEnd_1220500] using wordTrace_append hprefix tailTrace_1220500
  have hstable : (prefixWord ++ tailWord_1220500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220500).length < 2 ^ (prefixWord ++ tailWord_1220500).sum := by decide
  have hdescent : baseEnd_1220500 < baseStart_1220500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220516 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_1220516 : Nat := 118140960795 + 1220516 * 2 ^ 59
def prefixEnd_1220516 : Nat := 4983230072969 + 3 ^ 40 * 1220516 * 2
def baseEnd_1220516 : Nat := 208903784834350653078985

theorem tailTrace_1220516 : CollatzResearch.WordTrace tailWord_1220516 prefixEnd_1220516 208903784834350653078985 := by
  unfold tailWord_1220516
  simp only [CollatzResearch.WordTrace]
  refine ⟨22257937823143227191276701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29677250430857636255035601 22257937823143227191276701)
  ·
    refine ⟨8346726683678710196728763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22257937823143227191276701 8346726683678710196728763)
    ·
      refine ⟨12520090025518065295093145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346726683678710196728763 12520090025518065295093145)
      ·
        refine ⟨9390067519138548971319859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12520090025518065295093145 9390067519138548971319859)
        ·
          refine ⟨14085101278707823456979789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390067519138548971319859 14085101278707823456979789)
          ·
            refine ⟨5281912979515433796367421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14085101278707823456979789 5281912979515433796367421)
            ·
              refine ⟨1980717367318287673637783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5281912979515433796367421 1980717367318287673637783)
              ·
                refine ⟨2971076050977431510456675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980717367318287673637783 2971076050977431510456675)
                ·
                  refine ⟨4456614076466147265685013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971076050977431510456675 4456614076466147265685013)
                  ·
                    refine ⟨208903784834350653078985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4456614076466147265685013 208903784834350653078985)
                    ·
                      rfl

theorem cell23_1220516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_1220516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220516 prefixEnd_1220516 := by exact prefixLift 1220516
  have htrace : WordTrace (prefixWord ++ tailWord_1220516) baseStart_1220516 baseEnd_1220516 := by
    simpa [prefixWord, tailWord_1220516, baseEnd_1220516] using wordTrace_append hprefix tailTrace_1220516
  have hstable : (prefixWord ++ tailWord_1220516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220516).length < 2 ^ (prefixWord ++ tailWord_1220516).sum := by decide
  have hdescent : baseEnd_1220516 < baseStart_1220516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220559 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 7]
def baseStart_1220559 : Nat := 118140960795 + 1220559 * 2 ^ 59
def prefixEnd_1220559 : Nat := 4983230072969 + 3 ^ 40 * 1220559 * 2
def baseEnd_1220559 : Nat := 208911144723731763666419

theorem tailTrace_1220559 : CollatzResearch.WordTrace tailWord_1220559 prefixEnd_1220559 208911144723731763666419 := by
  unfold tailWord_1220559
  simp only [CollatzResearch.WordTrace]
  refine ⟨44517443985130672726368731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29678295990087115150912487 44517443985130672726368731)
  ·
    refine ⟨66776165977696009089553097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44517443985130672726368731 66776165977696009089553097)
    ·
      refine ⟨50082124483272006817164823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66776165977696009089553097 50082124483272006817164823)
      ·
        refine ⟨75123186724908010225747235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50082124483272006817164823 75123186724908010225747235)
        ·
          refine ⟨112684780087362015338620853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75123186724908010225747235 112684780087362015338620853)
          ·
            refine ⟨10564198133190188937995705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112684780087362015338620853 10564198133190188937995705)
            ·
              refine ⟨7923148599892641703496779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10564198133190188937995705 7923148599892641703496779)
              ·
                refine ⟨11884722899838962555245169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7923148599892641703496779 11884722899838962555245169)
                ·
                  refine ⟨8913542174879221916433877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11884722899838962555245169 8913542174879221916433877)
                  ·
                    refine ⟨208911144723731763666419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8913542174879221916433877 208911144723731763666419)
                    ·
                      rfl

theorem cell23_1220559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_1220559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220559 prefixEnd_1220559 := by exact prefixLift 1220559
  have htrace : WordTrace (prefixWord ++ tailWord_1220559) baseStart_1220559 baseEnd_1220559 := by
    simpa [prefixWord, tailWord_1220559, baseEnd_1220559] using wordTrace_append hprefix tailTrace_1220559
  have hstable : (prefixWord ++ tailWord_1220559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220559).length < 2 ^ (prefixWord ++ tailWord_1220559).sum := by decide
  have hdescent : baseEnd_1220559 < baseStart_1220559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220614 : List Nat := [6, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1220614 : Nat := 118140960795 + 1220614 * 2 ^ 59
def prefixEnd_1220614 : Nat := 4983230072969 + 3 ^ 40 * 1220614 * 2
def baseEnd_1220614 : Nat := 23213395392858984289315

theorem tailTrace_1220614 : CollatzResearch.WordTrace tailWord_1220614 prefixEnd_1220614 23213395392858984289315 := by
  unfold tailWord_1220614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391232812497856784988153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29679633333287611413080597 1391232812497856784988153)
  ·
    refine ⟨1043424609373392588741115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391232812497856784988153 1043424609373392588741115)
    ·
      refine ⟨1565136914060088883111673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043424609373392588741115 1565136914060088883111673)
      ·
        refine ⟨1173852685545066662333755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1565136914060088883111673 1173852685545066662333755)
        ·
          refine ⟨1760779028317599993500633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173852685545066662333755 1760779028317599993500633)
          ·
            refine ⟨1320584271238199995125475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760779028317599993500633 1320584271238199995125475)
            ·
              refine ⟨1980876406857299992688213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320584271238199995125475 1980876406857299992688213)
              ·
                refine ⟨23213395392858984289315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1980876406857299992688213 23213395392858984289315)
                ·
                  rfl

theorem cell23_1220614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1220614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220614 prefixEnd_1220614 := by exact prefixLift 1220614
  have htrace : WordTrace (prefixWord ++ tailWord_1220614) baseStart_1220614 baseEnd_1220614 := by
    simpa [prefixWord, tailWord_1220614, baseEnd_1220614] using wordTrace_append hprefix tailTrace_1220614
  have hstable : (prefixWord ++ tailWord_1220614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220614).length < 2 ^ (prefixWord ++ tailWord_1220614).sum := by decide
  have hdescent : baseEnd_1220614 < baseStart_1220614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220616 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1220616 : Nat := 118140960795 + 1220616 * 2 ^ 59
def prefixEnd_1220616 : Nat := 4983230072969 + 3 ^ 40 * 1220616 * 2
def baseEnd_1220616 : Nat := 626762702568501567986495

theorem tailTrace_1220616 : CollatzResearch.WordTrace tailWord_1220616 prefixEnd_1220616 626762702568501567986495 := by
  unfold tailWord_1220616
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259761472962085730596851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29679681963949447640795801 22259761472962085730596851)
  ·
    refine ⟨33389642209443128595895277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22259761472962085730596851 33389642209443128595895277)
    ·
      refine ⟨12521115828541173223460729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33389642209443128595895277 12521115828541173223460729)
      ·
        refine ⟨9390836871405879917595547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12521115828541173223460729 9390836871405879917595547)
        ·
          refine ⟨14086255307108819876393321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390836871405879917595547 14086255307108819876393321)
          ·
            refine ⟨10564691480331614907294991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14086255307108819876393321 10564691480331614907294991)
            ·
              refine ⟨15847037220497422360942487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10564691480331614907294991 15847037220497422360942487)
              ·
                refine ⟨23770555830746133541413731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15847037220497422360942487 23770555830746133541413731)
                ·
                  refine ⟨35655833746119200312120597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23770555830746133541413731 35655833746119200312120597)
                  ·
                    refine ⟨1671367206849337514630653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35655833746119200312120597 1671367206849337514630653)
                    ·
                      refine ⟨626762702568501567986495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1671367206849337514630653 626762702568501567986495)
                      ·
                        rfl

theorem cell23_1220616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1220616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220616 prefixEnd_1220616 := by exact prefixLift 1220616
  have htrace : WordTrace (prefixWord ++ tailWord_1220616) baseStart_1220616 baseEnd_1220616 := by
    simpa [prefixWord, tailWord_1220616, baseEnd_1220616] using wordTrace_append hprefix tailTrace_1220616
  have hstable : (prefixWord ++ tailWord_1220616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220616).length < 2 ^ (prefixWord ++ tailWord_1220616).sum := by decide
  have hdescent : baseEnd_1220616 < baseStart_1220616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220636 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 9]
def baseStart_1220636 : Nat := 118140960795 + 1220636 * 2 ^ 59
def prefixEnd_1220636 : Nat := 4983230072969 + 3 ^ 40 * 1220636 * 2
def baseEnd_1220636 : Nat := 69641441353510165526267

theorem tailTrace_1220636 : CollatzResearch.WordTrace tailWord_1220636 prefixEnd_1220636 69641441353510165526267 := by
  unfold tailWord_1220636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260126202925857438460881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29680168270567809917947841 22260126202925857438460881)
  ·
    refine ⟨16695094652194393078845661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22260126202925857438460881 16695094652194393078845661)
    ·
      refine ⟨6260660494572897404567123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16695094652194393078845661 6260660494572897404567123)
      ·
        refine ⟨9390990741859346106850685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260660494572897404567123 9390990741859346106850685)
        ·
          refine ⟨3521621528197254790069007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9390990741859346106850685 3521621528197254790069007)
          ·
            refine ⟨5282432292295882185103511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521621528197254790069007 5282432292295882185103511)
            ·
              refine ⟨7923648438443823277655267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282432292295882185103511 7923648438443823277655267)
              ·
                refine ⟨11885472657665734916482901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7923648438443823277655267 11885472657665734916482901)
                ·
                  refine ⟨69641441353510165526267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11885472657665734916482901 69641441353510165526267)
                  ·
                    rfl

theorem cell23_1220636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_1220636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220636 prefixEnd_1220636 := by exact prefixLift 1220636
  have htrace : WordTrace (prefixWord ++ tailWord_1220636) baseStart_1220636 baseEnd_1220636 := by
    simpa [prefixWord, tailWord_1220636, baseEnd_1220636] using wordTrace_append hprefix tailTrace_1220636
  have hstable : (prefixWord ++ tailWord_1220636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220636).length < 2 ^ (prefixWord ++ tailWord_1220636).sum := by decide
  have hdescent : baseEnd_1220636 < baseStart_1220636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220664 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_1220664 : Nat := 118140960795 + 1220664 * 2 ^ 59
def prefixEnd_1220664 : Nat := 4983230072969 + 3 ^ 40 * 1220664 * 2
def baseEnd_1220664 : Nat := 626787349639917380186275

theorem tailTrace_1220664 : CollatzResearch.WordTrace tailWord_1220664 prefixEnd_1220664 626787349639917380186275 := by
  unfold tailWord_1220664
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260636824875137829470523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29680849099833517105960697 22260636824875137829470523)
  ·
    refine ⟨33390955237312706744205785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260636824875137829470523 33390955237312706744205785)
    ·
      refine ⟨25043216427984530058154339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33390955237312706744205785 25043216427984530058154339)
      ·
        refine ⟨37564824641976795087231509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25043216427984530058154339 37564824641976795087231509)
        ·
          refine ⟨1760851155092662269713977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37564824641976795087231509 1760851155092662269713977)
          ·
            refine ⟨1320638366319496702285483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760851155092662269713977 1320638366319496702285483)
            ·
              refine ⟨1980957549479245053428225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320638366319496702285483 1980957549479245053428225)
              ·
                refine ⟨1485718162109433790071169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980957549479245053428225 1485718162109433790071169)
                ·
                  refine ⟨1114288621582075342553377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485718162109433790071169 1114288621582075342553377)
                  ·
                    refine ⟨835716466186556506915033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114288621582075342553377 835716466186556506915033)
                    ·
                      refine ⟨626787349639917380186275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835716466186556506915033 626787349639917380186275)
                      ·
                        rfl

theorem cell23_1220664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_1220664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220664 prefixEnd_1220664 := by exact prefixLift 1220664
  have htrace : WordTrace (prefixWord ++ tailWord_1220664) baseStart_1220664 baseEnd_1220664 := by
    simpa [prefixWord, tailWord_1220664, baseEnd_1220664] using wordTrace_append hprefix tailTrace_1220664
  have hstable : (prefixWord ++ tailWord_1220664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220664).length < 2 ^ (prefixWord ++ tailWord_1220664).sum := by decide
  have hdescent : baseEnd_1220664 < baseStart_1220664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220666 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_1220666 : Nat := 118140960795 + 1220666 * 2 ^ 59
def prefixEnd_1220666 : Nat := 4983230072969 + 3 ^ 40 * 1220666 * 2
def baseEnd_1220666 : Nat := 208929458867075457453755

theorem tailTrace_1220666 : CollatzResearch.WordTrace tailWord_1220666 prefixEnd_1220666 208929458867075457453755 := by
  unfold tailWord_1220666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130336648935757500128463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29680897730495353333675901 11130336648935757500128463)
  ·
    refine ⟨16695504973403636250192695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11130336648935757500128463 16695504973403636250192695)
    ·
      refine ⟨25043257460105454375289043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16695504973403636250192695 25043257460105454375289043)
      ·
        refine ⟨37564886190158181562933565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25043257460105454375289043 37564886190158181562933565)
        ·
          refine ⟨14086832321309318086100087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37564886190158181562933565 14086832321309318086100087)
          ·
            refine ⟨21130248481963977129150131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14086832321309318086100087 21130248481963977129150131)
            ·
              refine ⟨31695372722945965693725197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21130248481963977129150131 31695372722945965693725197)
              ·
                refine ⟨11885764771104737135146949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31695372722945965693725197 11885764771104737135146949)
                ·
                  refine ⟨2228580894582138212840053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11885764771104737135146949 2228580894582138212840053)
                  ·
                    refine ⟨208929458867075457453755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2228580894582138212840053 208929458867075457453755)
                    ·
                      rfl

theorem cell23_1220666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_1220666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220666 prefixEnd_1220666 := by exact prefixLift 1220666
  have htrace : WordTrace (prefixWord ++ tailWord_1220666) baseStart_1220666 baseEnd_1220666 := by
    simpa [prefixWord, tailWord_1220666, baseEnd_1220666] using wordTrace_append hprefix tailTrace_1220666
  have hstable : (prefixWord ++ tailWord_1220666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220666).length < 2 ^ (prefixWord ++ tailWord_1220666).sum := by decide
  have hdescent : baseEnd_1220666 < baseStart_1220666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220670 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_1220670 : Nat := 118140960795 + 1220670 * 2 ^ 59
def prefixEnd_1220670 : Nat := 4983230072969 + 3 ^ 40 * 1220670 * 2
def baseEnd_1220670 : Nat := 69643381169316039634583

theorem tailTrace_1220670 : CollatzResearch.WordTrace tailWord_1220670 prefixEnd_1220670 69643381169316039634583 := by
  unfold tailWord_1220670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565186560966067335457433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29680994991819025789106309 5565186560966067335457433)
  ·
    refine ⟨4173889920724550501593075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5565186560966067335457433 4173889920724550501593075)
    ·
      refine ⟨6260834881086825752389613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173889920724550501593075 6260834881086825752389613)
      ·
        refine ⟨2347813080407559657146105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6260834881086825752389613 2347813080407559657146105)
        ·
          refine ⟨1760859810305669742859579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347813080407559657146105 1760859810305669742859579)
          ·
            refine ⟨2641289715458504614289369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760859810305669742859579 2641289715458504614289369)
            ·
              refine ⟨1980967286593878460717027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2641289715458504614289369 1980967286593878460717027)
              ·
                refine ⟨2971450929890817691075541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980967286593878460717027 2971450929890817691075541)
                ·
                  refine ⟨69643381169316039634583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2971450929890817691075541 69643381169316039634583)
                  ·
                    rfl

theorem cell23_1220670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_1220670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220670 prefixEnd_1220670 := by exact prefixLift 1220670
  have htrace : WordTrace (prefixWord ++ tailWord_1220670) baseStart_1220670 baseEnd_1220670 := by
    simpa [prefixWord, tailWord_1220670, baseEnd_1220670] using wordTrace_append hprefix tailTrace_1220670
  have hstable : (prefixWord ++ tailWord_1220670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220670).length < 2 ^ (prefixWord ++ tailWord_1220670).sum := by decide
  have hdescent : baseEnd_1220670 < baseStart_1220670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220703 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 4, 4, 2]
def baseStart_1220703 : Nat := 118140960795 + 1220703 * 2 ^ 59
def prefixEnd_1220703 : Nat := 4983230072969 + 3 ^ 40 * 1220703 * 2
def baseEnd_1220703 : Nat := 626807375385442727598595

theorem tailTrace_1220703 : CollatzResearch.WordTrace tailWord_1220703 prefixEnd_1220703 626807375385442727598595 := by
  unfold tailWord_1220703
  simp only [CollatzResearch.WordTrace]
  refine ⟨44522696096608985319610763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29681797397739323546407175 44522696096608985319610763)
  ·
    refine ⟨66784044144913477979416145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44522696096608985319610763 66784044144913477979416145)
    ·
      refine ⟨50088033108685108484562109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66784044144913477979416145 50088033108685108484562109)
      ·
        refine ⟨18783012415756915681710791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50088033108685108484562109 18783012415756915681710791)
        ·
          refine ⟨28174518623635373522566187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18783012415756915681710791 28174518623635373522566187)
          ·
            refine ⟨42261777935453060283849281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28174518623635373522566187 42261777935453060283849281)
            ·
              refine ⟨31696333451589795212886961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42261777935453060283849281 31696333451589795212886961)
              ·
                refine ⟨23772250088692346409665221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31696333451589795212886961 23772250088692346409665221)
                ·
                  refine ⟨4457296891629814951812229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23772250088692346409665221 4457296891629814951812229)
                  ·
                    refine ⟨835743167180590303464793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4457296891629814951812229 835743167180590303464793)
                    ·
                      refine ⟨626807375385442727598595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835743167180590303464793 626807375385442727598595)
                      ·
                        rfl

theorem cell23_1220703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_1220703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220703 prefixEnd_1220703 := by exact prefixLift 1220703
  have htrace : WordTrace (prefixWord ++ tailWord_1220703) baseStart_1220703 baseEnd_1220703 := by
    simpa [prefixWord, tailWord_1220703, baseEnd_1220703] using wordTrace_append hprefix tailTrace_1220703
  have hstable : (prefixWord ++ tailWord_1220703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220703).length < 2 ^ (prefixWord ++ tailWord_1220703).sum := by decide
  have hdescent : baseEnd_1220703 < baseStart_1220703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220781 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1220781 : Nat := 118140960795 + 1220781 * 2 ^ 59
def prefixEnd_1220781 : Nat := 4983230072969 + 3 ^ 40 * 1220781 * 2
def baseEnd_1220781 : Nat := 208949142292164474141079

theorem tailTrace_1220781 : CollatzResearch.WordTrace tailWord_1220781 prefixEnd_1220781 208949142292164474141079 := by
  unfold tailWord_1220781
  simp only [CollatzResearch.WordTrace]
  refine ⟨44525540990326404640950197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29683693993550936427300131 44525540990326404640950197)
  ·
    refine ⟨4174269467843100435089081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44525540990326404640950197 4174269467843100435089081)
    ·
      refine ⟨3130702100882325326316811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4174269467843100435089081 3130702100882325326316811)
      ·
        refine ⟨4696053151323487989475217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130702100882325326316811 4696053151323487989475217)
        ·
          refine ⟨3522039863492615992106413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4696053151323487989475217 3522039863492615992106413)
          ·
            refine ⟨1320764948809730997039905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3522039863492615992106413 1320764948809730997039905)
            ·
              refine ⟨990573711607298247779929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320764948809730997039905 990573711607298247779929)
              ·
                refine ⟨742930283705473685834947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990573711607298247779929 742930283705473685834947)
                ·
                  refine ⟨1114395425558210528752421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742930283705473685834947 1114395425558210528752421)
                  ·
                    refine ⟨208949142292164474141079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114395425558210528752421 208949142292164474141079)
                    ·
                      rfl

theorem cell23_1220781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1220781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220781 prefixEnd_1220781 := by exact prefixLift 1220781
  have htrace : WordTrace (prefixWord ++ tailWord_1220781) baseStart_1220781 baseEnd_1220781 := by
    simpa [prefixWord, tailWord_1220781, baseEnd_1220781] using wordTrace_append hprefix tailTrace_1220781
  have hstable : (prefixWord ++ tailWord_1220781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220781).length < 2 ^ (prefixWord ++ tailWord_1220781).sum := by decide
  have hdescent : baseEnd_1220781 < baseStart_1220781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220793 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1220793 : Nat := 118140960795 + 1220793 * 2 ^ 59
def prefixEnd_1220793 : Nat := 4983230072969 + 3 ^ 40 * 1220793 * 2
def baseEnd_1220793 : Nat := 626853588644347375473181

theorem tailTrace_1220793 : CollatzResearch.WordTrace tailWord_1220793 prefixEnd_1220793 626853588644347375473181 := by
  unfold tailWord_1220793
  simp only [CollatzResearch.WordTrace]
  refine ⟨44525978666282930690387033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29683985777521953793591355 44525978666282930690387033)
  ·
    refine ⟨33394483999712198017790275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44525978666282930690387033 33394483999712198017790275)
    ·
      refine ⟨50091725999568297026685413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33394483999712198017790275 50091725999568297026685413)
      ·
        refine ⟨9392198624919055692503515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50091725999568297026685413 9392198624919055692503515)
        ·
          refine ⟨14088297937378583538755273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392198624919055692503515 14088297937378583538755273)
          ·
            refine ⟨10566223453033937654066455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14088297937378583538755273 10566223453033937654066455)
            ·
              refine ⟨15849335179550906481099683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10566223453033937654066455 15849335179550906481099683)
              ·
                refine ⟨23774002769326359721649525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15849335179550906481099683 23774002769326359721649525)
                ·
                  refine ⟨2228812759624346223904643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23774002769326359721649525 2228812759624346223904643)
                  ·
                    refine ⟨3343219139436519335856965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2228812759624346223904643 3343219139436519335856965)
                    ·
                      refine ⟨626853588644347375473181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3343219139436519335856965 626853588644347375473181)
                      ·
                        rfl

theorem cell23_1220793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1220793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220793 prefixEnd_1220793 := by exact prefixLift 1220793
  have htrace : WordTrace (prefixWord ++ tailWord_1220793) baseStart_1220793 baseEnd_1220793 := by
    simpa [prefixWord, tailWord_1220793, baseEnd_1220793] using wordTrace_append hprefix tailTrace_1220793
  have hstable : (prefixWord ++ tailWord_1220793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220793).length < 2 ^ (prefixWord ++ tailWord_1220793).sum := by decide
  have hdescent : baseEnd_1220793 < baseStart_1220793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220810 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1220810 : Nat := 118140960795 + 1220810 * 2 ^ 59
def prefixEnd_1220810 : Nat := 4983230072969 + 3 ^ 40 * 1220810 * 2
def baseEnd_1220810 : Nat := 626862317815473808960603

theorem tailTrace_1220810 : CollatzResearch.WordTrace tailWord_1220810 prefixEnd_1220810 626862317815473808960603 := by
  unfold tailWord_1220810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131649676805335648438971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29684399138147561729170589 11131649676805335648438971)
  ·
    refine ⟨16697474515208003472658457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11131649676805335648438971 16697474515208003472658457)
    ·
      refine ⟨12523105886406002604493843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16697474515208003472658457 12523105886406002604493843)
      ·
        refine ⟨18784658829609003906740765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12523105886406002604493843 18784658829609003906740765)
        ·
          refine ⟨7044247061103376465027787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18784658829609003906740765 7044247061103376465027787)
          ·
            refine ⟨10566370591655064697541681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7044247061103376465027787 10566370591655064697541681)
            ·
              refine ⟨7924777943741298523156261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10566370591655064697541681 7924777943741298523156261)
              ·
                refine ⟨1485895864451493473091799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7924777943741298523156261 1485895864451493473091799)
                ·
                  refine ⟨2228843796677240209637699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485895864451493473091799 2228843796677240209637699)
                  ·
                    refine ⟨3343265695015860314456549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2228843796677240209637699 3343265695015860314456549)
                    ·
                      refine ⟨626862317815473808960603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3343265695015860314456549 626862317815473808960603)
                      ·
                        rfl

theorem cell23_1220810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1220810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220810 prefixEnd_1220810 := by exact prefixLift 1220810
  have htrace : WordTrace (prefixWord ++ tailWord_1220810) baseStart_1220810 baseEnd_1220810 := by
    simpa [prefixWord, tailWord_1220810, baseEnd_1220810] using wordTrace_append hprefix tailTrace_1220810
  have hstable : (prefixWord ++ tailWord_1220810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220810).length < 2 ^ (prefixWord ++ tailWord_1220810).sum := by decide
  have hdescent : baseEnd_1220810 < baseStart_1220810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220814 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_1220814 : Nat := 118140960795 + 1220814 * 2 ^ 59
def prefixEnd_1220814 : Nat := 4983230072969 + 3 ^ 40 * 1220814 * 2
def baseEnd_1220814 : Nat := 626864371738091793310585

theorem tailTrace_1220814 : CollatzResearch.WordTrace tailWord_1220814 prefixEnd_1220814 626864371738091793310585 := by
  unfold tailWord_1220814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565843074900856409612687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29684496399471234184600997 5565843074900856409612687)
  ·
    refine ⟨8348764612351284614419031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5565843074900856409612687 8348764612351284614419031)
    ·
      refine ⟨12523146918526926921628547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8348764612351284614419031 12523146918526926921628547)
      ·
        refine ⟨18784720377790390382442821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12523146918526926921628547 18784720377790390382442821)
        ·
          refine ⟨3522135070835698196708029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18784720377790390382442821 3522135070835698196708029)
          ·
            refine ⟨1320800651563386823765511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3522135070835698196708029 1320800651563386823765511)
            ·
              refine ⟨1981200977345080235648267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320800651563386823765511 1981200977345080235648267)
              ·
                refine ⟨2971801466017620353472401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981200977345080235648267 2971801466017620353472401)
                ·
                  refine ⟨2228851099513215265104301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971801466017620353472401 2228851099513215265104301)
                  ·
                    refine ⟨835819162317455724414113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228851099513215265104301 835819162317455724414113)
                    ·
                      refine ⟨626864371738091793310585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835819162317455724414113 626864371738091793310585)
                      ·
                        rfl

theorem cell23_1220814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_1220814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220814 prefixEnd_1220814 := by exact prefixLift 1220814
  have htrace : WordTrace (prefixWord ++ tailWord_1220814) baseStart_1220814 baseEnd_1220814 := by
    simpa [prefixWord, tailWord_1220814, baseEnd_1220814] using wordTrace_append hprefix tailTrace_1220814
  have hstable : (prefixWord ++ tailWord_1220814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220814).length < 2 ^ (prefixWord ++ tailWord_1220814).sum := by decide
  have hdescent : baseEnd_1220814 < baseStart_1220814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220821 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1220821 : Nat := 118140960795 + 1220821 * 2 ^ 59
def prefixEnd_1220821 : Nat := 4983230072969 + 3 ^ 40 * 1220821 * 2
def baseEnd_1220821 : Nat := 626867966102673265923053

theorem tailTrace_1220821 : CollatzResearch.WordTrace tailWord_1220821 prefixEnd_1220821 626867966102673265923053 := by
  unfold tailWord_1220821
  simp only [CollatzResearch.WordTrace]
  refine ⟨44526999910181491472406317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29684666606787660981604211 44526999910181491472406317)
  ·
    refine ⟨16697624966318059302152369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44526999910181491472406317 16697624966318059302152369)
    ·
      refine ⟨12523218724738544476614277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16697624966318059302152369 12523218724738544476614277)
      ·
        refine ⟨2348103510888477089365177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12523218724738544476614277 2348103510888477089365177)
        ·
          refine ⟨1761077633166357817023883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2348103510888477089365177 1761077633166357817023883)
          ·
            refine ⟨2641616449749536725535825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761077633166357817023883 2641616449749536725535825)
            ·
              refine ⟨1981212337312152544151869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2641616449749536725535825 1981212337312152544151869)
              ·
                refine ⟨742954626492057204056951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1981212337312152544151869 742954626492057204056951)
                ·
                  refine ⟨1114431939738085806085427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742954626492057204056951 1114431939738085806085427)
                  ·
                    refine ⟨1671647909607128709128141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1114431939738085806085427 1671647909607128709128141)
                    ·
                      refine ⟨626867966102673265923053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1671647909607128709128141 626867966102673265923053)
                      ·
                        rfl

theorem cell23_1220821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1220821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220821 prefixEnd_1220821 := by exact prefixLift 1220821
  have htrace : WordTrace (prefixWord ++ tailWord_1220821) baseStart_1220821 baseEnd_1220821 := by
    simpa [prefixWord, tailWord_1220821, baseEnd_1220821] using wordTrace_append hprefix tailTrace_1220821
  have hstable : (prefixWord ++ tailWord_1220821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220821).length < 2 ^ (prefixWord ++ tailWord_1220821).sum := by decide
  have hdescent : baseEnd_1220821 < baseStart_1220821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220837 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1220837 : Nat := 118140960795 + 1220837 * 2 ^ 59
def prefixEnd_1220837 : Nat := 4983230072969 + 3 ^ 40 * 1220837 * 2
def baseEnd_1220837 : Nat := 208958727264381734440993

theorem tailTrace_1220837 : CollatzResearch.WordTrace tailWord_1220837 prefixEnd_1220837 208958727264381734440993 := by
  unfold tailWord_1220837
  simp only [CollatzResearch.WordTrace]
  refine ⟨44527583478123526204988765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29685055652082350803325843 44527583478123526204988765)
  ·
    refine ⟨16697843804296322326870787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44527583478123526204988765 16697843804296322326870787)
    ·
      refine ⟨25046765706444483490306181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16697843804296322326870787 25046765706444483490306181)
      ·
        refine ⟨4696268569958340654432409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25046765706444483490306181 4696268569958340654432409)
        ·
          refine ⟨3522201427468755490824307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4696268569958340654432409 3522201427468755490824307)
          ·
            refine ⟨5283302141203133236236461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522201427468755490824307 5283302141203133236236461)
            ·
              refine ⟨1981238302951174963588673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5283302141203133236236461 1981238302951174963588673)
              ·
                refine ⟨1485928727213381222691505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981238302951174963588673 1485928727213381222691505)
                ·
                  refine ⟨1114446545410035917018629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485928727213381222691505 1114446545410035917018629)
                  ·
                    refine ⟨208958727264381734440993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114446545410035917018629 208958727264381734440993)
                    ·
                      rfl

theorem cell23_1220837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1220837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220837 prefixEnd_1220837 := by exact prefixLift 1220837
  have htrace : WordTrace (prefixWord ++ tailWord_1220837) baseStart_1220837 baseEnd_1220837 := by
    simpa [prefixWord, tailWord_1220837, baseEnd_1220837] using wordTrace_append hprefix tailTrace_1220837
  have hstable : (prefixWord ++ tailWord_1220837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220837).length < 2 ^ (prefixWord ++ tailWord_1220837).sum := by decide
  have hdescent : baseEnd_1220837 < baseStart_1220837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220844 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 1, 2, 2]
def baseStart_1220844 : Nat := 118140960795 + 1220844 * 2 ^ 59
def prefixEnd_1220844 : Nat := 4983230072969 + 3 ^ 40 * 1220844 * 2
def baseEnd_1220844 : Nat := 626879776157726675935447

theorem tailTrace_1220844 : CollatzResearch.WordTrace tailWord_1220844 prefixEnd_1220844 626879776157726675935447 := by
  unfold tailWord_1220844
  simp only [CollatzResearch.WordTrace]
  refine ⟨22263919394549083200246793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29685225859398777600329057 22263919394549083200246793)
  ·
    refine ⟨16697939545911812400185095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22263919394549083200246793 16697939545911812400185095)
    ·
      refine ⟨25046909318867718600277643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16697939545911812400185095 25046909318867718600277643)
      ·
        refine ⟨37570363978301577900416465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25046909318867718600277643 37570363978301577900416465)
        ·
          refine ⟨28177772983726183425312349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37570363978301577900416465 28177772983726183425312349)
          ·
            refine ⟨10566664868897318784492131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28177772983726183425312349 10566664868897318784492131)
            ·
              refine ⟨15849997303345978176738197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10566664868897318784492131 15849997303345978176738197)
              ·
                refine ⟨742968623594342727034603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15849997303345978176738197 742968623594342727034603)
                ·
                  refine ⟨1114452935391514090551905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742968623594342727034603 1114452935391514090551905)
                  ·
                    refine ⟨835839701543635567913929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114452935391514090551905 835839701543635567913929)
                    ·
                      refine ⟨626879776157726675935447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835839701543635567913929 626879776157726675935447)
                      ·
                        rfl

theorem cell23_1220844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_1220844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220844 prefixEnd_1220844 := by exact prefixLift 1220844
  have htrace : WordTrace (prefixWord ++ tailWord_1220844) baseStart_1220844 baseEnd_1220844 := by
    simpa [prefixWord, tailWord_1220844, baseEnd_1220844] using wordTrace_append hprefix tailTrace_1220844
  have hstable : (prefixWord ++ tailWord_1220844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220844).length < 2 ^ (prefixWord ++ tailWord_1220844).sum := by decide
  have hdescent : baseEnd_1220844 < baseStart_1220844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220873 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_1220873 : Nat := 118140960795 + 1220873 * 2 ^ 59
def prefixEnd_1220873 : Nat := 4983230072969 + 3 ^ 40 * 1220873 * 2
def baseEnd_1220873 : Nat := 626894667096707062472813

theorem tailTrace_1220873 : CollatzResearch.WordTrace tailWord_1220873 prefixEnd_1220873 626894667096707062472813 := by
  unfold tailWord_1220873
  simp only [CollatzResearch.WordTrace]
  refine ⟨44528896505993104353299273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29685931003995402902199515 44528896505993104353299273)
  ·
    refine ⟨33396672379494828264974455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44528896505993104353299273 33396672379494828264974455)
    ·
      refine ⟨50095008569242242397461683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33396672379494828264974455 50095008569242242397461683)
      ·
        refine ⟨75142512853863363596192525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50095008569242242397461683 75142512853863363596192525)
        ·
          refine ⟨28178442320198761348572197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75142512853863363596192525 28178442320198761348572197)
          ·
            refine ⟨5283457935037267752857287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28178442320198761348572197 5283457935037267752857287)
            ·
              refine ⟨7925186902555901629285931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283457935037267752857287 7925186902555901629285931)
              ·
                refine ⟨11887780353833852443928897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7925186902555901629285931 11887780353833852443928897)
                ·
                  refine ⟨8915835265375389332946673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11887780353833852443928897 8915835265375389332946673)
                  ·
                    refine ⟨6686876449031541999710005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8915835265375389332946673 6686876449031541999710005)
                    ·
                      refine ⟨626894667096707062472813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6686876449031541999710005 626894667096707062472813)
                      ·
                        rfl

theorem cell23_1220873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_1220873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220873 prefixEnd_1220873 := by exact prefixLift 1220873
  have htrace : WordTrace (prefixWord ++ tailWord_1220873) baseStart_1220873 baseEnd_1220873 := by
    simpa [prefixWord, tailWord_1220873, baseEnd_1220873] using wordTrace_append hprefix tailTrace_1220873
  have hstable : (prefixWord ++ tailWord_1220873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220873).length < 2 ^ (prefixWord ++ tailWord_1220873).sum := by decide
  have hdescent : baseEnd_1220873 < baseStart_1220873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220917 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_1220917 : Nat := 118140960795 + 1220917 * 2 ^ 59
def prefixEnd_1220917 : Nat := 4983230072969 + 3 ^ 40 * 1220917 * 2
def baseEnd_1220917 : Nat := 626917260245504890322611

theorem tailTrace_1220917 : CollatzResearch.WordTrace tailWord_1220917 prefixEnd_1220917 626917260245504890322611 := by
  unfold tailWord_1220917
  simp only [CollatzResearch.WordTrace]
  refine ⟨44530501317833699867901005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29687000878555799911934003 44530501317833699867901005)
  ·
    refine ⟨16698937994187637450462877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44530501317833699867901005 16698937994187637450462877)
    ·
      refine ⟨6262101747820364043923579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16698937994187637450462877 6262101747820364043923579)
      ·
        refine ⟨9393152621730546065885369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6262101747820364043923579 9393152621730546065885369)
        ·
          refine ⟨7044864466297909549414027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9393152621730546065885369 7044864466297909549414027)
          ·
            refine ⟨10567296699446864324121041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7044864466297909549414027 10567296699446864324121041)
            ·
              refine ⟨7925472524585148243090781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10567296699446864324121041 7925472524585148243090781)
              ·
                refine ⟨2972052196719430591159043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7925472524585148243090781 2972052196719430591159043)
                ·
                  refine ⟨4458078295079145886738565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972052196719430591159043 4458078295079145886738565)
                  ·
                    refine ⟨835889680327339853763481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4458078295079145886738565 835889680327339853763481)
                    ·
                      refine ⟨626917260245504890322611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835889680327339853763481 626917260245504890322611)
                      ·
                        rfl

theorem cell23_1220917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_1220917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220917 prefixEnd_1220917 := by exact prefixLift 1220917
  have htrace : WordTrace (prefixWord ++ tailWord_1220917) baseStart_1220917 baseEnd_1220917 := by
    simpa [prefixWord, tailWord_1220917, baseEnd_1220917] using wordTrace_append hprefix tailTrace_1220917
  have hstable : (prefixWord ++ tailWord_1220917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220917).length < 2 ^ (prefixWord ++ tailWord_1220917).sum := by decide
  have hdescent : baseEnd_1220917 < baseStart_1220917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220921 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1220921 : Nat := 118140960795 + 1220921 * 2 ^ 59
def prefixEnd_1220921 : Nat := 4983230072969 + 3 ^ 40 * 1220921 * 2
def baseEnd_1220921 : Nat := 626919314168122874672593

theorem tailTrace_1220921 : CollatzResearch.WordTrace tailWord_1220921 prefixEnd_1220921 626919314168122874672593 := by
  unfold tailWord_1220921
  simp only [CollatzResearch.WordTrace]
  refine ⟨44530647209819208551046617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29687098139879472367364411 44530647209819208551046617)
  ·
    refine ⟨33397985407364406413284963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44530647209819208551046617 33397985407364406413284963)
    ·
      refine ⟨50096978111046609619927445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33397985407364406413284963 50096978111046609619927445)
      ·
        refine ⟨2348295848955309825934099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50096978111046609619927445 2348295848955309825934099)
        ·
          refine ⟨3522443773432964738901149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348295848955309825934099 3522443773432964738901149)
          ·
            refine ⟨1320916415037361777087931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3522443773432964738901149 1320916415037361777087931)
            ·
              refine ⟨1981374622556042665631897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320916415037361777087931 1981374622556042665631897)
              ·
                refine ⟨1486030966917031999223923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981374622556042665631897 1486030966917031999223923)
                ·
                  refine ⟨2229046450375547998835885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486030966917031999223923 2229046450375547998835885)
                  ·
                    refine ⟨835892418890830499563457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229046450375547998835885 835892418890830499563457)
                    ·
                      refine ⟨626919314168122874672593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 835892418890830499563457 626919314168122874672593)
                      ·
                        rfl

theorem cell23_1220921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1220921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220921 prefixEnd_1220921 := by exact prefixLift 1220921
  have htrace : WordTrace (prefixWord ++ tailWord_1220921) baseStart_1220921 baseEnd_1220921 := by
    simpa [prefixWord, tailWord_1220921, baseEnd_1220921] using wordTrace_append hprefix tailTrace_1220921
  have hstable : (prefixWord ++ tailWord_1220921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220921).length < 2 ^ (prefixWord ++ tailWord_1220921).sum := by decide
  have hdescent : baseEnd_1220921 < baseStart_1220921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220953 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_1220953 : Nat := 118140960795 + 1220953 * 2 ^ 59
def prefixEnd_1220953 : Nat := 4983230072969 + 3 ^ 40 * 1220953 * 2
def baseEnd_1220953 : Nat := 208978581849688916490815

theorem tailTrace_1220953 : CollatzResearch.WordTrace tailWord_1220953 prefixEnd_1220953 208978581849688916490815 := by
  unfold tailWord_1220953
  simp only [CollatzResearch.WordTrace]
  refine ⟨44531814345703278016211513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29687876230468852010807675 44531814345703278016211513)
  ·
    refine ⟨33398860759277458512158635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44531814345703278016211513 33398860759277458512158635)
    ·
      refine ⟨50098291138916187768237953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33398860759277458512158635 50098291138916187768237953)
      ·
        refine ⟨37573718354187140826178465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50098291138916187768237953 37573718354187140826178465)
        ·
          refine ⟨28180288765640355619633849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37573718354187140826178465 28180288765640355619633849)
          ·
            refine ⟨21135216574230266714725387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28180288765640355619633849 21135216574230266714725387)
            ·
              refine ⟨31702824861345400072088081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21135216574230266714725387 31702824861345400072088081)
              ·
                refine ⟨23777118646009050054066061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31702824861345400072088081 23777118646009050054066061)
                ·
                  refine ⟨8916419492253393770274773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23777118646009050054066061 8916419492253393770274773)
                  ·
                    refine ⟨208978581849688916490815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8916419492253393770274773 208978581849688916490815)
                    ·
                      rfl

theorem cell23_1220953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_1220953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220953 prefixEnd_1220953 := by exact prefixLift 1220953
  have htrace : WordTrace (prefixWord ++ tailWord_1220953) baseStart_1220953 baseEnd_1220953 := by
    simpa [prefixWord, tailWord_1220953, baseEnd_1220953] using wordTrace_append hprefix tailTrace_1220953
  have hstable : (prefixWord ++ tailWord_1220953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220953).length < 2 ^ (prefixWord ++ tailWord_1220953).sum := by decide
  have hdescent : baseEnd_1220953 < baseStart_1220953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220967 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1220967 : Nat := 118140960795 + 1220967 * 2 ^ 59
def prefixEnd_1220967 : Nat := 4983230072969 + 3 ^ 40 * 1220967 * 2
def baseEnd_1220967 : Nat := 626942934278229694697381

theorem tailTrace_1220967 : CollatzResearch.WordTrace tailWord_1220967 prefixEnd_1220967 626942934278229694697381 := by
  unfold tailWord_1220967
  simp only [CollatzResearch.WordTrace]
  refine ⟨44532324967652558407221155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29688216645101705604814103 44532324967652558407221155)
  ·
    refine ⟨66798487451478837610831733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44532324967652558407221155 66798487451478837610831733)
    ·
      refine ⟨6262358198576141026015475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66798487451478837610831733 6262358198576141026015475)
      ·
        refine ⟨9393537297864211539023213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6262358198576141026015475 9393537297864211539023213)
        ·
          refine ⟨3522576486699079327133705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9393537297864211539023213 3522576486699079327133705)
          ·
            refine ⟨2641932365024309495350279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3522576486699079327133705 2641932365024309495350279)
            ·
              refine ⟨3962898547536464243025419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641932365024309495350279 3962898547536464243025419)
              ·
                refine ⟨5944347821304696364538129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962898547536464243025419 5944347821304696364538129)
                ·
                  refine ⟨4458260865978522273403597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5944347821304696364538129 4458260865978522273403597)
                  ·
                    refine ⟨1671847824741945852526349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4458260865978522273403597 1671847824741945852526349)
                    ·
                      refine ⟨626942934278229694697381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1671847824741945852526349 626942934278229694697381)
                      ·
                        rfl

theorem cell23_1220967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1220967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220967 prefixEnd_1220967 := by exact prefixLift 1220967
  have htrace : WordTrace (prefixWord ++ tailWord_1220967) baseStart_1220967 baseEnd_1220967 := by
    simpa [prefixWord, tailWord_1220967, baseEnd_1220967] using wordTrace_append hprefix tailTrace_1220967
  have hstable : (prefixWord ++ tailWord_1220967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220967).length < 2 ^ (prefixWord ++ tailWord_1220967).sum := by decide
  have hdescent : baseEnd_1220967 < baseStart_1220967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220983 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 10]
def baseStart_1220983 : Nat := 118140960795 + 1220983 * 2 ^ 59
def prefixEnd_1220983 : Nat := 4983230072969 + 3 ^ 40 * 1220983 * 2
def baseEnd_1220983 : Nat := 208983716656233877365769

theorem tailTrace_1220983 : CollatzResearch.WordTrace tailWord_1220983 prefixEnd_1220983 208983716656233877365769 := by
  unfold tailWord_1220983
  simp only [CollatzResearch.WordTrace]
  refine ⟨44532908535594593139803603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29688605690396395426535735 44532908535594593139803603)
  ·
    refine ⟨66799362803391889709705405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44532908535594593139803603 66799362803391889709705405)
    ·
      refine ⟨25049761051271958641139527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66799362803391889709705405 25049761051271958641139527)
      ·
        refine ⟨37574641576907937961709291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25049761051271958641139527 37574641576907937961709291)
        ·
          refine ⟨56361962365361906942563937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37574641576907937961709291 56361962365361906942563937)
          ·
            refine ⟨42271471774021430206922953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56361962365361906942563937 42271471774021430206922953)
            ·
              refine ⟨31703603830516072655192215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42271471774021430206922953 31703603830516072655192215)
              ·
                refine ⟨47555405745774108982788323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31703603830516072655192215 47555405745774108982788323)
                ·
                  refine ⟨71333108618661163474182485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47555405745774108982788323 71333108618661163474182485)
                  ·
                    refine ⟨208983716656233877365769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 71333108618661163474182485 208983716656233877365769)
                    ·
                      rfl

theorem cell23_1220983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_1220983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220983 prefixEnd_1220983 := by exact prefixLift 1220983
  have htrace : WordTrace (prefixWord ++ tailWord_1220983) baseStart_1220983 baseEnd_1220983 := by
    simpa [prefixWord, tailWord_1220983, baseEnd_1220983] using wordTrace_append hprefix tailTrace_1220983
  have hstable : (prefixWord ++ tailWord_1220983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220983).length < 2 ^ (prefixWord ++ tailWord_1220983).sum := by decide
  have hdescent : baseEnd_1220983 < baseStart_1220983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220987 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 2, 5]
def baseStart_1220987 : Nat := 118140960795 + 1220987 * 2 ^ 59
def prefixEnd_1220987 : Nat := 4983230072969 + 3 ^ 40 * 1220987 * 2
def baseEnd_1220987 : Nat := 208984401297106538815763

theorem tailTrace_1220987 : CollatzResearch.WordTrace tailWord_1220987 prefixEnd_1220987 208984401297106538815763 := by
  unfold tailWord_1220987
  simp only [CollatzResearch.WordTrace]
  refine ⟨44533054427580101822949215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29688702951720067881966143 44533054427580101822949215)
  ·
    refine ⟨66799581641370152734423823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44533054427580101822949215 66799581641370152734423823)
    ·
      refine ⟨100199372462055229101635735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66799581641370152734423823 100199372462055229101635735)
      ·
        refine ⟨150299058693082843652453603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100199372462055229101635735 150299058693082843652453603)
        ·
          refine ⟨225448588039624265478680405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150299058693082843652453603 225448588039624265478680405)
          ·
            refine ⟨1320987820544673430539143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 225448588039624265478680405 1320987820544673430539143)
            ·
              refine ⟨1981481730817010145808715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320987820544673430539143 1981481730817010145808715)
              ·
                refine ⟨2972222596225515218713073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981481730817010145808715 2972222596225515218713073)
                ·
                  refine ⟨2229166947169136414034805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972222596225515218713073 2229166947169136414034805)
                  ·
                    refine ⟨208984401297106538815763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2229166947169136414034805 208984401297106538815763)
                    ·
                      rfl

theorem cell23_1220987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 5].length) (baseStart_1220987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1220987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1220987 prefixEnd_1220987 := by exact prefixLift 1220987
  have htrace : WordTrace (prefixWord ++ tailWord_1220987) baseStart_1220987 baseEnd_1220987 := by
    simpa [prefixWord, tailWord_1220987, baseEnd_1220987] using wordTrace_append hprefix tailTrace_1220987
  have hstable : (prefixWord ++ tailWord_1220987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220987).length < 2 ^ (prefixWord ++ tailWord_1220987).sum := by decide
  have hdescent : baseEnd_1220987 < baseStart_1220987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221017 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_1221017 : Nat := 118140960795 + 1221017 * 2 ^ 59
def prefixEnd_1221017 : Nat := 4983230072969 + 3 ^ 40 * 1221017 * 2
def baseEnd_1221017 : Nat := 208989536103651499690717

theorem tailTrace_1221017 : CollatzResearch.WordTrace tailWord_1221017 prefixEnd_1221017 208989536103651499690717 := by
  unfold tailWord_1221017
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534148617471416946541305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29689432411647611297694203 44534148617471416946541305)
  ·
    refine ⟨33400611463103562709905979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44534148617471416946541305 33400611463103562709905979)
    ·
      refine ⟨50100917194655344064858969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33400611463103562709905979 50100917194655344064858969)
      ·
        refine ⟨37575687895991508048644227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50100917194655344064858969 37575687895991508048644227)
        ·
          refine ⟨56363531843987262072966341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37575687895991508048644227 56363531843987262072966341)
          ·
            refine ⟨10568162220747611638681189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56363531843987262072966341 10568162220747611638681189)
            ·
              refine ⟨1981530416390177182252723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10568162220747611638681189 1981530416390177182252723)
              ·
                refine ⟨2972295624585265773379085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981530416390177182252723 2972295624585265773379085)
                ·
                  refine ⟨1114610859219474665017157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2972295624585265773379085 1114610859219474665017157)
                  ·
                    refine ⟨208989536103651499690717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114610859219474665017157 208989536103651499690717)
                    ·
                      rfl

theorem cell23_1221017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_1221017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221017 prefixEnd_1221017 := by exact prefixLift 1221017
  have htrace : WordTrace (prefixWord ++ tailWord_1221017) baseStart_1221017 baseEnd_1221017 := by
    simpa [prefixWord, tailWord_1221017, baseEnd_1221017] using wordTrace_append hprefix tailTrace_1221017
  have hstable : (prefixWord ++ tailWord_1221017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221017).length < 2 ^ (prefixWord ++ tailWord_1221017).sum := by decide
  have hdescent : baseEnd_1221017 < baseStart_1221017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221068 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_1221068 : Nat := 118140960795 + 1221068 * 2 ^ 59
def prefixEnd_1221068 : Nat := 4983230072969 + 3 ^ 40 * 1221068 * 2
def baseEnd_1221068 : Nat := 208998265274777933178139

theorem tailTrace_1221068 : CollatzResearch.WordTrace tailWord_1221068 prefixEnd_1221068 208998265274777933178139 := by
  unfold tailWord_1221068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22268004370143326328323929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29690672493524435104431905 22268004370143326328323929)
  ·
    refine ⟨16701003277607494746242947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22268004370143326328323929 16701003277607494746242947)
    ·
      refine ⟨25051504916411242119364421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16701003277607494746242947 25051504916411242119364421)
      ·
        refine ⟨4697157171827107897380829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25051504916411242119364421 4697157171827107897380829)
        ·
          refine ⟨1761433939435165461517811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4697157171827107897380829 1761433939435165461517811)
          ·
            refine ⟨2642150909152748192276717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761433939435165461517811 2642150909152748192276717)
            ·
              refine ⟨990806590932280572103769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2642150909152748192276717 990806590932280572103769)
              ·
                refine ⟨743104943199210429077827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990806590932280572103769 743104943199210429077827)
                ·
                  refine ⟨1114657414798815643616741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743104943199210429077827 1114657414798815643616741)
                  ·
                    refine ⟨208998265274777933178139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114657414798815643616741 208998265274777933178139)
                    ·
                      rfl

theorem cell23_1221068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_1221068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221068 prefixEnd_1221068 := by exact prefixLift 1221068
  have htrace : WordTrace (prefixWord ++ tailWord_1221068) baseStart_1221068 baseEnd_1221068 := by
    simpa [prefixWord, tailWord_1221068, baseEnd_1221068] using wordTrace_append hprefix tailTrace_1221068
  have hstable : (prefixWord ++ tailWord_1221068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221068).length < 2 ^ (prefixWord ++ tailWord_1221068).sum := by decide
  have hdescent : baseEnd_1221068 < baseStart_1221068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221070 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1221070 : Nat := 118140960795 + 1221070 * 2 ^ 59
def prefixEnd_1221070 : Nat := 4983230072969 + 3 ^ 40 * 1221070 * 2
def baseEnd_1221070 : Nat := 626995822785642791709407

theorem tailTrace_1221070 : CollatzResearch.WordTrace tailWord_1221070 prefixEnd_1221070 626995822785642791709407 := by
  unfold tailWord_1221070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567010210784925874777583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29690721124186271332147109 5567010210784925874777583)
  ·
    refine ⟨8350515316177388812166375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567010210784925874777583 8350515316177388812166375)
    ·
      refine ⟨12525772974266083218249563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350515316177388812166375 12525772974266083218249563)
      ·
        refine ⟨18788659461399124827374345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12525772974266083218249563 18788659461399124827374345)
        ·
          refine ⟨14091494596049343620530759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18788659461399124827374345 14091494596049343620530759)
          ·
            refine ⟨21137241894074015430796139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091494596049343620530759 21137241894074015430796139)
            ·
              refine ⟨31705862841111023146194209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21137241894074015430796139 31705862841111023146194209)
              ·
                refine ⟨23779397130833267359645657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31705862841111023146194209 23779397130833267359645657)
                ·
                  refine ⟨17834547848124950519734243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23779397130833267359645657 17834547848124950519734243)
                  ·
                    refine ⟨26751821772187425779601365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17834547848124950519734243 26751821772187425779601365)
                    ·
                      refine ⟨626995822785642791709407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26751821772187425779601365 626995822785642791709407)
                      ·
                        rfl

theorem cell23_1221070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1221070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221070 prefixEnd_1221070 := by exact prefixLift 1221070
  have htrace : WordTrace (prefixWord ++ tailWord_1221070) baseStart_1221070 baseEnd_1221070 := by
    simpa [prefixWord, tailWord_1221070, baseEnd_1221070] using wordTrace_append hprefix tailTrace_1221070
  have hstable : (prefixWord ++ tailWord_1221070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221070).length < 2 ^ (prefixWord ++ tailWord_1221070).sum := by decide
  have hdescent : baseEnd_1221070 < baseStart_1221070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221080 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1221080 : Nat := 118140960795 + 1221080 * 2 ^ 59
def prefixEnd_1221080 : Nat := 4983230072969 + 3 ^ 40 * 1221080 * 2
def baseEnd_1221080 : Nat := 627000957592187752584361

theorem tailTrace_1221080 : CollatzResearch.WordTrace tailWord_1221080 prefixEnd_1221080 627000957592187752584361 := by
  unfold tailWord_1221080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22268223208121589353042347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29690964277495452470723129 22268223208121589353042347)
  ·
    refine ⟨33402334812182384029563521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22268223208121589353042347 33402334812182384029563521)
    ·
      refine ⟨25051751109136788022172641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33402334812182384029563521 25051751109136788022172641)
      ·
        refine ⟨18788813331852591016629481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25051751109136788022172641 18788813331852591016629481)
        ·
          refine ⟨14091609998889443262472111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18788813331852591016629481 14091609998889443262472111)
          ·
            refine ⟨21137414998334164893708167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091609998889443262472111 21137414998334164893708167)
            ·
              refine ⟨31706122497501247340562251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21137414998334164893708167 31706122497501247340562251)
              ·
                refine ⟨47559183746251871010843377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31706122497501247340562251 47559183746251871010843377)
                ·
                  refine ⟨35669387809688903258132533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47559183746251871010843377 35669387809688903258132533)
                  ·
                    refine ⟨3344005107158334680449925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35669387809688903258132533 3344005107158334680449925)
                    ·
                      refine ⟨627000957592187752584361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3344005107158334680449925 627000957592187752584361)
                      ·
                        rfl

theorem cell23_1221080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1221080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221080 prefixEnd_1221080 := by exact prefixLift 1221080
  have htrace : WordTrace (prefixWord ++ tailWord_1221080) baseStart_1221080 baseEnd_1221080 := by
    simpa [prefixWord, tailWord_1221080, baseEnd_1221080] using wordTrace_append hprefix tailTrace_1221080
  have hstable : (prefixWord ++ tailWord_1221080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221080).length < 2 ^ (prefixWord ++ tailWord_1221080).sum := by decide
  have hdescent : baseEnd_1221080 < baseStart_1221080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221097 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_1221097 : Nat := 118140960795 + 1221097 * 2 ^ 59
def prefixEnd_1221097 : Nat := 4983230072969 + 3 ^ 40 * 1221097 * 2
def baseEnd_1221097 : Nat := 627009686763314186071783

theorem tailTrace_1221097 : CollatzResearch.WordTrace tailWord_1221097 prefixEnd_1221097 627009686763314186071783 := by
  unfold tailWord_1221097
  simp only [CollatzResearch.WordTrace]
  refine ⟨44537066457181590609453545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29691377638121060406302363 44537066457181590609453545)
  ·
    refine ⟨33402799842886192957090159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44537066457181590609453545 33402799842886192957090159)
    ·
      refine ⟨50104199764329289435635239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33402799842886192957090159 50104199764329289435635239)
      ·
        refine ⟨75156299646493934153452859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50104199764329289435635239 75156299646493934153452859)
        ·
          refine ⟨112734449469740901230179289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75156299646493934153452859 112734449469740901230179289)
          ·
            refine ⟨84550837102305675922634467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112734449469740901230179289 84550837102305675922634467)
            ·
              refine ⟨126826255653458513883951701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84550837102305675922634467 126826255653458513883951701)
              ·
                refine ⟨1486245183438966959577559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 126826255653458513883951701 1486245183438966959577559)
                ·
                  refine ⟨2229367775158450439366339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486245183438966959577559 2229367775158450439366339)
                  ·
                    refine ⟨3344051662737675659049509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229367775158450439366339 3344051662737675659049509)
                    ·
                      refine ⟨627009686763314186071783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3344051662737675659049509 627009686763314186071783)
                      ·
                        rfl

theorem cell23_1221097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_1221097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221097 prefixEnd_1221097 := by exact prefixLift 1221097
  have htrace : WordTrace (prefixWord ++ tailWord_1221097) baseStart_1221097 baseEnd_1221097 := by
    simpa [prefixWord, tailWord_1221097, baseEnd_1221097] using wordTrace_append hprefix tailTrace_1221097
  have hstable : (prefixWord ++ tailWord_1221097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221097).length < 2 ^ (prefixWord ++ tailWord_1221097).sum := by decide
  have hdescent : baseEnd_1221097 < baseStart_1221097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221101 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1221101 : Nat := 118140960795 + 1221101 * 2 ^ 59
def prefixEnd_1221101 : Nat := 4983230072969 + 3 ^ 40 * 1221101 * 2
def baseEnd_1221101 : Nat := 627011740685932170421765

theorem tailTrace_1221101 : CollatzResearch.WordTrace tailWord_1221101 prefixEnd_1221101 627011740685932170421765 := by
  unfold tailWord_1221101
  simp only [CollatzResearch.WordTrace]
  refine ⟨44537212349167099292599157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29691474899444732861732771 44537212349167099292599157)
  ·
    refine ⟨4175363657734415558681171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44537212349167099292599157 4175363657734415558681171)
    ·
      refine ⟨6263045486601623338021757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175363657734415558681171 6263045486601623338021757)
      ·
        refine ⟨2348642057475608751758159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6263045486601623338021757 2348642057475608751758159)
        ·
          refine ⟨3522963086213413127637239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348642057475608751758159 3522963086213413127637239)
          ·
            refine ⟨5284444629320119691455859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522963086213413127637239 5284444629320119691455859)
            ·
              refine ⟨7926666943980179537183789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284444629320119691455859 7926666943980179537183789)
              ·
                refine ⟨2972500103992567326443921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7926666943980179537183789 2972500103992567326443921)
                ·
                  refine ⟨2229375077994425494832941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972500103992567326443921 2229375077994425494832941)
                  ·
                    refine ⟨836015654247909560562353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229375077994425494832941 836015654247909560562353)
                    ·
                      refine ⟨627011740685932170421765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836015654247909560562353 627011740685932170421765)
                      ·
                        rfl

theorem cell23_1221101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1221101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221101 prefixEnd_1221101 := by exact prefixLift 1221101
  have htrace : WordTrace (prefixWord ++ tailWord_1221101) baseStart_1221101 baseEnd_1221101 := by
    simpa [prefixWord, tailWord_1221101, baseEnd_1221101] using wordTrace_append hprefix tailTrace_1221101
  have hstable : (prefixWord ++ tailWord_1221101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221101).length < 2 ^ (prefixWord ++ tailWord_1221101).sum := by decide
  have hdescent : baseEnd_1221101 < baseStart_1221101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221114 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_1221114 : Nat := 118140960795 + 1221114 * 2 ^ 59
def prefixEnd_1221114 : Nat := 4983230072969 + 3 ^ 40 * 1221114 * 2
def baseEnd_1221114 : Nat := 627018415934440619559205

theorem tailTrace_1221114 : CollatzResearch.WordTrace tailWord_1221114 prefixEnd_1221114 627018415934440619559205 := by
  unfold tailWord_1221114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134421624530000628205599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29691790998746668341881597 11134421624530000628205599)
  ·
    refine ⟨16701632436795000942308399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134421624530000628205599 16701632436795000942308399)
    ·
      refine ⟨25052448655192501413462599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16701632436795000942308399 25052448655192501413462599)
      ·
        refine ⟨37578672982788752120193899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25052448655192501413462599 37578672982788752120193899)
        ·
          refine ⟨56368009474183128180290849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37578672982788752120193899 56368009474183128180290849)
          ·
            refine ⟨42276007105637346135218137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56368009474183128180290849 42276007105637346135218137)
            ·
              refine ⟨31707005329228009601413603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42276007105637346135218137 31707005329228009601413603)
              ·
                refine ⟨47560507993842014402120405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31707005329228009601413603 47560507993842014402120405)
                ·
                  refine ⟨1114699406105672212549697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47560507993842014402120405 1114699406105672212549697)
                  ·
                    refine ⟨836024554579254159412273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114699406105672212549697 836024554579254159412273)
                    ·
                      refine ⟨627018415934440619559205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836024554579254159412273 627018415934440619559205)
                      ·
                        rfl

theorem cell23_1221114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_1221114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221114 prefixEnd_1221114 := by exact prefixLift 1221114
  have htrace : WordTrace (prefixWord ++ tailWord_1221114) baseStart_1221114 baseEnd_1221114 := by
    simpa [prefixWord, tailWord_1221114, baseEnd_1221114] using wordTrace_append hprefix tailTrace_1221114
  have hstable : (prefixWord ++ tailWord_1221114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221114).length < 2 ^ (prefixWord ++ tailWord_1221114).sum := by decide
  have hdescent : baseEnd_1221114 < baseStart_1221114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221134 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1221134 : Nat := 118140960795 + 1221134 * 2 ^ 59
def prefixEnd_1221134 : Nat := 4983230072969 + 3 ^ 40 * 1221134 * 2
def baseEnd_1221134 : Nat := 627028685547530541309113

theorem tailTrace_1221134 : CollatzResearch.WordTrace tailWord_1221134 prefixEnd_1221134 627028685547530541309113 := by
  unfold tailWord_1221134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567301994755943241068807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29692277305365030619033637 5567301994755943241068807)
  ·
    refine ⟨8350952992133914861603211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567301994755943241068807 8350952992133914861603211)
    ·
      refine ⟨12526429488200872292404817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350952992133914861603211 12526429488200872292404817)
      ·
        refine ⟨9394822116150654219303613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12526429488200872292404817 9394822116150654219303613)
        ·
          refine ⟨3523058293556495332238855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9394822116150654219303613 3523058293556495332238855)
          ·
            refine ⟨5284587440334742998358283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523058293556495332238855 5284587440334742998358283)
            ·
              refine ⟨7926881160502114497537425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284587440334742998358283 7926881160502114497537425)
              ·
                refine ⟨5945160870376585873153069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7926881160502114497537425 5945160870376585873153069)
                ·
                  refine ⟨2229435326391219702432401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5945160870376585873153069 2229435326391219702432401)
                  ·
                    refine ⟨1672076494793414776824301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229435326391219702432401 1672076494793414776824301)
                    ·
                      refine ⟨627028685547530541309113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1672076494793414776824301 627028685547530541309113)
                      ·
                        rfl

theorem cell23_1221134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1221134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221134 prefixEnd_1221134 := by exact prefixLift 1221134
  have htrace : WordTrace (prefixWord ++ tailWord_1221134) baseStart_1221134 baseEnd_1221134 := by
    simpa [prefixWord, tailWord_1221134, baseEnd_1221134] using wordTrace_append hprefix tailTrace_1221134
  have hstable : (prefixWord ++ tailWord_1221134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221134).length < 2 ^ (prefixWord ++ tailWord_1221134).sum := by decide
  have hdescent : baseEnd_1221134 < baseStart_1221134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221144 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1221144 : Nat := 118140960795 + 1221144 * 2 ^ 59
def prefixEnd_1221144 : Nat := 4983230072969 + 3 ^ 40 * 1221144 * 2
def baseEnd_1221144 : Nat := 627033820354075502184067

theorem tailTrace_1221144 : CollatzResearch.WordTrace tailWord_1221144 prefixEnd_1221144 627033820354075502184067 := by
  unfold tailWord_1221144
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269390344005658818207243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29692520458674211757609657 22269390344005658818207243)
  ·
    refine ⟨33404085516008488227310865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22269390344005658818207243 33404085516008488227310865)
    ·
      refine ⟨25053064137006366170483149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33404085516008488227310865 25053064137006366170483149)
      ·
        refine ⟨9394899051377387313931181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25053064137006366170483149 9394899051377387313931181)
        ·
          refine ⟨3523087144266520242724193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9394899051377387313931181 3523087144266520242724193)
          ·
            refine ⟨2642315358199890182043145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3523087144266520242724193 2642315358199890182043145)
            ·
              refine ⟨1981736518649917636532359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642315358199890182043145 1981736518649917636532359)
              ·
                refine ⟨2972604777974876454798539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981736518649917636532359 2972604777974876454798539)
                ·
                  refine ⟨4458907166962314682197809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972604777974876454798539 4458907166962314682197809)
                  ·
                    refine ⟨3344180375221736011648357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458907166962314682197809 3344180375221736011648357)
                    ·
                      refine ⟨627033820354075502184067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3344180375221736011648357 627033820354075502184067)
                      ·
                        rfl

theorem cell23_1221144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1221144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221144 prefixEnd_1221144 := by exact prefixLift 1221144
  have htrace : WordTrace (prefixWord ++ tailWord_1221144) baseStart_1221144 baseEnd_1221144 := by
    simpa [prefixWord, tailWord_1221144, baseEnd_1221144] using wordTrace_append hprefix tailTrace_1221144
  have hstable : (prefixWord ++ tailWord_1221144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221144).length < 2 ^ (prefixWord ++ tailWord_1221144).sum := by decide
  have hdescent : baseEnd_1221144 < baseStart_1221144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221165 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1221165 : Nat := 118140960795 + 1221165 * 2 ^ 59
def prefixEnd_1221165 : Nat := 4983230072969 + 3 ^ 40 * 1221165 * 2
def baseEnd_1221165 : Nat := 627044603447819920021471

theorem tailTrace_1221165 : CollatzResearch.WordTrace tailWord_1221165 prefixEnd_1221165 627044603447819920021471 := by
  unfold tailWord_1221165
  simp only [CollatzResearch.WordTrace]
  refine ⟨44539546620935238222928949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29693031080623492148619299 44539546620935238222928949)
  ·
    refine ⟨4175582495712678583399589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44539546620935238222928949 4175582495712678583399589)
    ·
      refine ⟨782921717946127234387423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4175582495712678583399589 782921717946127234387423)
      ·
        refine ⟨1174382576919190851581135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782921717946127234387423 1174382576919190851581135)
        ·
          refine ⟨1761573865378786277371703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174382576919190851581135 1761573865378786277371703)
          ·
            refine ⟨2642360798068179416057555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761573865378786277371703 2642360798068179416057555)
            ·
              refine ⟨3963541197102269124086333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642360798068179416057555 3963541197102269124086333)
              ·
                refine ⟨1486327948913350921532375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3963541197102269124086333 1486327948913350921532375)
                ·
                  refine ⟨2229491923370026382298563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486327948913350921532375 2229491923370026382298563)
                  ·
                    refine ⟨3344237885055039573447845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229491923370026382298563 3344237885055039573447845)
                    ·
                      refine ⟨627044603447819920021471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3344237885055039573447845 627044603447819920021471)
                      ·
                        rfl

theorem cell23_1221165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1221165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221165 prefixEnd_1221165 := by exact prefixLift 1221165
  have htrace : WordTrace (prefixWord ++ tailWord_1221165) baseStart_1221165 baseEnd_1221165 := by
    simpa [prefixWord, tailWord_1221165, baseEnd_1221165] using wordTrace_append hprefix tailTrace_1221165
  have hstable : (prefixWord ++ tailWord_1221165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221165).length < 2 ^ (prefixWord ++ tailWord_1221165).sum := by decide
  have hdescent : baseEnd_1221165 < baseStart_1221165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221181 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1221181 : Nat := 118140960795 + 1221181 * 2 ^ 59
def prefixEnd_1221181 : Nat := 4983230072969 + 3 ^ 40 * 1221181 * 2
def baseEnd_1221181 : Nat := 627052819138291857421397

theorem tailTrace_1221181 : CollatzResearch.WordTrace tailWord_1221181 prefixEnd_1221181 627052819138291857421397 := by
  unfold tailWord_1221181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540130188877272955511397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29693420125918181970340931 44540130188877272955511397)
  ·
    refine ⟨8351274410414488679158387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44540130188877272955511397 8351274410414488679158387)
    ·
      refine ⟨12526911615621733018737581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351274410414488679158387 12526911615621733018737581)
      ·
        refine ⟨4697591855858149882026593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12526911615621733018737581 4697591855858149882026593)
        ·
          refine ⟨3523193891893612411519945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4697591855858149882026593 3523193891893612411519945)
          ·
            refine ⟨2642395418920209308639959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3523193891893612411519945 2642395418920209308639959)
            ·
              refine ⟨3963593128380313962959939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642395418920209308639959 3963593128380313962959939)
              ·
                refine ⟨5945389692570470944439909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963593128380313962959939 5945389692570470944439909)
                ·
                  refine ⟨1114760567356963302082483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5945389692570470944439909 1114760567356963302082483)
                  ·
                    refine ⟨1672140851035444953123725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1114760567356963302082483 1672140851035444953123725)
                    ·
                      refine ⟨627052819138291857421397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1672140851035444953123725 627052819138291857421397)
                      ·
                        rfl

theorem cell23_1221181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1221181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221181 prefixEnd_1221181 := by exact prefixLift 1221181
  have htrace : WordTrace (prefixWord ++ tailWord_1221181) baseStart_1221181 baseEnd_1221181 := by
    simpa [prefixWord, tailWord_1221181, baseEnd_1221181] using wordTrace_append hprefix tailTrace_1221181
  have hstable : (prefixWord ++ tailWord_1221181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221181).length < 2 ^ (prefixWord ++ tailWord_1221181).sum := by decide
  have hdescent : baseEnd_1221181 < baseStart_1221181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221207 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1221207 : Nat := 118140960795 + 1221207 * 2 ^ 59
def prefixEnd_1221207 : Nat := 4983230072969 + 3 ^ 40 * 1221207 * 2
def baseEnd_1221207 : Nat := 627066169635308755696277

theorem tailTrace_1221207 : CollatzResearch.WordTrace tailWord_1221207 prefixEnd_1221207 627066169635308755696277 := by
  unfold tailWord_1221207
  simp only [CollatzResearch.WordTrace]
  refine ⟨44541078486783079395957875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29694052324522052930638583 44541078486783079395957875)
  ·
    refine ⟨66811617730174619093936813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44541078486783079395957875 66811617730174619093936813)
    ·
      refine ⟨25054356648815482160226305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66811617730174619093936813 25054356648815482160226305)
      ·
        refine ⟨18790767486611611620169729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25054356648815482160226305 18790767486611611620169729)
        ·
          refine ⟨14093075614958708715127297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18790767486611611620169729 14093075614958708715127297)
          ·
            refine ⟨10569806711219031536345473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14093075614958708715127297 10569806711219031536345473)
            ·
              refine ⟨7927355033414273652259105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569806711219031536345473 7927355033414273652259105)
              ·
                refine ⟨5945516275060705239194329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7927355033414273652259105 5945516275060705239194329)
                ·
                  refine ⟨4459137206295528929395747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5945516275060705239194329 4459137206295528929395747)
                  ·
                    refine ⟨6688705809443293394093621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4459137206295528929395747 6688705809443293394093621)
                    ·
                      refine ⟨627066169635308755696277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6688705809443293394093621 627066169635308755696277)
                      ·
                        rfl

theorem cell23_1221207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1221207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221207 prefixEnd_1221207 := by exact prefixLift 1221207
  have htrace : WordTrace (prefixWord ++ tailWord_1221207) baseStart_1221207 baseEnd_1221207 := by
    simpa [prefixWord, tailWord_1221207, baseEnd_1221207] using wordTrace_append hprefix tailTrace_1221207
  have hstable : (prefixWord ++ tailWord_1221207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221207).length < 2 ^ (prefixWord ++ tailWord_1221207).sum := by decide
  have hdescent : baseEnd_1221207 < baseStart_1221207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221244 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 5]
def baseStart_1221244 : Nat := 118140960795 + 1221244 * 2 ^ 59
def prefixEnd_1221244 : Nat := 4983230072969 + 3 ^ 40 * 1221244 * 2
def baseEnd_1221244 : Nat := 69676129824391678992623

theorem tailTrace_1221244 : CollatzResearch.WordTrace tailWord_1221244 prefixEnd_1221244 69676129824391678992623 := by
  unfold tailWord_1221244
  simp only [CollatzResearch.WordTrace]
  refine ⟨22271213993824517357527393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29694951991766023143369857 22271213993824517357527393)
  ·
    refine ⟨16703410495368388018145545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22271213993824517357527393 16703410495368388018145545)
    ·
      refine ⟨12527557871526291013609159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16703410495368388018145545 12527557871526291013609159)
      ·
        refine ⟨18791336807289436520413739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527557871526291013609159 18791336807289436520413739)
        ·
          refine ⟨28187005210934154780620609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18791336807289436520413739 28187005210934154780620609)
          ·
            refine ⟨21140253908200616085465457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28187005210934154780620609 21140253908200616085465457)
            ·
              refine ⟨15855190431150462064099093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21140253908200616085465457 15855190431150462064099093)
              ·
                refine ⟨743212051460177909254645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15855190431150462064099093 743212051460177909254645)
                ·
                  refine ⟨69676129824391678992623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 743212051460177909254645 69676129824391678992623)
                  ·
                    rfl

theorem cell23_1221244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_1221244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221244 prefixEnd_1221244 := by exact prefixLift 1221244
  have htrace : WordTrace (prefixWord ++ tailWord_1221244) baseStart_1221244 baseEnd_1221244 := by
    simpa [prefixWord, tailWord_1221244, baseEnd_1221244] using wordTrace_append hprefix tailTrace_1221244
  have hstable : (prefixWord ++ tailWord_1221244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221244).length < 2 ^ (prefixWord ++ tailWord_1221244).sum := by decide
  have hdescent : baseEnd_1221244 < baseStart_1221244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221257 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_1221257 : Nat := 118140960795 + 1221257 * 2 ^ 59
def prefixEnd_1221257 : Nat := 4983230072969 + 3 ^ 40 * 1221257 * 2
def baseEnd_1221257 : Nat := 209030614556011186690349

theorem tailTrace_1221257 : CollatzResearch.WordTrace tailWord_1221257 prefixEnd_1221257 209030614556011186690349 := by
  unfold tailWord_1221257
  simp only [CollatzResearch.WordTrace]
  refine ⟨44542902136601937935278025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29695268091067958623518683 44542902136601937935278025)
  ·
    refine ⟨33407176602451453451458519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44542902136601937935278025 33407176602451453451458519)
    ·
      refine ⟨50110764903677180177187779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33407176602451453451458519 50110764903677180177187779)
      ·
        refine ⟨75166147355515770265781669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50110764903677180177187779 75166147355515770265781669)
        ·
          refine ⟨14093652629159206924834063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75166147355515770265781669 14093652629159206924834063)
          ·
            refine ⟨21140478943738810387251095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14093652629159206924834063 21140478943738810387251095)
            ·
              refine ⟨31710718415608215580876643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21140478943738810387251095 31710718415608215580876643)
              ·
                refine ⟨47566077623412323371314965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31710718415608215580876643 47566077623412323371314965)
                ·
                  refine ⟨2229659888597452658030389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47566077623412323371314965 2229659888597452658030389)
                  ·
                    refine ⟨209030614556011186690349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2229659888597452658030389 209030614556011186690349)
                    ·
                      rfl

theorem cell23_1221257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_1221257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221257 prefixEnd_1221257 := by exact prefixLift 1221257
  have htrace : WordTrace (prefixWord ++ tailWord_1221257) baseStart_1221257 baseEnd_1221257 := by
    simpa [prefixWord, tailWord_1221257, baseEnd_1221257] using wordTrace_append hprefix tailTrace_1221257
  have hstable : (prefixWord ++ tailWord_1221257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221257).length < 2 ^ (prefixWord ++ tailWord_1221257).sum := by decide
  have hdescent : baseEnd_1221257 < baseStart_1221257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221307 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_1221307 : Nat := 118140960795 + 1221307 * 2 ^ 59
def prefixEnd_1221307 : Nat := 4983230072969 + 3 ^ 40 * 1221307 * 2
def baseEnd_1221307 : Nat := 627117517700758364445817

theorem tailTrace_1221307 : CollatzResearch.WordTrace tailWord_1221307 prefixEnd_1221307 627117517700758364445817 := by
  unfold tailWord_1221307
  simp only [CollatzResearch.WordTrace]
  refine ⟨44544725786420796474598175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29696483857613864316398783 44544725786420796474598175)
  ·
    refine ⟨66817088679631194711897263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44544725786420796474598175 66817088679631194711897263)
    ·
      refine ⟨100225633019446792067845895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66817088679631194711897263 100225633019446792067845895)
      ·
        refine ⟨150338449529170188101768843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100225633019446792067845895 150338449529170188101768843)
        ·
          refine ⟨225507674293755282152653265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150338449529170188101768843 225507674293755282152653265)
          ·
            refine ⟨169130755720316461614489949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225507674293755282152653265 169130755720316461614489949)
            ·
              refine ⟨63424033395118673105433731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169130755720316461614489949 63424033395118673105433731)
              ·
                refine ⟨95136050092678009658150597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63424033395118673105433731 95136050092678009658150597)
                ·
                  refine ⟨17838009392377126810903237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95136050092678009658150597 17838009392377126810903237)
                  ·
                    refine ⟨3344626761070711277044357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17838009392377126810903237 3344626761070711277044357)
                    ·
                      refine ⟨627117517700758364445817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3344626761070711277044357 627117517700758364445817)
                      ·
                        rfl

theorem cell23_1221307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_1221307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221307 prefixEnd_1221307 := by exact prefixLift 1221307
  have htrace : WordTrace (prefixWord ++ tailWord_1221307) baseStart_1221307 baseEnd_1221307 := by
    simpa [prefixWord, tailWord_1221307, baseEnd_1221307] using wordTrace_append hprefix tailTrace_1221307
  have hstable : (prefixWord ++ tailWord_1221307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221307).length < 2 ^ (prefixWord ++ tailWord_1221307).sum := by decide
  have hdescent : baseEnd_1221307 < baseStart_1221307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221311 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 2, 4, 2]
def baseStart_1221311 : Nat := 118140960795 + 1221311 * 2 ^ 59
def prefixEnd_1221311 : Nat := 4983230072969 + 3 ^ 40 * 1221311 * 2
def baseEnd_1221311 : Nat := 627119571623376348795799

theorem tailTrace_1221311 : CollatzResearch.WordTrace tailWord_1221311 prefixEnd_1221311 627119571623376348795799 := by
  unfold tailWord_1221311
  simp only [CollatzResearch.WordTrace]
  refine ⟨44544871678406305157743787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29696581118937536771829191 44544871678406305157743787)
  ·
    refine ⟨66817307517609457736615681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44544871678406305157743787 66817307517609457736615681)
    ·
      refine ⟨50112980638207093302461761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66817307517609457736615681 50112980638207093302461761)
      ·
        refine ⟨37584735478655319976846321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50112980638207093302461761 37584735478655319976846321)
        ·
          refine ⟨28188551608991489982634741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37584735478655319976846321 28188551608991489982634741)
          ·
            refine ⟨2642676713342952185872007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28188551608991489982634741 2642676713342952185872007)
            ·
              refine ⟨3964015070014428278808011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642676713342952185872007 3964015070014428278808011)
              ·
                refine ⟨5946022605021642418212017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964015070014428278808011 5946022605021642418212017)
                ·
                  refine ⟨4459516953766231813659013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5946022605021642418212017 4459516953766231813659013)
                  ·
                    refine ⟨836159428831168465061065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459516953766231813659013 836159428831168465061065)
                    ·
                      refine ⟨627119571623376348795799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836159428831168465061065 627119571623376348795799)
                      ·
                        rfl

theorem cell23_1221311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_1221311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221311 prefixEnd_1221311 := by exact prefixLift 1221311
  have htrace : WordTrace (prefixWord ++ tailWord_1221311) baseStart_1221311 baseEnd_1221311 := by
    simpa [prefixWord, tailWord_1221311, baseEnd_1221311] using wordTrace_append hprefix tailTrace_1221311
  have hstable : (prefixWord ++ tailWord_1221311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221311).length < 2 ^ (prefixWord ++ tailWord_1221311).sum := by decide
  have hdescent : baseEnd_1221311 < baseStart_1221311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221325 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1221325 : Nat := 118140960795 + 1221325 * 2 ^ 59
def prefixEnd_1221325 : Nat := 4983230072969 + 3 ^ 40 * 1221325 * 2
def baseEnd_1221325 : Nat := 209042253450846431340245

theorem tailTrace_1221325 : CollatzResearch.WordTrace tailWord_1221325 prefixEnd_1221325 209042253450846431340245 := by
  unfold tailWord_1221325
  simp only [CollatzResearch.WordTrace]
  refine ⟨44545382300355585548753429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29696921533570390365835619 44545382300355585548753429)
  ·
    refine ⟨2088064795329168072597817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44545382300355585548753429 2088064795329168072597817)
    ·
      refine ⟨1566048596496876054448363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088064795329168072597817 1566048596496876054448363)
      ·
        refine ⟨2349072894745314081672545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566048596496876054448363 2349072894745314081672545)
        ·
          refine ⟨1761804671058985561254409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2349072894745314081672545 1761804671058985561254409)
          ·
            refine ⟨1321353503294239170940807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761804671058985561254409 1321353503294239170940807)
            ·
              refine ⟨1982030254941358756411211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321353503294239170940807 1982030254941358756411211)
              ·
                refine ⟨2973045382412038134616817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982030254941358756411211 2973045382412038134616817)
                ·
                  refine ⟨2229784036809028600962613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2973045382412038134616817 2229784036809028600962613)
                  ·
                    refine ⟨209042253450846431340245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2229784036809028600962613 209042253450846431340245)
                    ·
                      rfl

theorem cell23_1221325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1221325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221325 prefixEnd_1221325 := by exact prefixLift 1221325
  have htrace : WordTrace (prefixWord ++ tailWord_1221325) baseStart_1221325 baseEnd_1221325 := by
    simpa [prefixWord, tailWord_1221325, baseEnd_1221325] using wordTrace_append hprefix tailTrace_1221325
  have hstable : (prefixWord ++ tailWord_1221325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221325).length < 2 ^ (prefixWord ++ tailWord_1221325).sum := by decide
  have hdescent : baseEnd_1221325 < baseStart_1221325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221338 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_1221338 : Nat := 118140960795 + 1221338 * 2 ^ 59
def prefixEnd_1221338 : Nat := 4983230072969 + 3 ^ 40 * 1221338 * 2
def baseEnd_1221338 : Nat := 209044478533682581052725

theorem tailTrace_1221338 : CollatzResearch.WordTrace tailWord_1221338 prefixEnd_1221338 209044478533682581052725 := by
  unfold tailWord_1221338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136464112327122192244167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29697237632872325845984445 11136464112327122192244167)
  ·
    refine ⟨16704696168490683288366251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11136464112327122192244167 16704696168490683288366251)
    ·
      refine ⟨25057044252736024932549377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16704696168490683288366251 25057044252736024932549377)
      ·
        refine ⟨18792783189552018699412033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25057044252736024932549377 18792783189552018699412033)
        ·
          refine ⟨14094587392164014024559025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18792783189552018699412033 14094587392164014024559025)
          ·
            refine ⟨10570940544123010518419269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14094587392164014024559025 10570940544123010518419269)
            ·
              refine ⟨1982051352023064472203613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10570940544123010518419269 1982051352023064472203613)
              ·
                refine ⟨743269257008649177076355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1982051352023064472203613 743269257008649177076355)
                ·
                  refine ⟨1114903885512973765614533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743269257008649177076355 1114903885512973765614533)
                  ·
                    refine ⟨209044478533682581052725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114903885512973765614533 209044478533682581052725)
                    ·
                      rfl

theorem cell23_1221338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_1221338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221338 prefixEnd_1221338 := by exact prefixLift 1221338
  have htrace : WordTrace (prefixWord ++ tailWord_1221338) baseStart_1221338 baseEnd_1221338 := by
    simpa [prefixWord, tailWord_1221338, baseEnd_1221338] using wordTrace_append hprefix tailTrace_1221338
  have hstable : (prefixWord ++ tailWord_1221338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221338).length < 2 ^ (prefixWord ++ tailWord_1221338).sum := by decide
  have hdescent : baseEnd_1221338 < baseStart_1221338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221411 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 2, 4]
def baseStart_1221411 : Nat := 118140960795 + 1221411 * 2 ^ 59
def prefixEnd_1221411 : Nat := 4983230072969 + 3 ^ 40 * 1221411 * 2
def baseEnd_1221411 : Nat := 209056973229608652515113

theorem tailTrace_1221411 : CollatzResearch.WordTrace tailWord_1221411 prefixEnd_1221411 209056973229608652515113 := by
  unfold tailWord_1221411
  simp only [CollatzResearch.WordTrace]
  refine ⟨44548518978044022236384087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29699012652029348157589391 44548518978044022236384087)
  ·
    refine ⟨66822778467066033354576131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44548518978044022236384087 66822778467066033354576131)
    ·
      refine ⟨100234167700599050031864197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66822778467066033354576131 100234167700599050031864197)
      ·
        refine ⟨18793906443862321880974537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100234167700599050031864197 18793906443862321880974537)
        ·
          refine ⟨14095429832896741410730903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18793906443862321880974537 14095429832896741410730903)
          ·
            refine ⟨21143144749345112116096355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14095429832896741410730903 21143144749345112116096355)
            ·
              refine ⟨31714717124017668174144533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21143144749345112116096355 31714717124017668174144533)
              ·
                refine ⟨1486627365188328195663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31714717124017668174144533 1486627365188328195663025)
                ·
                  refine ⟨1114970523891246146747269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1486627365188328195663025 1114970523891246146747269)
                  ·
                    refine ⟨209056973229608652515113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114970523891246146747269 209056973229608652515113)
                    ·
                      rfl

theorem cell23_1221411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 4].length) (baseStart_1221411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221411 prefixEnd_1221411 := by exact prefixLift 1221411
  have htrace : WordTrace (prefixWord ++ tailWord_1221411) baseStart_1221411 baseEnd_1221411 := by
    simpa [prefixWord, tailWord_1221411, baseEnd_1221411] using wordTrace_append hprefix tailTrace_1221411
  have hstable : (prefixWord ++ tailWord_1221411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221411).length < 2 ^ (prefixWord ++ tailWord_1221411).sum := by decide
  have hdescent : baseEnd_1221411 < baseStart_1221411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221412 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_1221412 : Nat := 118140960795 + 1221412 * 2 ^ 59
def prefixEnd_1221412 : Nat := 4983230072969 + 3 ^ 40 * 1221412 * 2
def baseEnd_1221412 : Nat := 627171433169480453632835

theorem tailTrace_1221412 : CollatzResearch.WordTrace tailWord_1221412 prefixEnd_1221412 627171433169480453632835 := by
  unfold tailWord_1221412
  simp only [CollatzResearch.WordTrace]
  refine ⟨22274277725520199703585245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29699036967360266271446993 22274277725520199703585245)
  ·
    refine ⟨8352854147070074888844467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22274277725520199703585245 8352854147070074888844467)
    ·
      refine ⟨12529281220605112333266701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8352854147070074888844467 12529281220605112333266701)
      ·
        refine ⟨4698480457726917124975013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12529281220605112333266701 4698480457726917124975013)
        ·
          refine ⟨880965085823796960932815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4698480457726917124975013 880965085823796960932815)
          ·
            refine ⟨1321447628735695441399223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880965085823796960932815 1321447628735695441399223)
            ·
              refine ⟨1982171443103543162098835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321447628735695441399223 1982171443103543162098835)
              ·
                refine ⟨2973257164655314743148253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982171443103543162098835 2973257164655314743148253)
                ·
                  refine ⟨1114971436745743028680595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2973257164655314743148253 1114971436745743028680595)
                  ·
                    refine ⟨1672457155118614543020893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1114971436745743028680595 1672457155118614543020893)
                    ·
                      refine ⟨627171433169480453632835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1672457155118614543020893 627171433169480453632835)
                      ·
                        rfl

theorem cell23_1221412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_1221412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221412 prefixEnd_1221412 := by exact prefixLift 1221412
  have htrace : WordTrace (prefixWord ++ tailWord_1221412) baseStart_1221412 baseEnd_1221412 := by
    simpa [prefixWord, tailWord_1221412, baseEnd_1221412] using wordTrace_append hprefix tailTrace_1221412
  have hstable : (prefixWord ++ tailWord_1221412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221412).length < 2 ^ (prefixWord ++ tailWord_1221412).sum := by decide
  have hdescent : baseEnd_1221412 < baseStart_1221412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221454 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1221454 : Nat := 118140960795 + 1221454 * 2 ^ 59
def prefixEnd_1221454 : Nat := 4983230072969 + 3 ^ 40 * 1221454 * 2
def baseEnd_1221454 : Nat := 209064333118989763102547

theorem tailTrace_1221454 : CollatzResearch.WordTrace tailWord_1221454 prefixEnd_1221454 209064333118989763102547 := by
  unfold tailWord_1221454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568760914611030072524927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29700058211258827053466277 5568760914611030072524927)
  ·
    refine ⟨8353141371916545108787391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5568760914611030072524927 8353141371916545108787391)
    ·
      refine ⟨12529712057874817663181087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8353141371916545108787391 12529712057874817663181087)
      ·
        refine ⟨18794568086812226494771631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12529712057874817663181087 18794568086812226494771631)
        ·
          refine ⟨28191852130218339742157447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18794568086812226494771631 28191852130218339742157447)
          ·
            refine ⟨42287778195327509613236171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28191852130218339742157447 42287778195327509613236171)
            ·
              refine ⟨63431667292991264419854257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42287778195327509613236171 63431667292991264419854257)
              ·
                refine ⟨47573750469743448314890693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63431667292991264419854257 47573750469743448314890693)
                ·
                  refine ⟨8920078213076896559042005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47573750469743448314890693 8920078213076896559042005)
                  ·
                    refine ⟨209064333118989763102547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8920078213076896559042005 209064333118989763102547)
                    ·
                      rfl

theorem cell23_1221454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1221454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221454 prefixEnd_1221454 := by exact prefixLift 1221454
  have htrace : WordTrace (prefixWord ++ tailWord_1221454) baseStart_1221454 baseEnd_1221454 := by
    simpa [prefixWord, tailWord_1221454, baseEnd_1221454] using wordTrace_append hprefix tailTrace_1221454
  have hstable : (prefixWord ++ tailWord_1221454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221454).length < 2 ^ (prefixWord ++ tailWord_1221454).sum := by decide
  have hdescent : baseEnd_1221454 < baseStart_1221454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221464 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1221464 : Nat := 118140960795 + 1221464 * 2 ^ 59
def prefixEnd_1221464 : Nat := 4983230072969 + 3 ^ 40 * 1221464 * 2
def baseEnd_1221464 : Nat := 627198134163514250182595

theorem tailTrace_1221464 : CollatzResearch.WordTrace tailWord_1221464 prefixEnd_1221464 627198134163514250182595 := by
  unfold tailWord_1221464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22275226023426006144031723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29700301364568008192042297 22275226023426006144031723)
  ·
    refine ⟨33412839035139009216047585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22275226023426006144031723 33412839035139009216047585)
    ·
      refine ⟨25059629276354256912035689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33412839035139009216047585 25059629276354256912035689)
      ·
        refine ⟨18794721957265692684026767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25059629276354256912035689 18794721957265692684026767)
        ·
          refine ⟨28192082935898539026040151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18794721957265692684026767 28192082935898539026040151)
          ·
            refine ⟨42288124403847808539060227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28192082935898539026040151 42288124403847808539060227)
            ·
              refine ⟨63432186605771712808590341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42288124403847808539060227 63432186605771712808590341)
              ·
                refine ⟨11893534988582196151610689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63432186605771712808590341 11893534988582196151610689)
                ·
                  refine ⟨8920151241436647113708017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11893534988582196151610689 8920151241436647113708017)
                  ·
                    refine ⟨6690113431077485335281013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8920151241436647113708017 6690113431077485335281013)
                    ·
                      refine ⟨627198134163514250182595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6690113431077485335281013 627198134163514250182595)
                      ·
                        rfl

theorem cell23_1221464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1221464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221464 prefixEnd_1221464 := by exact prefixLift 1221464
  have htrace : WordTrace (prefixWord ++ tailWord_1221464) baseStart_1221464 baseEnd_1221464 := by
    simpa [prefixWord, tailWord_1221464, baseEnd_1221464] using wordTrace_append hprefix tailTrace_1221464
  have hstable : (prefixWord ++ tailWord_1221464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221464).length < 2 ^ (prefixWord ++ tailWord_1221464).sum := by decide
  have hdescent : baseEnd_1221464 < baseStart_1221464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221506 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1221506 : Nat := 118140960795 + 1221506 * 2 ^ 59
def prefixEnd_1221506 : Nat := 4983230072969 + 3 ^ 40 * 1221506 * 2
def baseEnd_1221506 : Nat := 627219700351003085857403

theorem tailTrace_1221506 : CollatzResearch.WordTrace tailWord_1221506 prefixEnd_1221506 627219700351003085857403 := by
  unfold tailWord_1221506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11137995978174963365273093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29701322608466568974061581 11137995978174963365273093)
  ·
    refine ⟨2088374245907805630988705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11137995978174963365273093 2088374245907805630988705)
    ·
      refine ⟨1566280684430854223241529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088374245907805630988705 1566280684430854223241529)
      ·
        refine ⟨1174710513323140667431147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1566280684430854223241529 1174710513323140667431147)
        ·
          refine ⟨1762065769984711001146721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174710513323140667431147 1762065769984711001146721)
          ·
            refine ⟨1321549327488533250860041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762065769984711001146721 1321549327488533250860041)
            ·
              refine ⟨991161995616399938145031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321549327488533250860041 991161995616399938145031)
              ·
                refine ⟨1486742993424599907217547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991161995616399938145031 1486742993424599907217547)
                ·
                  refine ⟨2230114490136899860826321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486742993424599907217547 2230114490136899860826321)
                  ·
                    refine ⟨1672585867602674895619741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230114490136899860826321 1672585867602674895619741)
                    ·
                      refine ⟨627219700351003085857403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1672585867602674895619741 627219700351003085857403)
                      ·
                        rfl

theorem cell23_1221506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1221506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221506 prefixEnd_1221506 := by exact prefixLift 1221506
  have htrace : WordTrace (prefixWord ++ tailWord_1221506) baseStart_1221506 baseEnd_1221506 := by
    simpa [prefixWord, tailWord_1221506, baseEnd_1221506] using wordTrace_append hprefix tailTrace_1221506
  have hstable : (prefixWord ++ tailWord_1221506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221506).length < 2 ^ (prefixWord ++ tailWord_1221506).sum := by decide
  have hdescent : baseEnd_1221506 < baseStart_1221506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221512 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_1221512 : Nat := 118140960795 + 1221512 * 2 ^ 59
def prefixEnd_1221512 : Nat := 4983230072969 + 3 ^ 40 * 1221512 * 2
def baseEnd_1221512 : Nat := 627222781234930062382375

theorem tailTrace_1221512 : CollatzResearch.WordTrace tailWord_1221512 prefixEnd_1221512 627222781234930062382375 := by
  unfold tailWord_1221512
  simp only [CollatzResearch.WordTrace]
  refine ⟨22276101375339058242905395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29701468500452077657207193 22276101375339058242905395)
  ·
    refine ⟨33414152063008587364358093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22276101375339058242905395 33414152063008587364358093)
    ·
      refine ⟨12530307023628220261634285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33414152063008587364358093 12530307023628220261634285)
      ·
        refine ⟨4698865133860582598112857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12530307023628220261634285 4698865133860582598112857)
        ·
          refine ⟨3524148850395436948584643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4698865133860582598112857 3524148850395436948584643)
          ·
            refine ⟨5286223275593155422876965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524148850395436948584643 5286223275593155422876965)
            ·
              refine ⟨991166864173716641789431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5286223275593155422876965 991166864173716641789431)
              ·
                refine ⟨1486750296260574962684147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991166864173716641789431 1486750296260574962684147)
                ·
                  refine ⟨2230125444390862444026221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486750296260574962684147 2230125444390862444026221)
                  ·
                    refine ⟨836297041646573416509833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230125444390862444026221 836297041646573416509833)
                    ·
                      refine ⟨627222781234930062382375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836297041646573416509833 627222781234930062382375)
                      ·
                        rfl

theorem cell23_1221512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_1221512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221512 prefixEnd_1221512 := by exact prefixLift 1221512
  have htrace : WordTrace (prefixWord ++ tailWord_1221512) baseStart_1221512 baseEnd_1221512 := by
    simpa [prefixWord, tailWord_1221512, baseEnd_1221512] using wordTrace_append hprefix tailTrace_1221512
  have hstable : (prefixWord ++ tailWord_1221512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221512).length < 2 ^ (prefixWord ++ tailWord_1221512).sum := by decide
  have hdescent : baseEnd_1221512 < baseStart_1221512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221525 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_1221525 : Nat := 118140960795 + 1221525 * 2 ^ 59
def prefixEnd_1221525 : Nat := 4983230072969 + 3 ^ 40 * 1221525 * 2
def baseEnd_1221525 : Nat := 627229456483438511519815

theorem tailTrace_1221525 : CollatzResearch.WordTrace tailWord_1221525 prefixEnd_1221525 627229456483438511519815 := by
  unfold tailWord_1221525
  simp only [CollatzResearch.WordTrace]
  refine ⟨44552676899631019706034029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29701784599754013137356019 44552676899631019706034029)
  ·
    refine ⟨16707253837361632389762761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44552676899631019706034029 16707253837361632389762761)
    ·
      refine ⟨12530440378021224292322071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16707253837361632389762761 12530440378021224292322071)
      ·
        refine ⟨18795660567031836438483107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12530440378021224292322071 18795660567031836438483107)
        ·
          refine ⟨28193490850547754657724661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18795660567031836438483107 28193490850547754657724661)
          ·
            refine ⟨2643139767238851999161687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28193490850547754657724661 2643139767238851999161687)
            ·
              refine ⟨3964709650858277998742531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643139767238851999161687 3964709650858277998742531)
              ·
                refine ⟨5947064476287416998113797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964709650858277998742531 5947064476287416998113797)
                ·
                  refine ⟨1115074589303890687146337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5947064476287416998113797 1115074589303890687146337)
                  ·
                    refine ⟨836305941977918015359753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115074589303890687146337 836305941977918015359753)
                    ·
                      refine ⟨627229456483438511519815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836305941977918015359753 627229456483438511519815)
                      ·
                        rfl

theorem cell23_1221525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_1221525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221525 prefixEnd_1221525 := by exact prefixLift 1221525
  have htrace : WordTrace (prefixWord ++ tailWord_1221525) baseStart_1221525 baseEnd_1221525 := by
    simpa [prefixWord, tailWord_1221525, baseEnd_1221525] using wordTrace_append hprefix tailTrace_1221525
  have hstable : (prefixWord ++ tailWord_1221525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221525).length < 2 ^ (prefixWord ++ tailWord_1221525).sum := by decide
  have hdescent : baseEnd_1221525 < baseStart_1221525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221538 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1221538 : Nat := 118140960795 + 1221538 * 2 ^ 59
def prefixEnd_1221538 : Nat := 4983230072969 + 3 ^ 40 * 1221538 * 2
def baseEnd_1221538 : Nat := 627236131731946960657255

theorem tailTrace_1221538 : CollatzResearch.WordTrace tailWord_1221538 prefixEnd_1221538 627236131731946960657255 := by
  unfold tailWord_1221538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138287762145980731564317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29702100699055948617504845 11138287762145980731564317)
  ·
    refine ⟨4176857910804742774336619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11138287762145980731564317 4176857910804742774336619)
    ·
      refine ⟨6265286866207114161504929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176857910804742774336619 6265286866207114161504929)
      ·
        refine ⟨4698965149655335621128697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6265286866207114161504929 4698965149655335621128697)
        ·
          refine ⟨3524223862241501715846523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4698965149655335621128697 3524223862241501715846523)
          ·
            refine ⟨5286335793362252573769785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524223862241501715846523 5286335793362252573769785)
            ·
              refine ⟨3964751845021689430327339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286335793362252573769785 3964751845021689430327339)
              ·
                refine ⟨5947127767532534145491009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964751845021689430327339 5947127767532534145491009)
                ·
                  refine ⟨4460345825649400609118257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947127767532534145491009 4460345825649400609118257)
                  ·
                    refine ⟨3345259369237050456838693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460345825649400609118257 3345259369237050456838693)
                    ·
                      refine ⟨627236131731946960657255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3345259369237050456838693 627236131731946960657255)
                      ·
                        rfl

theorem cell23_1221538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1221538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221538 prefixEnd_1221538 := by exact prefixLift 1221538
  have htrace : WordTrace (prefixWord ++ tailWord_1221538) baseStart_1221538 baseEnd_1221538 := by
    simpa [prefixWord, tailWord_1221538, baseEnd_1221538] using wordTrace_append hprefix tailTrace_1221538
  have hstable : (prefixWord ++ tailWord_1221538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221538).length < 2 ^ (prefixWord ++ tailWord_1221538).sum := by decide
  have hdescent : baseEnd_1221538 < baseStart_1221538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221561 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_1221561 : Nat := 118140960795 + 1221561 * 2 ^ 59
def prefixEnd_1221561 : Nat := 4983230072969 + 3 ^ 40 * 1221561 * 2
def baseEnd_1221561 : Nat := 209082647262333456889883

theorem tailTrace_1221561 : CollatzResearch.WordTrace tailWord_1221561 prefixEnd_1221561 209082647262333456889883 := by
  unfold tailWord_1221561
  simp only [CollatzResearch.WordTrace]
  refine ⟨44553989927500597854344537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29702659951667065236229691 44553989927500597854344537)
  ·
    refine ⟨33415492445625448390758403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44553989927500597854344537 33415492445625448390758403)
    ·
      refine ⟨50123238668438172586137605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33415492445625448390758403 50123238668438172586137605)
      ·
        refine ⟨9398107250332157359900801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50123238668438172586137605 9398107250332157359900801)
        ·
          refine ⟨7048580437749118019925601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9398107250332157359900801 7048580437749118019925601)
          ·
            refine ⟨5286435328311838514944201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7048580437749118019925601 5286435328311838514944201)
            ·
              refine ⟨3964826496233878886208151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286435328311838514944201 3964826496233878886208151)
              ·
                refine ⟨5947239744350818329312227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964826496233878886208151 5947239744350818329312227)
                ·
                  refine ⟨8920859616526227493968341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947239744350818329312227 8920859616526227493968341)
                  ·
                    refine ⟨209082647262333456889883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8920859616526227493968341 209082647262333456889883)
                    ·
                      rfl

theorem cell23_1221561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_1221561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221561 prefixEnd_1221561 := by exact prefixLift 1221561
  have htrace : WordTrace (prefixWord ++ tailWord_1221561) baseStart_1221561 baseEnd_1221561 := by
    simpa [prefixWord, tailWord_1221561, baseEnd_1221561] using wordTrace_append hprefix tailTrace_1221561
  have hstable : (prefixWord ++ tailWord_1221561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221561).length < 2 ^ (prefixWord ++ tailWord_1221561).sum := by decide
  have hdescent : baseEnd_1221561 < baseStart_1221561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221588 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1221588 : Nat := 118140960795 + 1221588 * 2 ^ 59
def prefixEnd_1221588 : Nat := 4983230072969 + 3 ^ 40 * 1221588 * 2
def baseEnd_1221588 : Nat := 627261805764671765032025

theorem tailTrace_1221588 : CollatzResearch.WordTrace tailWord_1221588 prefixEnd_1221588 627261805764671765032025 := by
  unfold tailWord_1221588
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277487349201390732788709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29703316465601854310384945 22277487349201390732788709)
  ·
    refine ⟨4177028877975260762397883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22277487349201390732788709 4177028877975260762397883)
    ·
      refine ⟨6265543316962891143596825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177028877975260762397883 6265543316962891143596825)
      ·
        refine ⟨4699157487722168357697619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6265543316962891143596825 4699157487722168357697619)
        ·
          refine ⟨7048736231583252536546429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699157487722168357697619 7048736231583252536546429)
          ·
            refine ⟨2643276086843719701204911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7048736231583252536546429 2643276086843719701204911)
            ·
              refine ⟨3964914130265579551807367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643276086843719701204911 3964914130265579551807367)
              ·
                refine ⟨5947371195398369327711051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964914130265579551807367 5947371195398369327711051)
                ·
                  refine ⟨8921056793097553991566577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947371195398369327711051 8921056793097553991566577)
                  ·
                    refine ⟨6690792594823165493674933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8921056793097553991566577 6690792594823165493674933)
                    ·
                      refine ⟨627261805764671765032025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6690792594823165493674933 627261805764671765032025)
                      ·
                        rfl

theorem cell23_1221588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1221588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221588 prefixEnd_1221588 := by exact prefixLift 1221588
  have htrace : WordTrace (prefixWord ++ tailWord_1221588) baseStart_1221588 baseEnd_1221588 := by
    simpa [prefixWord, tailWord_1221588, baseEnd_1221588] using wordTrace_append hprefix tailTrace_1221588
  have hstable : (prefixWord ++ tailWord_1221588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221588).length < 2 ^ (prefixWord ++ tailWord_1221588).sum := by decide
  have hdescent : baseEnd_1221588 < baseStart_1221588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221608 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1221608 : Nat := 118140960795 + 1221608 * 2 ^ 59
def prefixEnd_1221608 : Nat := 4983230072969 + 3 ^ 40 * 1221608 * 2
def baseEnd_1221608 : Nat := 209090691792587228927311

theorem tailTrace_1221608 : CollatzResearch.WordTrace tailWord_1221608 prefixEnd_1221608 209090691792587228927311 := by
  unfold tailWord_1221608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277852079165162440652739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29703802772220216587536985 22277852079165162440652739)
  ·
    refine ⟨33416778118747743660979109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22277852079165162440652739 33416778118747743660979109)
    ·
      refine ⟨6265645897265201936433583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33416778118747743660979109 6265645897265201936433583)
      ·
        refine ⟨9398468845897802904650375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6265645897265201936433583 9398468845897802904650375)
        ·
          refine ⟨14097703268846704356975563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9398468845897802904650375 14097703268846704356975563)
          ·
            refine ⟨21146554903270056535463345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14097703268846704356975563 21146554903270056535463345)
            ·
              refine ⟨15859916177452542401597509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21146554903270056535463345 15859916177452542401597509)
              ·
                refine ⟨2973734283272351700299533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15859916177452542401597509 2973734283272351700299533)
                ·
                  refine ⟨1115150356227131887612325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2973734283272351700299533 1115150356227131887612325)
                  ·
                    refine ⟨209090691792587228927311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115150356227131887612325 209090691792587228927311)
                    ·
                      rfl

theorem cell23_1221608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1221608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221608 prefixEnd_1221608 := by exact prefixLift 1221608
  have htrace : WordTrace (prefixWord ++ tailWord_1221608) baseStart_1221608 baseEnd_1221608 := by
    simpa [prefixWord, tailWord_1221608, baseEnd_1221608] using wordTrace_append hprefix tailTrace_1221608
  have hstable : (prefixWord ++ tailWord_1221608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221608).length < 2 ^ (prefixWord ++ tailWord_1221608).sum := by decide
  have hdescent : baseEnd_1221608 < baseStart_1221608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221625 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 1, 4]
def baseStart_1221625 : Nat := 118140960795 + 1221625 * 2 ^ 59
def prefixEnd_1221625 : Nat := 4983230072969 + 3 ^ 40 * 1221625 * 2
def baseEnd_1221625 : Nat := 209093601516296040089785

theorem tailTrace_1221625 : CollatzResearch.WordTrace tailWord_1221625 prefixEnd_1221625 209093601516296040089785 := by
  unfold tailWord_1221625
  simp only [CollatzResearch.WordTrace]
  refine ⟨44556324199268736784674329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29704216132845824523116219 44556324199268736784674329)
  ·
    refine ⟨33417243149451552588505747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44556324199268736784674329 33417243149451552588505747)
    ·
      refine ⟨50125864724177328882758621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33417243149451552588505747 50125864724177328882758621)
      ·
        refine ⟨18797199271566498331034483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50125864724177328882758621 18797199271566498331034483)
        ·
          refine ⟨28195798907349747496551725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18797199271566498331034483 28195798907349747496551725)
          ·
            refine ⟨10573424590256155311206897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28195798907349747496551725 10573424590256155311206897)
            ·
              refine ⟨7930068442692116483405173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10573424590256155311206897 7930068442692116483405173)
              ·
                refine ⟨743443916502385920319235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7930068442692116483405173 743443916502385920319235)
                ·
                  refine ⟨1115165874753578880478853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743443916502385920319235 1115165874753578880478853)
                  ·
                    refine ⟨209093601516296040089785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115165874753578880478853 209093601516296040089785)
                    ·
                      rfl

theorem cell23_1221625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 4].length) (baseStart_1221625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221625 prefixEnd_1221625 := by exact prefixLift 1221625
  have htrace : WordTrace (prefixWord ++ tailWord_1221625) baseStart_1221625 baseEnd_1221625 := by
    simpa [prefixWord, tailWord_1221625, baseEnd_1221625] using wordTrace_append hprefix tailTrace_1221625
  have hstable : (prefixWord ++ tailWord_1221625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221625).length < 2 ^ (prefixWord ++ tailWord_1221625).sum := by decide
  have hdescent : baseEnd_1221625 < baseStart_1221625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221642 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_1221642 : Nat := 118140960795 + 1221642 * 2 ^ 59
def prefixEnd_1221642 : Nat := 4983230072969 + 3 ^ 40 * 1221642 * 2
def baseEnd_1221642 : Nat := 209096511240004851252259

theorem tailTrace_1221642 : CollatzResearch.WordTrace tailWord_1221642 prefixEnd_1221642 209096511240004851252259 := by
  unfold tailWord_1221642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139236060051787172010795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29704629493471432458695453 11139236060051787172010795)
  ·
    refine ⟨16708854090077680758016193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11139236060051787172010795 16708854090077680758016193)
    ·
      refine ⟨12531640567558260568512145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16708854090077680758016193 12531640567558260568512145)
      ·
        refine ⟨9398730425668695426384109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12531640567558260568512145 9398730425668695426384109)
        ·
          refine ⟨3524523909625760784894041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9398730425668695426384109 3524523909625760784894041)
          ·
            refine ⟨2643392932219320588670531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3524523909625760784894041 2643392932219320588670531)
            ·
              refine ⟨3965089398328980883005797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643392932219320588670531 3965089398328980883005797)
              ·
                refine ⟨743454262186683915563587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3965089398328980883005797 743454262186683915563587)
                ·
                  refine ⟨1115181393280025873345381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743454262186683915563587 1115181393280025873345381)
                  ·
                    refine ⟨209096511240004851252259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115181393280025873345381 209096511240004851252259)
                    ·
                      rfl

theorem cell23_1221642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_1221642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221642 prefixEnd_1221642 := by exact prefixLift 1221642
  have htrace : WordTrace (prefixWord ++ tailWord_1221642) baseStart_1221642 baseEnd_1221642 := by
    simpa [prefixWord, tailWord_1221642, baseEnd_1221642] using wordTrace_append hprefix tailTrace_1221642
  have hstable : (prefixWord ++ tailWord_1221642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221642).length < 2 ^ (prefixWord ++ tailWord_1221642).sum := by decide
  have hdescent : baseEnd_1221642 < baseStart_1221642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221665 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1221665 : Nat := 118140960795 + 1221665 * 2 ^ 59
def prefixEnd_1221665 : Nat := 4983230072969 + 3 ^ 40 * 1221665 * 2
def baseEnd_1221665 : Nat := 627301343775067963769171

theorem tailTrace_1221665 : CollatzResearch.WordTrace tailWord_1221665 prefixEnd_1221665 627301343775067963769171 := by
  unfold tailWord_1221665
  simp only [CollatzResearch.WordTrace]
  refine ⟨44557783119123823616130449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29705188746082549077420299 44557783119123823616130449)
  ·
    refine ⟨33418337339342867712097837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44557783119123823616130449 33418337339342867712097837)
    ·
      refine ⟨12531876502253575392036689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33418337339342867712097837 12531876502253575392036689)
      ·
        refine ⟨9398907376690181544027517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12531876502253575392036689 9398907376690181544027517)
        ·
          refine ⟨3524590266258818079010319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9398907376690181544027517 3524590266258818079010319)
          ·
            refine ⟨5286885399388227118515479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524590266258818079010319 5286885399388227118515479)
            ·
              refine ⟨7930328099082340677773219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286885399388227118515479 7930328099082340677773219)
              ·
                refine ⟨11895492148623511016659829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7930328099082340677773219 11895492148623511016659829)
                ·
                  refine ⟨1115202388933454157811859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11895492148623511016659829 1115202388933454157811859)
                  ·
                    refine ⟨1672803583400181236717789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1115202388933454157811859 1672803583400181236717789)
                    ·
                      refine ⟨627301343775067963769171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1672803583400181236717789 627301343775067963769171)
                      ·
                        rfl

theorem cell23_1221665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1221665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221665 prefixEnd_1221665 := by exact prefixLift 1221665
  have htrace : WordTrace (prefixWord ++ tailWord_1221665) baseStart_1221665 baseEnd_1221665 := by
    simpa [prefixWord, tailWord_1221665, baseEnd_1221665] using wordTrace_append hprefix tailTrace_1221665
  have hstable : (prefixWord ++ tailWord_1221665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221665).length < 2 ^ (prefixWord ++ tailWord_1221665).sum := by decide
  have hdescent : baseEnd_1221665 < baseStart_1221665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221742 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1221742 : Nat := 118140960795 + 1221742 * 2 ^ 59
def prefixEnd_1221742 : Nat := 4983230072969 + 3 ^ 40 * 1221742 * 2
def baseEnd_1221742 : Nat := 627340881785464162506317

theorem tailTrace_1221742 : CollatzResearch.WordTrace tailWord_1221742 prefixEnd_1221742 627340881785464162506317 := by
  unfold tailWord_1221742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570073942480608220835435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29707061026563243844455653 5570073942480608220835435)
  ·
    refine ⟨8355110913720912331253153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5570073942480608220835435 8355110913720912331253153)
    ·
      refine ⟨6266333185290684248439865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8355110913720912331253153 6266333185290684248439865)
      ·
        refine ⟨4699749888968013186329899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6266333185290684248439865 4699749888968013186329899)
        ·
          refine ⟨7049624833452019779494849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699749888968013186329899 7049624833452019779494849)
          ·
            refine ⟨5287218625089014834621137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7049624833452019779494849 5287218625089014834621137)
            ·
              refine ⟨3965413968816761125965853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5287218625089014834621137 3965413968816761125965853)
              ·
                refine ⟨1487030238306285422237195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3965413968816761125965853 1487030238306285422237195)
                ·
                  refine ⟨2230545357459428133355793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487030238306285422237195 2230545357459428133355793)
                  ·
                    refine ⟨1672909018094571100016845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230545357459428133355793 1672909018094571100016845)
                    ·
                      refine ⟨627340881785464162506317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1672909018094571100016845 627340881785464162506317)
                      ·
                        rfl

theorem cell23_1221742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1221742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221742 prefixEnd_1221742 := by exact prefixLift 1221742
  have htrace : WordTrace (prefixWord ++ tailWord_1221742) baseStart_1221742 baseEnd_1221742 := by
    simpa [prefixWord, tailWord_1221742, baseEnd_1221742] using wordTrace_append hprefix tailTrace_1221742
  have hstable : (prefixWord ++ tailWord_1221742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221742).length < 2 ^ (prefixWord ++ tailWord_1221742).sum := by decide
  have hdescent : baseEnd_1221742 < baseStart_1221742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221756 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_1221756 : Nat := 118140960795 + 1221756 * 2 ^ 59
def prefixEnd_1221756 : Nat := 4983230072969 + 3 ^ 40 * 1221756 * 2
def baseEnd_1221756 : Nat := 627348070514627107731253

theorem tailTrace_1221756 : CollatzResearch.WordTrace tailWord_1221756 prefixEnd_1221756 627348070514627107731253 := by
  unfold tailWord_1221756
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280551080897073078846561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29707401441196097438462081 22280551080897073078846561)
  ·
    refine ⟨16710413310672804809134921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22280551080897073078846561 16710413310672804809134921)
    ·
      refine ⟨12532809983004603606851191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16710413310672804809134921 12532809983004603606851191)
      ·
        refine ⟨18799214974506905410276787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532809983004603606851191 18799214974506905410276787)
        ·
          refine ⟨28198822461760358115415181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799214974506905410276787 28198822461760358115415181)
          ·
            refine ⟨10574558423160134293280693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28198822461760358115415181 10574558423160134293280693)
            ·
              refine ⟨991364852171262589995065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10574558423160134293280693 991364852171262589995065)
              ·
                refine ⟨743523639128446942496299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 991364852171262589995065 743523639128446942496299)
                ·
                  refine ⟨1115285458692670413744449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743523639128446942496299 1115285458692670413744449)
                  ·
                    refine ⟨836464094019502810308337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115285458692670413744449 836464094019502810308337)
                    ·
                      refine ⟨627348070514627107731253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836464094019502810308337 627348070514627107731253)
                      ·
                        rfl

theorem cell23_1221756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_1221756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221756 prefixEnd_1221756 := by exact prefixLift 1221756
  have htrace : WordTrace (prefixWord ++ tailWord_1221756) baseStart_1221756 baseEnd_1221756 := by
    simpa [prefixWord, tailWord_1221756, baseEnd_1221756] using wordTrace_append hprefix tailTrace_1221756
  have hstable : (prefixWord ++ tailWord_1221756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221756).length < 2 ^ (prefixWord ++ tailWord_1221756).sum := by decide
  have hdescent : baseEnd_1221756 < baseStart_1221756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221808 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_1221808 : Nat := 118140960795 + 1221808 * 2 ^ 59
def prefixEnd_1221808 : Nat := 4983230072969 + 3 ^ 40 * 1221808 * 2
def baseEnd_1221808 : Nat := 627374771508660904281013

theorem tailTrace_1221808 : CollatzResearch.WordTrace tailWord_1221808 prefixEnd_1221808 627374771508660904281013 := by
  unfold tailWord_1221808
  simp only [CollatzResearch.WordTrace]
  refine ⟨22281499378802879519293039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29708665838403839359057385 22281499378802879519293039)
  ·
    refine ⟨33422249068204319278939559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22281499378802879519293039 33422249068204319278939559)
    ·
      refine ⟨50133373602306478918409339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33422249068204319278939559 50133373602306478918409339)
      ·
        refine ⟨75200060403459718377614009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50133373602306478918409339 75200060403459718377614009)
        ·
          refine ⟨56400045302594788783210507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75200060403459718377614009 56400045302594788783210507)
          ·
            refine ⟨84600067953892183174815761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56400045302594788783210507 84600067953892183174815761)
            ·
              refine ⟨63450050965419137381111821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84600067953892183174815761 63450050965419137381111821)
              ·
                refine ⟨23793769112032176517916933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63450050965419137381111821 23793769112032176517916933)
                ·
                  refine ⟨4461331708506033097109425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23793769112032176517916933 4461331708506033097109425)
                  ·
                    refine ⟨3345998781379524822832069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4461331708506033097109425 3345998781379524822832069)
                    ·
                      refine ⟨627374771508660904281013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3345998781379524822832069 627374771508660904281013)
                      ·
                        rfl

theorem cell23_1221808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_1221808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221808 prefixEnd_1221808 := by exact prefixLift 1221808
  have htrace : WordTrace (prefixWord ++ tailWord_1221808) baseStart_1221808 baseEnd_1221808 := by
    simpa [prefixWord, tailWord_1221808, baseEnd_1221808] using wordTrace_append hprefix tailTrace_1221808
  have hstable : (prefixWord ++ tailWord_1221808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221808).length < 2 ^ (prefixWord ++ tailWord_1221808).sum := by decide
  have hdescent : baseEnd_1221808 < baseStart_1221808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221818 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_1221818 : Nat := 118140960795 + 1221818 * 2 ^ 59
def prefixEnd_1221818 : Nat := 4983230072969 + 3 ^ 40 * 1221818 * 2
def baseEnd_1221818 : Nat := 69708878479467318350663

theorem tailTrace_1221818 : CollatzResearch.WordTrace tailWord_1221818 prefixEnd_1221818 69708878479467318350663 := by
  unfold tailWord_1221818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140840871892382686612527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29708908991713020497633405 11140840871892382686612527)
  ·
    refine ⟨16711261307838574029918791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11140840871892382686612527 16711261307838574029918791)
    ·
      refine ⟨25066891961757861044878187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16711261307838574029918791 25066891961757861044878187)
      ·
        refine ⟨37600337942636791567317281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25066891961757861044878187 37600337942636791567317281)
        ·
          refine ⟨28200253456977593675487961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37600337942636791567317281 28200253456977593675487961)
          ·
            refine ⟨21150190092733195256615971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28200253456977593675487961 21150190092733195256615971)
            ·
              refine ⟨31725285139099792884923957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21150190092733195256615971 31725285139099792884923957)
              ·
                refine ⟨2974245481790605582961621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31725285139099792884923957 2974245481790605582961621)
                ·
                  refine ⟨69708878479467318350663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2974245481790605582961621 69708878479467318350663)
                  ·
                    rfl

theorem cell23_1221818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_1221818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221818 prefixEnd_1221818 := by exact prefixLift 1221818
  have htrace : WordTrace (prefixWord ++ tailWord_1221818) baseStart_1221818 baseEnd_1221818 := by
    simpa [prefixWord, tailWord_1221818, baseEnd_1221818] using wordTrace_append hprefix tailTrace_1221818
  have hstable : (prefixWord ++ tailWord_1221818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221818).length < 2 ^ (prefixWord ++ tailWord_1221818).sum := by decide
  have hdescent : baseEnd_1221818 < baseStart_1221818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221863 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1221863 : Nat := 118140960795 + 1221863 * 2 ^ 59
def prefixEnd_1221863 : Nat := 4983230072969 + 3 ^ 40 * 1221863 * 2
def baseEnd_1221863 : Nat := 627403012944658189093261

theorem tailTrace_1221863 : CollatzResearch.WordTrace tailWord_1221863 prefixEnd_1221863 627403012944658189093261 := by
  unfold tailWord_1221863
  simp only [CollatzResearch.WordTrace]
  refine ⟨44565004772406503431838243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29710003181604335621225495 44565004772406503431838243)
  ·
    refine ⟨66847507158609755147757365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44565004772406503431838243 66847507158609755147757365)
    ·
      refine ⟨6266953796119664545102253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66847507158609755147757365 6266953796119664545102253)
      ·
        refine ⟨2350107673544874204413345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6266953796119664545102253 2350107673544874204413345)
        ·
          refine ⟨1762580755158655653310009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2350107673544874204413345 1762580755158655653310009)
          ·
            refine ⟨1321935566368991739982507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762580755158655653310009 1321935566368991739982507)
            ·
              refine ⟨1982903349553487609973761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321935566368991739982507 1982903349553487609973761)
              ·
                refine ⟨1487177512165115707480321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982903349553487609973761 1487177512165115707480321)
                ·
                  refine ⟨1115383134123836780610241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487177512165115707480321 1115383134123836780610241)
                  ·
                    refine ⟨836537350592877585457681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115383134123836780610241 836537350592877585457681)
                    ·
                      refine ⟨627403012944658189093261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836537350592877585457681 627403012944658189093261)
                      ·
                        rfl

theorem cell23_1221863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1221863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221863 prefixEnd_1221863 := by exact prefixLift 1221863
  have htrace : WordTrace (prefixWord ++ tailWord_1221863) baseStart_1221863 baseEnd_1221863 := by
    simpa [prefixWord, tailWord_1221863, baseEnd_1221863] using wordTrace_append hprefix tailTrace_1221863
  have hstable : (prefixWord ++ tailWord_1221863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221863).length < 2 ^ (prefixWord ++ tailWord_1221863).sum := by decide
  have hdescent : baseEnd_1221863 < baseStart_1221863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221905 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_1221905 : Nat := 118140960795 + 1221905 * 2 ^ 59
def prefixEnd_1221905 : Nat := 4983230072969 + 3 ^ 40 * 1221905 * 2
def baseEnd_1221905 : Nat := 627424579132147024768067

theorem tailTrace_1221905 : CollatzResearch.WordTrace tailWord_1221905 prefixEnd_1221905 627424579132147024768067 := by
  unfold tailWord_1221905
  simp only [CollatzResearch.WordTrace]
  refine ⟨44566536638254344604867169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29711024425502896403244779 44566536638254344604867169)
  ·
    refine ⟨33424902478690758453650377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44566536638254344604867169 33424902478690758453650377)
    ·
      refine ⟨25068676859018068840237783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33424902478690758453650377 25068676859018068840237783)
      ·
        refine ⟨37603015288527103260356675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25068676859018068840237783 37603015288527103260356675)
        ·
          refine ⟨56404522932790654890535013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37603015288527103260356675 56404522932790654890535013)
          ·
            refine ⟨10575848049898247791975315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56404522932790654890535013 10575848049898247791975315)
            ·
              refine ⟨15863772074847371687962973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10575848049898247791975315 15863772074847371687962973)
              ·
                refine ⟨5948914528067764382986115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15863772074847371687962973 5948914528067764382986115)
                ·
                  refine ⟨8923371792101646574479173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5948914528067764382986115 8923371792101646574479173)
                  ·
                    refine ⟨1673132211019058732714845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8923371792101646574479173 1673132211019058732714845)
                    ·
                      refine ⟨627424579132147024768067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1673132211019058732714845 627424579132147024768067)
                      ·
                        rfl

theorem cell23_1221905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_1221905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221905 prefixEnd_1221905 := by exact prefixLift 1221905
  have htrace : WordTrace (prefixWord ++ tailWord_1221905) baseStart_1221905 baseEnd_1221905 := by
    simpa [prefixWord, tailWord_1221905, baseEnd_1221905] using wordTrace_append hprefix tailTrace_1221905
  have hstable : (prefixWord ++ tailWord_1221905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221905).length < 2 ^ (prefixWord ++ tailWord_1221905).sum := by decide
  have hdescent : baseEnd_1221905 < baseStart_1221905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221925 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 8]
def baseStart_1221925 : Nat := 118140960795 + 1221925 * 2 ^ 59
def prefixEnd_1221925 : Nat := 4983230072969 + 3 ^ 40 * 1221925 * 2
def baseEnd_1221925 : Nat := 69714983193915216279775

theorem tailTrace_1221925 : CollatzResearch.WordTrace tailWord_1221925 prefixEnd_1221925 69714983193915216279775 := by
  unfold tailWord_1221925
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567266098181888020595229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29711510732121258680396819 44567266098181888020595229)
  ·
    refine ⟨16712724786818208007723211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44567266098181888020595229 16712724786818208007723211)
    ·
      refine ⟨25069087180227312011584817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16712724786818208007723211 25069087180227312011584817)
      ·
        refine ⟨18801815385170484008688613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25069087180227312011584817 18801815385170484008688613)
        ·
          refine ⟨3525340384719465751629115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18801815385170484008688613 3525340384719465751629115)
          ·
            refine ⟨5288010577079198627443673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525340384719465751629115 5288010577079198627443673)
            ·
              refine ⟨3966007932809398970582755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288010577079198627443673 3966007932809398970582755)
              ·
                refine ⟨5949011899214098455874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966007932809398970582755 5949011899214098455874133)
                ·
                  refine ⟨69714983193915216279775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5949011899214098455874133 69714983193915216279775)
                  ·
                    rfl

theorem cell23_1221925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_1221925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221925 prefixEnd_1221925 := by exact prefixLift 1221925
  have htrace : WordTrace (prefixWord ++ tailWord_1221925) baseStart_1221925 baseEnd_1221925 := by
    simpa [prefixWord, tailWord_1221925, baseEnd_1221925] using wordTrace_append hprefix tailTrace_1221925
  have hstable : (prefixWord ++ tailWord_1221925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221925).length < 2 ^ (prefixWord ++ tailWord_1221925).sum := by decide
  have hdescent : baseEnd_1221925 < baseStart_1221925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221952 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3]
def baseStart_1221952 : Nat := 118140960795 + 1221952 * 2 ^ 59
def prefixEnd_1221952 : Nat := 4983230072969 + 3 ^ 40 * 1221952 * 2
def baseEnd_1221952 : Nat := 627448712722908340880351

theorem tailTrace_1221952 : CollatzResearch.WordTrace tailWord_1221952 prefixEnd_1221952 627448712722908340880351 := by
  unfold tailWord_1221952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22284125434542035815914055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29712167246056047754552073 22284125434542035815914055)
  ·
    refine ⟨33426188151813053723871083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22284125434542035815914055 33426188151813053723871083)
    ·
      refine ⟨50139282227719580585806625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33426188151813053723871083 50139282227719580585806625)
      ·
        refine ⟨37604461670789685439354969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50139282227719580585806625 37604461670789685439354969)
        ·
          refine ⟨28203346253092264079516227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37604461670789685439354969 28203346253092264079516227)
          ·
            refine ⟨42305019379638396119274341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28203346253092264079516227 42305019379638396119274341)
            ·
              refine ⟨7932191133682199272363939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42305019379638396119274341 7932191133682199272363939)
              ·
                refine ⟨11898286700523298908545909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932191133682199272363939 11898286700523298908545909)
                ·
                  refine ⟨1115464378174059272676179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11898286700523298908545909 1115464378174059272676179)
                  ·
                    refine ⟨1673196567261088909014269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1115464378174059272676179 1673196567261088909014269)
                    ·
                      refine ⟨627448712722908340880351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1673196567261088909014269 627448712722908340880351)
                      ·
                        rfl

theorem cell23_1221952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_1221952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221952 prefixEnd_1221952 := by exact prefixLift 1221952
  have htrace : WordTrace (prefixWord ++ tailWord_1221952) baseStart_1221952 baseEnd_1221952 := by
    simpa [prefixWord, tailWord_1221952, baseEnd_1221952] using wordTrace_append hprefix tailTrace_1221952
  have hstable : (prefixWord ++ tailWord_1221952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221952).length < 2 ^ (prefixWord ++ tailWord_1221952).sum := by decide
  have hdescent : baseEnd_1221952 < baseStart_1221952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221956 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1221956 : Nat := 118140960795 + 1221956 * 2 ^ 59
def prefixEnd_1221956 : Nat := 4983230072969 + 3 ^ 40 * 1221956 * 2
def baseEnd_1221956 : Nat := 627450766645526325230333

theorem tailTrace_1221956 : CollatzResearch.WordTrace tailWord_1221956 prefixEnd_1221956 627450766645526325230333 := by
  unfold tailWord_1221956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22284198380534790157486861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29712264507379720209982481 22284198380534790157486861)
  ·
    refine ⟨8356574392700546309057573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22284198380534790157486861 8356574392700546309057573)
    ·
      refine ⟨1566857698631352432948295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8356574392700546309057573 1566857698631352432948295)
      ·
        refine ⟨2350286547947028649422443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566857698631352432948295 2350286547947028649422443)
        ·
          refine ⟨3525429821920542974133665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350286547947028649422443 3525429821920542974133665)
          ·
            refine ⟨2644072366440407230600249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525429821920542974133665 2644072366440407230600249)
            ·
              refine ⟨1983054274830305422950187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644072366440407230600249 1983054274830305422950187)
              ·
                refine ⟨2974581412245458134425281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983054274830305422950187 2974581412245458134425281)
                ·
                  refine ⟨2230936059184093600818961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974581412245458134425281 2230936059184093600818961)
                  ·
                    refine ⟨1673202044388070200614221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230936059184093600818961 1673202044388070200614221)
                    ·
                      refine ⟨627450766645526325230333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1673202044388070200614221 627450766645526325230333)
                      ·
                        rfl

theorem cell23_1221956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1221956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221956 prefixEnd_1221956 := by exact prefixLift 1221956
  have htrace : WordTrace (prefixWord ++ tailWord_1221956) baseStart_1221956 baseEnd_1221956 := by
    simpa [prefixWord, tailWord_1221956, baseEnd_1221956] using wordTrace_append hprefix tailTrace_1221956
  have hstable : (prefixWord ++ tailWord_1221956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221956).length < 2 ^ (prefixWord ++ tailWord_1221956).sum := by decide
  have hdescent : baseEnd_1221956 < baseStart_1221956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221962 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_1221962 : Nat := 118140960795 + 1221962 * 2 ^ 59
def prefixEnd_1221962 : Nat := 4983230072969 + 3 ^ 40 * 1221962 * 2
def baseEnd_1221962 : Nat := 627453847529453301755305

theorem tailTrace_1221962 : CollatzResearch.WordTrace tailWord_1221962 prefixEnd_1221962 627453847529453301755305 := by
  unfold tailWord_1221962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142153899761960834923035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29712410399365228893128093 11142153899761960834923035)
  ·
    refine ⟨16713230849642941252384553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11142153899761960834923035 16713230849642941252384553)
    ·
      refine ⟨12534923137232205939288415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16713230849642941252384553 12534923137232205939288415)
      ·
        refine ⟨18802384705848308908932623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12534923137232205939288415 18802384705848308908932623)
        ·
          refine ⟨28203577058772463363398935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18802384705848308908932623 28203577058772463363398935)
          ·
            refine ⟨42305365588158695045098403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28203577058772463363398935 42305365588158695045098403)
            ·
              refine ⟨63458048382238042567647605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42305365588158695045098403 63458048382238042567647605)
              ·
                refine ⟨5949192035834816490716963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63458048382238042567647605 5949192035834816490716963)
                ·
                  refine ⟨8923788053752224736075445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5949192035834816490716963 8923788053752224736075445)
                  ·
                    refine ⟨836605130039271069007073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8923788053752224736075445 836605130039271069007073)
                    ·
                      refine ⟨627453847529453301755305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836605130039271069007073 627453847529453301755305)
                      ·
                        rfl

theorem cell23_1221962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_1221962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221962 prefixEnd_1221962 := by exact prefixLift 1221962
  have htrace : WordTrace (prefixWord ++ tailWord_1221962) baseStart_1221962 baseEnd_1221962 := by
    simpa [prefixWord, tailWord_1221962, baseEnd_1221962] using wordTrace_append hprefix tailTrace_1221962
  have hstable : (prefixWord ++ tailWord_1221962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221962).length < 2 ^ (prefixWord ++ tailWord_1221962).sum := by decide
  have hdescent : baseEnd_1221962 < baseStart_1221962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221995 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3]
def baseStart_1221995 : Nat := 118140960795 + 1221995 * 2 ^ 59
def prefixEnd_1221995 : Nat := 4983230072969 + 3 ^ 40 * 1221995 * 2
def baseEnd_1221995 : Nat := 627470792391051672642653

theorem tailTrace_1221995 : CollatzResearch.WordTrace tailWord_1221995 prefixEnd_1221995 627470792391051672642653 := by
  unfold tailWord_1221995
  simp only [CollatzResearch.WordTrace]
  refine ⟨44569819207928289975643439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29713212805285526650428959 44569819207928289975643439)
  ·
    refine ⟨66854728811892434963465159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44569819207928289975643439 66854728811892434963465159)
    ·
      refine ⟨100282093217838652445197739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66854728811892434963465159 100282093217838652445197739)
      ·
        refine ⟨150423139826757978667796609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100282093217838652445197739 150423139826757978667796609)
        ·
          refine ⟨112817354870068484000847457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150423139826757978667796609 112817354870068484000847457)
          ·
            refine ⟨84613016152551363000635593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112817354870068484000847457 84613016152551363000635593)
            ·
              refine ⟨63459762114413522250476695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84613016152551363000635593 63459762114413522250476695)
              ·
                refine ⟨95189643171620283375715043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63459762114413522250476695 95189643171620283375715043)
                ·
                  refine ⟨142784464757430425063572565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95189643171620283375715043 142784464757430425063572565)
                  ·
                    refine ⟨1673255446376137793713741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 142784464757430425063572565 1673255446376137793713741)
                    ·
                      refine ⟨627470792391051672642653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1673255446376137793713741 627470792391051672642653)
                      ·
                        rfl

theorem cell23_1221995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3].length) (baseStart_1221995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1221995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1221995 prefixEnd_1221995 := by exact prefixLift 1221995
  have htrace : WordTrace (prefixWord ++ tailWord_1221995) baseStart_1221995 baseEnd_1221995 := by
    simpa [prefixWord, tailWord_1221995, baseEnd_1221995] using wordTrace_append hprefix tailTrace_1221995
  have hstable : (prefixWord ++ tailWord_1221995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221995).length < 2 ^ (prefixWord ++ tailWord_1221995).sum := by decide
  have hdescent : baseEnd_1221995 < baseStart_1221995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222002 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_1222002 : Nat := 118140960795 + 1222002 * 2 ^ 59
def prefixEnd_1222002 : Nat := 4983230072969 + 3 ^ 40 * 1222002 * 2
def baseEnd_1222002 : Nat := 209158128918544381751707

theorem tailTrace_1222002 : CollatzResearch.WordTrace tailWord_1222002 prefixEnd_1222002 209158128918544381751707 := by
  unfold tailWord_1222002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142518629725732542787065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29713383012601953447432173 11142518629725732542787065)
  ·
    refine ⟨8356888972294299407090299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11142518629725732542787065 8356888972294299407090299)
    ·
      refine ⟨12535333458441449110635449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8356888972294299407090299 12535333458441449110635449)
      ·
        refine ⟨9401500093831086832976587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12535333458441449110635449 9401500093831086832976587)
        ·
          refine ⟨14102250140746630249464881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9401500093831086832976587 14102250140746630249464881)
          ·
            refine ⟨10576687605559972687098661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14102250140746630249464881 10576687605559972687098661)
            ·
              refine ⟨1983128926042494878830999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10576687605559972687098661 1983128926042494878830999)
              ·
                refine ⟨2974693389063742318246499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983128926042494878830999 2974693389063742318246499)
                ·
                  refine ⟨4462040083595613477369749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974693389063742318246499 4462040083595613477369749)
                  ·
                    refine ⟨209158128918544381751707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4462040083595613477369749 209158128918544381751707)
                    ·
                      rfl

theorem cell23_1222002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_1222002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222002 prefixEnd_1222002 := by exact prefixLift 1222002
  have htrace : WordTrace (prefixWord ++ tailWord_1222002) baseStart_1222002 baseEnd_1222002 := by
    simpa [prefixWord, tailWord_1222002, baseEnd_1222002] using wordTrace_append hprefix tailTrace_1222002
  have hstable : (prefixWord ++ tailWord_1222002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222002).length < 2 ^ (prefixWord ++ tailWord_1222002).sum := by decide
  have hdescent : baseEnd_1222002 < baseStart_1222002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222009 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 5, 2, 2]
def baseStart_1222009 : Nat := 118140960795 + 1222009 * 2 ^ 59
def prefixEnd_1222009 : Nat := 4983230072969 + 3 ^ 40 * 1222009 * 2
def baseEnd_1222009 : Nat := 627477981120214617867589

theorem tailTrace_1222009 : CollatzResearch.WordTrace tailWord_1222009 prefixEnd_1222009 627477981120214617867589 := by
  unfold tailWord_1222009
  simp only [CollatzResearch.WordTrace]
  refine ⟨44570329829877570366653081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29713553219918380244435387 44570329829877570366653081)
  ·
    refine ⟨33427747372408177774989811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44570329829877570366653081 33427747372408177774989811)
    ·
      refine ⟨50141621058612266662484717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33427747372408177774989811 50141621058612266662484717)
      ·
        refine ⟨18803107896979599998431769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50141621058612266662484717 18803107896979599998431769)
        ·
          refine ⟨14102330922734699998823827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18803107896979599998431769 14102330922734699998823827)
          ·
            refine ⟨21153496384102049998235741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14102330922734699998823827 21153496384102049998235741)
            ·
              refine ⟨7932561144038268749338403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21153496384102049998235741 7932561144038268749338403)
              ·
                refine ⟨11898841716057403124007605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932561144038268749338403 11898841716057403124007605)
                ·
                  refine ⟨1115516410880381542875713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11898841716057403124007605 1115516410880381542875713)
                  ·
                    refine ⟨836637308160286157156785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115516410880381542875713 836637308160286157156785)
                    ·
                      refine ⟨627477981120214617867589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836637308160286157156785 627477981120214617867589)
                      ·
                        rfl

theorem cell23_1222009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_1222009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222009 prefixEnd_1222009 := by exact prefixLift 1222009
  have htrace : WordTrace (prefixWord ++ tailWord_1222009) baseStart_1222009 baseEnd_1222009 := by
    simpa [prefixWord, tailWord_1222009, baseEnd_1222009] using wordTrace_append hprefix tailTrace_1222009
  have hstable : (prefixWord ++ tailWord_1222009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222009).length < 2 ^ (prefixWord ++ tailWord_1222009).sum := by decide
  have hdescent : baseEnd_1222009 < baseStart_1222009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222012 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_1222012 : Nat := 118140960795 + 1222012 * 2 ^ 59
def prefixEnd_1222012 : Nat := 4983230072969 + 3 ^ 40 * 1222012 * 2
def baseEnd_1222012 : Nat := 627479521562178106130075

theorem tailTrace_1222012 : CollatzResearch.WordTrace tailWord_1222012 prefixEnd_1222012 627479521562178106130075 := by
  unfold tailWord_1222012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285219624433350939506145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29713626165911134586008193 22285219624433350939506145)
  ·
    refine ⟨16713914718325013204629609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22285219624433350939506145 16713914718325013204629609)
    ·
      refine ⟨12535436038743759903472207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16713914718325013204629609 12535436038743759903472207)
      ·
        refine ⟨18803154058115639855208311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12535436038743759903472207 18803154058115639855208311)
        ·
          refine ⟨28204731087173459782812467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18803154058115639855208311 28204731087173459782812467)
          ·
            refine ⟨42307096630760189674218701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28204731087173459782812467 42307096630760189674218701)
            ·
              refine ⟨15865161236535071127832013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42307096630760189674218701 15865161236535071127832013)
              ·
                refine ⟨5949435463700651672937005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15865161236535071127832013 5949435463700651672937005)
                ·
                  refine ⟨2231038298887744377351377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5949435463700651672937005 2231038298887744377351377)
                  ·
                    refine ⟨1673278724165808283013533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231038298887744377351377 1673278724165808283013533)
                    ·
                      refine ⟨627479521562178106130075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1673278724165808283013533 627479521562178106130075)
                      ·
                        rfl

theorem cell23_1222012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_1222012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222012 prefixEnd_1222012 := by exact prefixLift 1222012
  have htrace : WordTrace (prefixWord ++ tailWord_1222012) baseStart_1222012 baseEnd_1222012 := by
    simpa [prefixWord, tailWord_1222012, baseEnd_1222012] using wordTrace_append hprefix tailTrace_1222012
  have hstable : (prefixWord ++ tailWord_1222012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222012).length < 2 ^ (prefixWord ++ tailWord_1222012).sum := by decide
  have hdescent : baseEnd_1222012 < baseStart_1222012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222036 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1222036 : Nat := 118140960795 + 1222036 * 2 ^ 59
def prefixEnd_1222036 : Nat := 4983230072969 + 3 ^ 40 * 1222036 * 2
def baseEnd_1222036 : Nat := 209163948365962004076655

theorem tailTrace_1222036 : CollatzResearch.WordTrace tailWord_1222036 prefixEnd_1222036 209163948365962004076655 := by
  unfold tailWord_1222036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285657300389876988942981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29714209733853169318590641 22285657300389876988942981)
  ·
    refine ⟨4178560743823101935426809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22285657300389876988942981 4178560743823101935426809)
    ·
      refine ⟨3133920557867326451570107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4178560743823101935426809 3133920557867326451570107)
      ·
        refine ⟨4700880836800989677355161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133920557867326451570107 4700880836800989677355161)
        ·
          refine ⟨3525660627600742258016371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700880836800989677355161 3525660627600742258016371)
          ·
            refine ⟨5288490941401113387024557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525660627600742258016371 5288490941401113387024557)
            ·
              refine ⟨1983184103025417520134209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5288490941401113387024557 1983184103025417520134209)
              ·
                refine ⟨1487388077269063140100657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983184103025417520134209 1487388077269063140100657)
                ·
                  refine ⟨1115541057951797355075493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487388077269063140100657 1115541057951797355075493)
                  ·
                    refine ⟨209163948365962004076655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115541057951797355075493 209163948365962004076655)
                    ·
                      rfl

theorem cell23_1222036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1222036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222036 prefixEnd_1222036 := by exact prefixLift 1222036
  have htrace : WordTrace (prefixWord ++ tailWord_1222036) baseStart_1222036 baseEnd_1222036 := by
    simpa [prefixWord, tailWord_1222036, baseEnd_1222036] using wordTrace_append hprefix tailTrace_1222036
  have hstable : (prefixWord ++ tailWord_1222036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222036).length < 2 ^ (prefixWord ++ tailWord_1222036).sum := by decide
  have hdescent : baseEnd_1222036 < baseStart_1222036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222046 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1222046 : Nat := 118140960795 + 1222046 * 2 ^ 59
def prefixEnd_1222046 : Nat := 4983230072969 + 3 ^ 40 * 1222046 * 2
def baseEnd_1222046 : Nat := 627496979904430973104919

theorem tailTrace_1222046 : CollatzResearch.WordTrace tailWord_1222046 prefixEnd_1222046 627496979904430973104919 := by
  unfold tailWord_1222046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571459916342940710718749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29714452887162350457166661 5571459916342940710718749)
  ·
    refine ⟨2089297468628602766519531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5571459916342940710718749 2089297468628602766519531)
    ·
      refine ⟨3133946202942904149779297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2089297468628602766519531 3133946202942904149779297)
      ·
        refine ⟨2350459652207178112334473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3133946202942904149779297 2350459652207178112334473)
        ·
          refine ⟨1762844739155383584250855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2350459652207178112334473 1762844739155383584250855)
          ·
            refine ⟨2644267108733075376376283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762844739155383584250855 2644267108733075376376283)
            ·
              refine ⟨3966400663099613064564425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644267108733075376376283 3966400663099613064564425)
              ·
                refine ⟨2974800497324709798423319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966400663099613064564425 2974800497324709798423319)
                ·
                  refine ⟨4462200745987064697634979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974800497324709798423319 4462200745987064697634979)
                  ·
                    refine ⟨6693301118980597046452469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4462200745987064697634979 6693301118980597046452469)
                    ·
                      refine ⟨627496979904430973104919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6693301118980597046452469 627496979904430973104919)
                      ·
                        rfl

theorem cell23_1222046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1222046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222046 prefixEnd_1222046 := by exact prefixLift 1222046
  have htrace : WordTrace (prefixWord ++ tailWord_1222046) baseStart_1222046 baseEnd_1222046 := by
    simpa [prefixWord, tailWord_1222046, baseEnd_1222046] using wordTrace_append hprefix tailTrace_1222046
  have hstable : (prefixWord ++ tailWord_1222046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222046).length < 2 ^ (prefixWord ++ tailWord_1222046).sum := by decide
  have hdescent : baseEnd_1222046 < baseStart_1222046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222133 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1222133 : Nat := 118140960795 + 1222133 * 2 ^ 59
def prefixEnd_1222133 : Nat := 4983230072969 + 3 ^ 40 * 1222133 * 2
def baseEnd_1222133 : Nat := 627541652721372132717019

theorem tailTrace_1222133 : CollatzResearch.WordTrace tailWord_1222133 prefixEnd_1222133 627541652721372132717019 := by
  unfold tailWord_1222133
  simp only [CollatzResearch.WordTrace]
  refine ⟨44574852481428339544167053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29716568320952226362778035 44574852481428339544167053)
  ·
    refine ⟨16715569680535627329062645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44574852481428339544167053 16715569680535627329062645)
    ·
      refine ⟨1567084657550215062099623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16715569680535627329062645 1567084657550215062099623)
      ·
        refine ⟨2350626986325322593149435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567084657550215062099623 2350626986325322593149435)
        ·
          refine ⟨3525940479487983889724153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350626986325322593149435 3525940479487983889724153)
          ·
            refine ⟨2644455359615987917293115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525940479487983889724153 2644455359615987917293115)
            ·
              refine ⟨3966683039423981875939673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644455359615987917293115 3966683039423981875939673)
              ·
                refine ⟨2975012279567986406954755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966683039423981875939673 2975012279567986406954755)
                ·
                  refine ⟨4462518419351979610432133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975012279567986406954755 4462518419351979610432133)
                  ·
                    refine ⟨836722203628496176956025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462518419351979610432133 836722203628496176956025)
                    ·
                      refine ⟨627541652721372132717019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836722203628496176956025 627541652721372132717019)
                      ·
                        rfl

theorem cell23_1222133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1222133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222133 prefixEnd_1222133 := by exact prefixLift 1222133
  have htrace : WordTrace (prefixWord ++ tailWord_1222133) baseStart_1222133 baseEnd_1222133 := by
    simpa [prefixWord, tailWord_1222133, baseEnd_1222133] using wordTrace_append hprefix tailTrace_1222133
  have hstable : (prefixWord ++ tailWord_1222133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222133).length < 2 ^ (prefixWord ++ tailWord_1222133).sum := by decide
  have hdescent : baseEnd_1222133 < baseStart_1222133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222156 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 5]
def baseStart_1222156 : Nat := 118140960795 + 1222156 * 2 ^ 59
def prefixEnd_1222156 : Nat := 4983230072969 + 3 ^ 40 * 1222156 * 2
def baseEnd_1222156 : Nat := 69728162530713949192157

theorem tailTrace_1222156 : CollatzResearch.WordTrace tailWord_1222156 prefixEnd_1222156 69728162530713949192157 := by
  unfold tailWord_1222156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22287845680172507236127161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29717127573563342981502881 22287845680172507236127161)
  ·
    refine ⟨16715884260129380427095371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22287845680172507236127161 16715884260129380427095371)
    ·
      refine ⟨25073826390194070640643057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715884260129380427095371 25073826390194070640643057)
      ·
        refine ⟨18805369792645552980482293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25073826390194070640643057 18805369792645552980482293)
        ·
          refine ⟨1763003418060520591920215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18805369792645552980482293 1763003418060520591920215)
          ·
            refine ⟨2644505127090780887880323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763003418060520591920215 2644505127090780887880323)
            ·
              refine ⟨3966757690636171331820485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644505127090780887880323 3966757690636171331820485)
              ·
                refine ⟨743767066994282124716341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3966757690636171331820485 743767066994282124716341)
                ·
                  refine ⟨69728162530713949192157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 743767066994282124716341 69728162530713949192157)
                  ·
                    rfl

theorem cell23_1222156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_1222156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222156 prefixEnd_1222156 := by exact prefixLift 1222156
  have htrace : WordTrace (prefixWord ++ tailWord_1222156) baseStart_1222156 baseEnd_1222156 := by
    simpa [prefixWord, tailWord_1222156, baseEnd_1222156] using wordTrace_append hprefix tailTrace_1222156
  have hstable : (prefixWord ++ tailWord_1222156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222156).length < 2 ^ (prefixWord ++ tailWord_1222156).sum := by decide
  have hdescent : baseEnd_1222156 < baseStart_1222156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222202 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1222202 : Nat := 118140960795 + 1222202 * 2 ^ 59
def prefixEnd_1222202 : Nat := 4983230072969 + 3 ^ 40 * 1222202 * 2
def baseEnd_1222202 : Nat := 627577082886532362754201

theorem tailTrace_1222202 : CollatzResearch.WordTrace tailWord_1222202 prefixEnd_1222202 627577082886532362754201 := by
  unfold tailWord_1222202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11144342279544591082107215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29718246078785576218952573 11144342279544591082107215)
  ·
    refine ⟨16716513419316886623160823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11144342279544591082107215 16716513419316886623160823)
    ·
      refine ⟨25074770128975329934741235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16716513419316886623160823 25074770128975329934741235)
      ·
        refine ⟨37612155193462994902111853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25074770128975329934741235 37612155193462994902111853)
        ·
          refine ⟨14104558197548623088291945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37612155193462994902111853 14104558197548623088291945)
          ·
            refine ⟨10578418648161467316218959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14104558197548623088291945 10578418648161467316218959)
            ·
              refine ⟨15867627972242200974328439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10578418648161467316218959 15867627972242200974328439)
              ·
                refine ⟨23801441958363301461492659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15867627972242200974328439 23801441958363301461492659)
                ·
                  refine ⟨35702162937544952192238989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23801441958363301461492659 35702162937544952192238989)
                  ·
                    refine ⟨13388311101579357072089621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35702162937544952192238989 13388311101579357072089621)
                    ·
                      refine ⟨627577082886532362754201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13388311101579357072089621 627577082886532362754201)
                      ·
                        rfl

theorem cell23_1222202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1222202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222202 prefixEnd_1222202 := by exact prefixLift 1222202
  have htrace : WordTrace (prefixWord ++ tailWord_1222202) baseStart_1222202 baseEnd_1222202 := by
    simpa [prefixWord, tailWord_1222202, baseEnd_1222202] using wordTrace_append hprefix tailTrace_1222202
  have hstable : (prefixWord ++ tailWord_1222202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222202).length < 2 ^ (prefixWord ++ tailWord_1222202).sum := by decide
  have hdescent : baseEnd_1222202 < baseStart_1222202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222232 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1222232 : Nat := 118140960795 + 1222232 * 2 ^ 59
def prefixEnd_1222232 : Nat := 4983230072969 + 3 ^ 40 * 1222232 * 2
def baseEnd_1222232 : Nat := 627592487306167245379063

theorem tailTrace_1222232 : CollatzResearch.WordTrace tailWord_1222232 prefixEnd_1222232 627592487306167245379063 := by
  unfold tailWord_1222232
  simp only [CollatzResearch.WordTrace]
  refine ⟨22289231654034839726010475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29718975538713119634680633 22289231654034839726010475)
  ·
    refine ⟨33433847481052259589015713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22289231654034839726010475 33433847481052259589015713)
    ·
      refine ⟨25075385610789194691761785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33433847481052259589015713 25075385610789194691761785)
      ·
        refine ⟨18806539208091896018821339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25075385610789194691761785 18806539208091896018821339)
        ·
          refine ⟨28209808812137844028232009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18806539208091896018821339 28209808812137844028232009)
          ·
            refine ⟨21157356609103383021174007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28209808812137844028232009 21157356609103383021174007)
            ·
              refine ⟨31736034913655074531761011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21157356609103383021174007 31736034913655074531761011)
              ·
                refine ⟨47604052370482611797641517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31736034913655074531761011 47604052370482611797641517)
                ·
                  refine ⟨17851519638930979424115569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47604052370482611797641517 17851519638930979424115569)
                  ·
                    refine ⟨13388639729198234568086677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17851519638930979424115569 13388639729198234568086677)
                    ·
                      refine ⟨627592487306167245379063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13388639729198234568086677 627592487306167245379063)
                      ·
                        rfl

theorem cell23_1222232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1222232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222232 prefixEnd_1222232 := by exact prefixLift 1222232
  have htrace : WordTrace (prefixWord ++ tailWord_1222232) baseStart_1222232 baseEnd_1222232 := by
    simpa [prefixWord, tailWord_1222232, baseEnd_1222232] using wordTrace_append hprefix tailTrace_1222232
  have hstable : (prefixWord ++ tailWord_1222232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222232).length < 2 ^ (prefixWord ++ tailWord_1222232).sum := by decide
  have hdescent : baseEnd_1222232 < baseStart_1222232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222250 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1222250 : Nat := 118140960795 + 1222250 * 2 ^ 59
def prefixEnd_1222250 : Nat := 4983230072969 + 3 ^ 40 * 1222250 * 2
def baseEnd_1222250 : Nat := 209200576652649391651327

theorem tailTrace_1222250 : CollatzResearch.WordTrace tailWord_1222250 prefixEnd_1222250 209200576652649391651327 := by
  unfold tailWord_1222250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11144779955501117131544051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29719413214669645684117469 11144779955501117131544051)
  ·
    refine ⟨16717169933251675697316077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11144779955501117131544051 16717169933251675697316077)
    ·
      refine ⟨6268938724969378386493529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16717169933251675697316077 6268938724969378386493529)
      ·
        refine ⟨4701704043727033789870147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268938724969378386493529 4701704043727033789870147)
        ·
          refine ⟨7052556065590550684805221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701704043727033789870147 7052556065590550684805221)
          ·
            refine ⟨1322354262298228253400979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7052556065590550684805221 1322354262298228253400979)
            ·
              refine ⟨1983531393447342380101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322354262298228253400979 1983531393447342380101469)
              ·
                refine ⟨743824272542753392538051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1983531393447342380101469 743824272542753392538051)
                ·
                  refine ⟨1115736408814130088807077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743824272542753392538051 1115736408814130088807077)
                  ·
                    refine ⟨209200576652649391651327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115736408814130088807077 209200576652649391651327)
                    ·
                      rfl

theorem cell23_1222250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1222250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222250 prefixEnd_1222250 := by exact prefixLift 1222250
  have htrace : WordTrace (prefixWord ++ tailWord_1222250) baseStart_1222250 baseEnd_1222250 := by
    simpa [prefixWord, tailWord_1222250, baseEnd_1222250] using wordTrace_append hprefix tailTrace_1222250
  have hstable : (prefixWord ++ tailWord_1222250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222250).length < 2 ^ (prefixWord ++ tailWord_1222250).sum := by decide
  have hdescent : baseEnd_1222250 < baseStart_1222250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222273 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1222273 : Nat := 118140960795 + 1222273 * 2 ^ 59
def prefixEnd_1222273 : Nat := 4983230072969 + 3 ^ 40 * 1222273 * 2
def baseEnd_1222273 : Nat := 627613540013001584966375

theorem tailTrace_1222273 : CollatzResearch.WordTrace tailWord_1222273 prefixEnd_1222273 627613540013001584966375 := by
  unfold tailWord_1222273
  simp only [CollatzResearch.WordTrace]
  refine ⟨44579958700921143454263473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29719972467280762302842315 44579958700921143454263473)
  ·
    refine ⟨33434969025690857590697605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44579958700921143454263473 33434969025690857590697605)
    ·
      refine ⟨6269056692317035798255801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33434969025690857590697605 6269056692317035798255801)
      ·
        refine ⟨4701792519237776848691851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269056692317035798255801 4701792519237776848691851)
        ·
          refine ⟨7052688778856665273037777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701792519237776848691851 7052688778856665273037777)
          ·
            refine ⟨5289516584142498954778333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052688778856665273037777 5289516584142498954778333)
            ·
              refine ⟨1983568719053437108041875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5289516584142498954778333 1983568719053437108041875)
              ·
                refine ⟨2975353078580155662062813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983568719053437108041875 2975353078580155662062813)
                ·
                  refine ⟨1115757404467558373273555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2975353078580155662062813 1115757404467558373273555)
                  ·
                    refine ⟨1673636106701337559910333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1115757404467558373273555 1673636106701337559910333)
                    ·
                      refine ⟨627613540013001584966375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1673636106701337559910333 627613540013001584966375)
                      ·
                        rfl

theorem cell23_1222273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1222273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222273 prefixEnd_1222273 := by exact prefixLift 1222273
  have htrace : WordTrace (prefixWord ++ tailWord_1222273) baseStart_1222273 baseEnd_1222273 := by
    simpa [prefixWord, tailWord_1222273, baseEnd_1222273] using wordTrace_append hprefix tailTrace_1222273
  have hstable : (prefixWord ++ tailWord_1222273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222273).length < 2 ^ (prefixWord ++ tailWord_1222273).sum := by decide
  have hdescent : baseEnd_1222273 < baseStart_1222273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222280 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 6]
def baseStart_1222280 : Nat := 118140960795 + 1222280 * 2 ^ 59
def prefixEnd_1222280 : Nat := 4983230072969 + 3 ^ 40 * 1222280 * 2
def baseEnd_1222280 : Nat := 69735237153064784175427

theorem tailTrace_1222280 : CollatzResearch.WordTrace tailWord_1222280 prefixEnd_1222280 69735237153064784175427 := by
  unfold tailWord_1222280
  simp only [CollatzResearch.WordTrace]
  refine ⟨22290107005947891824884147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29720142674597189099845529 22290107005947891824884147)
  ·
    refine ⟨33435160508921837737326221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22290107005947891824884147 33435160508921837737326221)
    ·
      refine ⟨12538185190845689151497333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33435160508921837737326221 12538185190845689151497333)
      ·
        refine ⟨1175454861641783357952875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12538185190845689151497333 1175454861641783357952875)
        ·
          refine ⟨1763182292462675036929313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175454861641783357952875 1763182292462675036929313)
          ·
            refine ⟨1322386719347006277696985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763182292462675036929313 1322386719347006277696985)
            ·
              refine ⟨991790039510254708272739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322386719347006277696985 991790039510254708272739)
              ·
                refine ⟨1487685059265382062409109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991790039510254708272739 1487685059265382062409109)
                ·
                  refine ⟨69735237153064784175427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1487685059265382062409109 69735237153064784175427)
                  ·
                    rfl

theorem cell23_1222280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 6].length) (baseStart_1222280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222280 prefixEnd_1222280 := by exact prefixLift 1222280
  have htrace : WordTrace (prefixWord ++ tailWord_1222280) baseStart_1222280 baseEnd_1222280 := by
    simpa [prefixWord, tailWord_1222280, baseEnd_1222280] using wordTrace_append hprefix tailTrace_1222280
  have hstable : (prefixWord ++ tailWord_1222280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222280).length < 2 ^ (prefixWord ++ tailWord_1222280).sum := by decide
  have hdescent : baseEnd_1222280 < baseStart_1222280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222289 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_1222289 : Nat := 118140960795 + 1222289 * 2 ^ 59
def prefixEnd_1222289 : Nat := 4983230072969 + 3 ^ 40 * 1222289 * 2
def baseEnd_1222289 : Nat := 209207251901157840788767

theorem tailTrace_1222289 : CollatzResearch.WordTrace tailWord_1222289 prefixEnd_1222289 209207251901157840788767 := by
  unfold tailWord_1222289
  simp only [CollatzResearch.WordTrace]
  refine ⟨44580542268863178186845921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29720361512575452124563947 44580542268863178186845921)
  ·
    refine ⟨33435406701647383640134441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44580542268863178186845921 33435406701647383640134441)
    ·
      refine ⟨25076555026235537730100831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33435406701647383640134441 25076555026235537730100831)
      ·
        refine ⟨37614832539353306595151247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25076555026235537730100831 37614832539353306595151247)
        ·
          refine ⟨56422248809029959892726871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37614832539353306595151247 56422248809029959892726871)
          ·
            refine ⟨84633373213544939839090307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56422248809029959892726871 84633373213544939839090307)
            ·
              refine ⟨126950059820317409758635461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84633373213544939839090307 126950059820317409758635461)
              ·
                refine ⟨23803136216309514329744149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126950059820317409758635461 23803136216309514329744149)
                ·
                  refine ⟨1115772010139508484206757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23803136216309514329744149 1115772010139508484206757)
                  ·
                    refine ⟨209207251901157840788767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115772010139508484206757 209207251901157840788767)
                    ·
                      rfl

theorem cell23_1222289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_1222289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222289 prefixEnd_1222289 := by exact prefixLift 1222289
  have htrace : WordTrace (prefixWord ++ tailWord_1222289) baseStart_1222289 baseEnd_1222289 := by
    simpa [prefixWord, tailWord_1222289, baseEnd_1222289] using wordTrace_append hprefix tailTrace_1222289
  have hstable : (prefixWord ++ tailWord_1222289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222289).length < 2 ^ (prefixWord ++ tailWord_1222289).sum := by decide
  have hdescent : baseEnd_1222289 < baseStart_1222289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222296 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1222296 : Nat := 118140960795 + 1222296 * 2 ^ 59
def prefixEnd_1222296 : Nat := 4983230072969 + 3 ^ 40 * 1222296 * 2
def baseEnd_1222296 : Nat := 627625350068054994978769

theorem tailTrace_1222296 : CollatzResearch.WordTrace tailWord_1222296 prefixEnd_1222296 627625350068054994978769 := by
  unfold tailWord_1222296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22290398789918909191175371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29720531719891878921567161 22290398789918909191175371)
  ·
    refine ⟨33435598184878363786763057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22290398789918909191175371 33435598184878363786763057)
    ·
      refine ⟨25076698638658772840072293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33435598184878363786763057 25076698638658772840072293)
      ·
        refine ⟨4701880994748519907513555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25076698638658772840072293 4701880994748519907513555)
        ·
          refine ⟨7052821492122779861270333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701880994748519907513555 7052821492122779861270333)
          ·
            refine ⟨2644808059546042447976375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7052821492122779861270333 2644808059546042447976375)
            ·
              refine ⟨3967212089319063671964563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644808059546042447976375 3967212089319063671964563)
              ·
                refine ⟨5950818133978595507946845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967212089319063671964563 5950818133978595507946845)
                ·
                  refine ⟨2231556800241973315480067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5950818133978595507946845 2231556800241973315480067)
                  ·
                    refine ⟨3347335200362959973220101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2231556800241973315480067 3347335200362959973220101)
                    ·
                      refine ⟨627625350068054994978769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3347335200362959973220101 627625350068054994978769)
                      ·
                        rfl

theorem cell23_1222296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1222296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222296 prefixEnd_1222296 := by exact prefixLift 1222296
  have htrace : WordTrace (prefixWord ++ tailWord_1222296) baseStart_1222296 baseEnd_1222296 := by
    simpa [prefixWord, tailWord_1222296, baseEnd_1222296] using wordTrace_append hprefix tailTrace_1222296
  have hstable : (prefixWord ++ tailWord_1222296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222296).length < 2 ^ (prefixWord ++ tailWord_1222296).sum := by decide
  have hdescent : baseEnd_1222296 < baseStart_1222296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222300 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1222300 : Nat := 118140960795 + 1222300 * 2 ^ 59
def prefixEnd_1222300 : Nat := 4983230072969 + 3 ^ 40 * 1222300 * 2
def baseEnd_1222300 : Nat := 627627403990672979328751

theorem tailTrace_1222300 : CollatzResearch.WordTrace tailWord_1222300 prefixEnd_1222300 627627403990672979328751 := by
  unfold tailWord_1222300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22290471735911663532748177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29720628981215551376997569 22290471735911663532748177)
  ·
    refine ⟨16717853801933747649561133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22290471735911663532748177 16717853801933747649561133)
    ·
      refine ⟨6269195175725155368585425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16717853801933747649561133 6269195175725155368585425)
      ·
        refine ⟨4701896381793866526439069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269195175725155368585425 4701896381793866526439069)
        ·
          refine ⟨1763211143172699947414651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4701896381793866526439069 1763211143172699947414651)
          ·
            refine ⟨2644816714759049921121977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763211143172699947414651 2644816714759049921121977)
            ·
              refine ⟨1983612536069287440841483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644816714759049921121977 1983612536069287440841483)
              ·
                refine ⟨2975418804103931161262225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983612536069287440841483 2975418804103931161262225)
                ·
                  refine ⟨2231564103077948370946669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975418804103931161262225 2231564103077948370946669)
                  ·
                    refine ⟨836836538654230639105001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231564103077948370946669 836836538654230639105001)
                    ·
                      refine ⟨627627403990672979328751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836836538654230639105001 627627403990672979328751)
                      ·
                        rfl

theorem cell23_1222300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1222300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222300 prefixEnd_1222300 := by exact prefixLift 1222300
  have htrace : WordTrace (prefixWord ++ tailWord_1222300) baseStart_1222300 baseEnd_1222300 := by
    simpa [prefixWord, tailWord_1222300, baseEnd_1222300] using wordTrace_append hprefix tailTrace_1222300
  have hstable : (prefixWord ++ tailWord_1222300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222300).length < 2 ^ (prefixWord ++ tailWord_1222300).sum := by decide
  have hdescent : baseEnd_1222300 < baseStart_1222300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222309 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_1222309 : Nat := 118140960795 + 1222309 * 2 ^ 59
def prefixEnd_1222309 : Nat := 4983230072969 + 3 ^ 40 * 1222309 * 2
def baseEnd_1222309 : Nat := 627632025316563444116209

theorem tailTrace_1222309 : CollatzResearch.WordTrace tailWord_1222309 prefixEnd_1222309 627632025316563444116209 := by
  unfold tailWord_1222309
  simp only [CollatzResearch.WordTrace]
  refine ⟨44581271728790721602573981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29720847819193814401715987 44581271728790721602573981)
  ·
    refine ⟨16717976898296520600965243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44581271728790721602573981 16717976898296520600965243)
    ·
      refine ⟨25076965347444780901447865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16717976898296520600965243 25076965347444780901447865)
      ·
        refine ⟨18807724010583585676085899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25076965347444780901447865 18807724010583585676085899)
        ·
          refine ⟨28211586015875378514128849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18807724010583585676085899 28211586015875378514128849)
          ·
            refine ⟨21158689511906533885596637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28211586015875378514128849 21158689511906533885596637)
            ·
              refine ⟨7934508566964950207098739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21158689511906533885596637 7934508566964950207098739)
              ·
                refine ⟨11901762850447425310648109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934508566964950207098739 11901762850447425310648109)
                ·
                  refine ⟨4463161068917784491493041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11901762850447425310648109 4463161068917784491493041)
                  ·
                    refine ⟨3347370801688338368619781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4463161068917784491493041 3347370801688338368619781)
                    ·
                      refine ⟨627632025316563444116209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3347370801688338368619781 627632025316563444116209)
                      ·
                        rfl

theorem cell23_1222309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_1222309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222309 prefixEnd_1222309 := by exact prefixLift 1222309
  have htrace : WordTrace (prefixWord ++ tailWord_1222309) baseStart_1222309 baseEnd_1222309 := by
    simpa [prefixWord, tailWord_1222309, baseEnd_1222309] using wordTrace_append hprefix tailTrace_1222309
  have hstable : (prefixWord ++ tailWord_1222309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222309).length < 2 ^ (prefixWord ++ tailWord_1222309).sum := by decide
  have hdescent : baseEnd_1222309 < baseStart_1222309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222359 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1222359 : Nat := 118140960795 + 1222359 * 2 ^ 59
def prefixEnd_1222359 : Nat := 4983230072969 + 3 ^ 40 * 1222359 * 2
def baseEnd_1222359 : Nat := 627657699349288248490979

theorem tailTrace_1222359 : CollatzResearch.WordTrace tailWord_1222359 prefixEnd_1222359 627657699349288248490979 := by
  unfold tailWord_1222359
  simp only [CollatzResearch.WordTrace]
  refine ⟨44583095378609580141894131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29722063585739720094596087 44583095378609580141894131)
  ·
    refine ⟨66874643067914370212841197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44583095378609580141894131 66874643067914370212841197)
    ·
      refine ⟨25077991150467888829815449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66874643067914370212841197 25077991150467888829815449)
      ·
        refine ⟨18808493362850916622361587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25077991150467888829815449 18808493362850916622361587)
        ·
          refine ⟨28212740044276374933542381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18808493362850916622361587 28212740044276374933542381)
          ·
            refine ⟨10579777516603640600078393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28212740044276374933542381 10579777516603640600078393)
            ·
              refine ⟨7934833137452730450058795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10579777516603640600078393 7934833137452730450058795)
              ·
                refine ⟨11902249706179095675088193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934833137452730450058795 11902249706179095675088193)
                ·
                  refine ⟨8926687279634321756316145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11902249706179095675088193 8926687279634321756316145)
                  ·
                    refine ⟨6695015459725741317237109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8926687279634321756316145 6695015459725741317237109)
                    ·
                      refine ⟨627657699349288248490979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6695015459725741317237109 627657699349288248490979)
                      ·
                        rfl

theorem cell23_1222359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1222359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222359 prefixEnd_1222359 := by exact prefixLift 1222359
  have htrace : WordTrace (prefixWord ++ tailWord_1222359) baseStart_1222359 baseEnd_1222359 := by
    simpa [prefixWord, tailWord_1222359, baseEnd_1222359] using wordTrace_append hprefix tailTrace_1222359
  have hstable : (prefixWord ++ tailWord_1222359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222359).length < 2 ^ (prefixWord ++ tailWord_1222359).sum := by decide
  have hdescent : baseEnd_1222359 < baseStart_1222359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222364 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1222364 : Nat := 118140960795 + 1222364 * 2 ^ 59
def prefixEnd_1222364 : Nat := 4983230072969 + 3 ^ 40 * 1222364 * 2
def baseEnd_1222364 : Nat := 627660266752560728928457

theorem tailTrace_1222364 : CollatzResearch.WordTrace tailWord_1222364 prefixEnd_1222364 627660266752560728928457 := by
  unfold tailWord_1222364
  simp only [CollatzResearch.WordTrace]
  refine ⟨22291638871795732997913073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29722185162394310663884097 22291638871795732997913073)
  ·
    refine ⟨16718729153846799748434805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22291638871795732997913073 16718729153846799748434805)
    ·
      refine ⟨1567380858173137476415763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16718729153846799748434805 1567380858173137476415763)
      ·
        refine ⟨2351071287259706214623645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567380858173137476415763 2351071287259706214623645)
        ·
          refine ⟨881651732722389830483867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351071287259706214623645 881651732722389830483867)
          ·
            refine ⟨1322477599083584745725801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881651732722389830483867 1322477599083584745725801)
            ·
              refine ⟨991858199312688559294351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322477599083584745725801 991858199312688559294351)
              ·
                refine ⟨1487787298969032838941527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991858199312688559294351 1487787298969032838941527)
                ·
                  refine ⟨2231680948453549258412291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487787298969032838941527 2231680948453549258412291)
                  ·
                    refine ⟨3347521422680323887618437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2231680948453549258412291 3347521422680323887618437)
                    ·
                      refine ⟨627660266752560728928457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3347521422680323887618437 627660266752560728928457)
                      ·
                        rfl

theorem cell23_1222364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1222364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222364 prefixEnd_1222364 := by exact prefixLift 1222364
  have htrace : WordTrace (prefixWord ++ tailWord_1222364) baseStart_1222364 baseEnd_1222364 := by
    simpa [prefixWord, tailWord_1222364, baseEnd_1222364] using wordTrace_append hprefix tailTrace_1222364
  have hstable : (prefixWord ++ tailWord_1222364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222364).length < 2 ^ (prefixWord ++ tailWord_1222364).sum := by decide
  have hdescent : baseEnd_1222364 < baseStart_1222364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222379 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 2, 6]
def baseStart_1222379 : Nat := 118140960795 + 1222379 * 2 ^ 59
def prefixEnd_1222379 : Nat := 4983230072969 + 3 ^ 40 * 1222379 * 2
def baseEnd_1222379 : Nat := 209222656320792723413629

theorem tailTrace_1222379 : CollatzResearch.WordTrace tailWord_1222379 prefixEnd_1222379 209222656320792723413629 := by
  unfold tailWord_1222379
  simp only [CollatzResearch.WordTrace]
  refine ⟨44583824838537123557622191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29722549892358082371748127 44583824838537123557622191)
  ·
    refine ⟨66875737257805685336433287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44583824838537123557622191 66875737257805685336433287)
    ·
      refine ⟨100313605886708528004649931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66875737257805685336433287 100313605886708528004649931)
      ·
        refine ⟨150470408830062792006974897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100313605886708528004649931 150470408830062792006974897)
        ·
          refine ⟨112852806622547094005231173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150470408830062792006974897 112852806622547094005231173)
          ·
            refine ⟨21159901241727580125980845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112852806622547094005231173 21159901241727580125980845)
            ·
              refine ⟨7934962965647842547242817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21159901241727580125980845 7934962965647842547242817)
              ·
                refine ⟨5951222224235881910432113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7934962965647842547242817 5951222224235881910432113)
                ·
                  refine ⟨4463416668176911432824085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951222224235881910432113 4463416668176911432824085)
                  ·
                    refine ⟨209222656320792723413629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4463416668176911432824085 209222656320792723413629)
                    ·
                      rfl

theorem cell23_1222379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_1222379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222379 prefixEnd_1222379 := by exact prefixLift 1222379
  have htrace : WordTrace (prefixWord ++ tailWord_1222379) baseStart_1222379 baseEnd_1222379 := by
    simpa [prefixWord, tailWord_1222379, baseEnd_1222379] using wordTrace_append hprefix tailTrace_1222379
  have hstable : (prefixWord ++ tailWord_1222379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222379).length < 2 ^ (prefixWord ++ tailWord_1222379).sum := by decide
  have hdescent : baseEnd_1222379 < baseStart_1222379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222403 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 1, 4, 2]
def baseStart_1222403 : Nat := 118140960795 + 1222403 * 2 ^ 59
def prefixEnd_1222403 : Nat := 4983230072969 + 3 ^ 40 * 1222403 * 2
def baseEnd_1222403 : Nat := 627680292498086076340777

theorem tailTrace_1222403 : CollatzResearch.WordTrace tailWord_1222403 prefixEnd_1222403 627680292498086076340777 := by
  unfold tailWord_1222403
  simp only [CollatzResearch.WordTrace]
  refine ⟨44584700190450175656495863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29723133460300117104330575 44584700190450175656495863)
  ·
    refine ⟨66877050285675263484743795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44584700190450175656495863 66877050285675263484743795)
    ·
      refine ⟨100315575428512895227115693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66877050285675263484743795 100315575428512895227115693)
      ·
        refine ⟨37618340785692335710168385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100315575428512895227115693 37618340785692335710168385)
        ·
          refine ⟨28213755589269251782626289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37618340785692335710168385 28213755589269251782626289)
          ·
            refine ⟨21160316691951938836969717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28213755589269251782626289 21160316691951938836969717)
            ·
              refine ⟨1983779689870494265965911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21160316691951938836969717 1983779689870494265965911)
              ·
                refine ⟨2975669534805741398948867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983779689870494265965911 2975669534805741398948867)
                ·
                  refine ⟨4463504302208612098423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975669534805741398948867 4463504302208612098423301)
                  ·
                    refine ⟨836907056664114768454369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463504302208612098423301 836907056664114768454369)
                    ·
                      refine ⟨627680292498086076340777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836907056664114768454369 627680292498086076340777)
                      ·
                        rfl

theorem cell23_1222403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_1222403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222403 prefixEnd_1222403 := by exact prefixLift 1222403
  have htrace : WordTrace (prefixWord ++ tailWord_1222403) baseStart_1222403 baseEnd_1222403 := by
    simpa [prefixWord, tailWord_1222403, baseEnd_1222403] using wordTrace_append hprefix tailTrace_1222403
  have hstable : (prefixWord ++ tailWord_1222403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222403).length < 2 ^ (prefixWord ++ tailWord_1222403).sum := by decide
  have hdescent : baseEnd_1222403 < baseStart_1222403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222407 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1222407 : Nat := 118140960795 + 1222407 * 2 ^ 59
def prefixEnd_1222407 : Nat := 4983230072969 + 3 ^ 40 * 1222407 * 2
def baseEnd_1222407 : Nat := 627682346420704060690759

theorem tailTrace_1222407 : CollatzResearch.WordTrace tailWord_1222407 prefixEnd_1222407 627682346420704060690759 := by
  unfold tailWord_1222407
  simp only [CollatzResearch.WordTrace]
  refine ⟨44584846082435684339641475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29723230721623789559760983 44584846082435684339641475)
  ·
    refine ⟨66877269123653526509462213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44584846082435684339641475 66877269123653526509462213)
    ·
      refine ⟨12539487960685036220524165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66877269123653526509462213 12539487960685036220524165)
      ·
        refine ⟨2351153992628444291348281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12539487960685036220524165 2351153992628444291348281)
        ·
          refine ⟨1763365494471333218511211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351153992628444291348281 1763365494471333218511211)
          ·
            refine ⟨2645048241706999827766817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763365494471333218511211 2645048241706999827766817)
            ·
              refine ⟨1983786181280249870825113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645048241706999827766817 1983786181280249870825113)
              ·
                refine ⟨1487839635960187403118835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983786181280249870825113 1487839635960187403118835)
                ·
                  refine ⟨2231759453940281104678253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487839635960187403118835 2231759453940281104678253)
                  ·
                    refine ⟨836909795227605414254345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231759453940281104678253 836909795227605414254345)
                    ·
                      refine ⟨627682346420704060690759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836909795227605414254345 627682346420704060690759)
                      ·
                        rfl

theorem cell23_1222407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1222407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222407 prefixEnd_1222407 := by exact prefixLift 1222407
  have htrace : WordTrace (prefixWord ++ tailWord_1222407) baseStart_1222407 baseEnd_1222407 := by
    simpa [prefixWord, tailWord_1222407, baseEnd_1222407] using wordTrace_append hprefix tailTrace_1222407
  have hstable : (prefixWord ++ tailWord_1222407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222407).length < 2 ^ (prefixWord ++ tailWord_1222407).sum := by decide
  have hdescent : baseEnd_1222407 < baseStart_1222407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222454 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1222454 : Nat := 118140960795 + 1222454 * 2 ^ 59
def prefixEnd_1222454 : Nat := 4983230072969 + 3 ^ 40 * 1222454 * 2
def baseEnd_1222454 : Nat := 627706480011465376803043

theorem tailTrace_1222454 : CollatzResearch.WordTrace tailWord_1222454 prefixEnd_1222454 627706480011465376803043 := by
  unfold tailWord_1222454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786660019579088210412651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29724373542176940911068277 2786660019579088210412651)
  ·
    refine ⟨4179990029368632315618977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2786660019579088210412651 4179990029368632315618977)
    ·
      refine ⟨3134992522026474236714233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4179990029368632315618977 3134992522026474236714233)
      ·
        refine ⟨2351244391519855677535675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134992522026474236714233 2351244391519855677535675)
        ·
          refine ⟨3526866587279783516303513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351244391519855677535675 3526866587279783516303513)
          ·
            refine ⟨2645149940459837637227635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526866587279783516303513 2645149940459837637227635)
            ·
              refine ⟨3967724910689756455841453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645149940459837637227635 3967724910689756455841453)
              ·
                refine ⟨1487896841508658670940545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3967724910689756455841453 1487896841508658670940545)
                ·
                  refine ⟨1115922631131494003205409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487896841508658670940545 1115922631131494003205409)
                  ·
                    refine ⟨836941973348620502404057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115922631131494003205409 836941973348620502404057)
                    ·
                      refine ⟨627706480011465376803043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836941973348620502404057 627706480011465376803043)
                      ·
                        rfl

theorem cell23_1222454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1222454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222454 prefixEnd_1222454 := by exact prefixLift 1222454
  have htrace : WordTrace (prefixWord ++ tailWord_1222454) baseStart_1222454 baseEnd_1222454 := by
    simpa [prefixWord, tailWord_1222454, baseEnd_1222454] using wordTrace_append hprefix tailTrace_1222454
  have hstable : (prefixWord ++ tailWord_1222454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222454).length < 2 ^ (prefixWord ++ tailWord_1222454).sum := by decide
  have hdescent : baseEnd_1222454 < baseStart_1222454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222479 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_1222479 : Nat := 118140960795 + 1222479 * 2 ^ 59
def prefixEnd_1222479 : Nat := 4983230072969 + 3 ^ 40 * 1222479 * 2
def baseEnd_1222479 : Nat := 627719317027827778990427

theorem tailTrace_1222479 : CollatzResearch.WordTrace tailWord_1222479 prefixEnd_1222479 627719317027827778990427 := by
  unfold tailWord_1222479
  simp only [CollatzResearch.WordTrace]
  refine ⟨44587472138174840636262491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29724981425449893757508327 44587472138174840636262491)
  ·
    refine ⟨66881208207262260954393737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44587472138174840636262491 66881208207262260954393737)
    ·
      refine ⟨50160906155446695715795303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66881208207262260954393737 50160906155446695715795303)
      ·
        refine ⟨75241359233170043573692955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50160906155446695715795303 75241359233170043573692955)
        ·
          refine ⟨112862038849755065360539433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75241359233170043573692955 112862038849755065360539433)
          ·
            refine ⟨84646529137316299020404575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112862038849755065360539433 84646529137316299020404575)
            ·
              refine ⟨126969793705974448530606863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84646529137316299020404575 126969793705974448530606863)
              ·
                refine ⟨190454690558961672795910295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126969793705974448530606863 190454690558961672795910295)
                ·
                  refine ⟨285682035838442509193865443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190454690558961672795910295 285682035838442509193865443)
                  ·
                    refine ⟨428523053757663763790798165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285682035838442509193865443 428523053757663763790798165)
                    ·
                      refine ⟨627719317027827778990427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 428523053757663763790798165 627719317027827778990427)
                      ·
                        rfl

theorem cell23_1222479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_1222479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222479 prefixEnd_1222479 := by exact prefixLift 1222479
  have htrace : WordTrace (prefixWord ++ tailWord_1222479) baseStart_1222479 baseEnd_1222479 := by
    simpa [prefixWord, tailWord_1222479, baseEnd_1222479] using wordTrace_append hprefix tailTrace_1222479
  have hstable : (prefixWord ++ tailWord_1222479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222479).length < 2 ^ (prefixWord ++ tailWord_1222479).sum := by decide
  have hdescent : baseEnd_1222479 < baseStart_1222479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222503 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 3, 4]
def baseStart_1222503 : Nat := 118140960795 + 1222503 * 2 ^ 59
def prefixEnd_1222503 : Nat := 4983230072969 + 3 ^ 40 * 1222503 * 2
def baseEnd_1222503 : Nat := 209243880187845228363439

theorem tailTrace_1222503 : CollatzResearch.WordTrace tailWord_1222503 prefixEnd_1222503 209243880187845228363439 := by
  unfold tailWord_1222503
  simp only [CollatzResearch.WordTrace]
  refine ⟨44588347490087892735136163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29725564993391928490090775 44588347490087892735136163)
  ·
    refine ⟨66882521235131839102704245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44588347490087892735136163 66882521235131839102704245)
    ·
      refine ⟨6270236365793609915878523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66882521235131839102704245 6270236365793609915878523)
      ·
        refine ⟨9405354548690414873817785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6270236365793609915878523 9405354548690414873817785)
        ·
          refine ⟨7054015911517811155363339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9405354548690414873817785 7054015911517811155363339)
          ·
            refine ⟨10581023867276716733045009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7054015911517811155363339 10581023867276716733045009)
            ·
              refine ⟨7935767900457537549783757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10581023867276716733045009 7935767900457537549783757)
              ·
                refine ⟨2975912962671576581168909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7935767900457537549783757 2975912962671576581168909)
                ·
                  refine ⟨1115967361001841217938341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2975912962671576581168909 1115967361001841217938341)
                  ·
                    refine ⟨209243880187845228363439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115967361001841217938341 209243880187845228363439)
                    ·
                      rfl

theorem cell23_1222503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_1222503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222503 prefixEnd_1222503 := by exact prefixLift 1222503
  have htrace : WordTrace (prefixWord ++ tailWord_1222503) baseStart_1222503 baseEnd_1222503 := by
    simpa [prefixWord, tailWord_1222503, baseEnd_1222503] using wordTrace_append hprefix tailTrace_1222503
  have hstable : (prefixWord ++ tailWord_1222503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222503).length < 2 ^ (prefixWord ++ tailWord_1222503).sum := by decide
  have hdescent : baseEnd_1222503 < baseStart_1222503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222510 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1222510 : Nat := 118140960795 + 1222510 * 2 ^ 59
def prefixEnd_1222510 : Nat := 4983230072969 + 3 ^ 40 * 1222510 * 2
def baseEnd_1222510 : Nat := 627735234928117157702785

theorem tailTrace_1222510 : CollatzResearch.WordTrace tailWord_1222510 prefixEnd_1222510 627735234928117157702785 := by
  unfold tailWord_1222510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573575350132816616330123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29725735200708355287093989 5573575350132816616330123)
  ·
    refine ⟨8360363025199224924495185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573575350132816616330123 8360363025199224924495185)
    ·
      refine ⟨6270272268899418693371389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8360363025199224924495185 6270272268899418693371389)
      ·
        refine ⟨2351352100837282010014271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6270272268899418693371389 2351352100837282010014271)
        ·
          refine ⟨3527028151255923015021407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351352100837282010014271 3527028151255923015021407)
          ·
            refine ⟨5290542226883884522532111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527028151255923015021407 5290542226883884522532111)
            ·
              refine ⟨7935813340325826783798167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290542226883884522532111 7935813340325826783798167)
              ·
                refine ⟨11903720010488740175697251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7935813340325826783798167 11903720010488740175697251)
                ·
                  refine ⟨17855580015733110263545877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11903720010488740175697251 17855580015733110263545877)
                  ·
                    refine ⟨836980313237489543603713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17855580015733110263545877 836980313237489543603713)
                    ·
                      refine ⟨627735234928117157702785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 836980313237489543603713 627735234928117157702785)
                      ·
                        rfl

theorem cell23_1222510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1222510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222510 prefixEnd_1222510 := by exact prefixLift 1222510
  have htrace : WordTrace (prefixWord ++ tailWord_1222510) baseStart_1222510 baseEnd_1222510 := by
    simpa [prefixWord, tailWord_1222510, baseEnd_1222510] using wordTrace_append hprefix tailTrace_1222510
  have hstable : (prefixWord ++ tailWord_1222510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222510).length < 2 ^ (prefixWord ++ tailWord_1222510).sum := by decide
  have hdescent : baseEnd_1222510 < baseStart_1222510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222583 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_1222583 : Nat := 118140960795 + 1222583 * 2 ^ 59
def prefixEnd_1222583 : Nat := 4983230072969 + 3 ^ 40 * 1222583 * 2
def baseEnd_1222583 : Nat := 627772719015895372089949

theorem tailTrace_1222583 : CollatzResearch.WordTrace tailWord_1222583 prefixEnd_1222583 627772719015895372089949 := by
  unfold tailWord_1222583
  simp only [CollatzResearch.WordTrace]
  refine ⟨44591265329798066398048403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29727510219865377598698935 44591265329798066398048403)
  ·
    refine ⟨66886897994697099597072605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44591265329798066398048403 66886897994697099597072605)
    ·
      refine ⟨25082586748011412348902227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66886897994697099597072605 25082586748011412348902227)
      ·
        refine ⟨37623880122017118523353341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25082586748011412348902227 37623880122017118523353341)
        ·
          refine ⟨14108955045756419446257503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37623880122017118523353341 14108955045756419446257503)
          ·
            refine ⟨21163432568634629169386255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14108955045756419446257503 21163432568634629169386255)
            ·
              refine ⟨31745148852951943754079383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21163432568634629169386255 31745148852951943754079383)
              ·
                refine ⟨47617723279427915631119075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31745148852951943754079383 47617723279427915631119075)
                ·
                  refine ⟨71426584919141873446678613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47617723279427915631119075 71426584919141873446678613)
                  ·
                    refine ⟨837030292021193829453265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71426584919141873446678613 837030292021193829453265)
                    ·
                      refine ⟨627772719015895372089949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837030292021193829453265 627772719015895372089949)
                      ·
                        rfl

theorem cell23_1222583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_1222583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222583 prefixEnd_1222583 := by exact prefixLift 1222583
  have htrace : WordTrace (prefixWord ++ tailWord_1222583) baseStart_1222583 baseEnd_1222583 := by
    simpa [prefixWord, tailWord_1222583, baseEnd_1222583] using wordTrace_append hprefix tailTrace_1222583
  have hstable : (prefixWord ++ tailWord_1222583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222583).length < 2 ^ (prefixWord ++ tailWord_1222583).sum := by decide
  have hdescent : baseEnd_1222583 < baseStart_1222583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222600 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_1222600 : Nat := 118140960795 + 1222600 * 2 ^ 59
def prefixEnd_1222600 : Nat := 4983230072969 + 3 ^ 40 * 1222600 * 2
def baseEnd_1222600 : Nat := 627781448187021805577371

theorem tailTrace_1222600 : CollatzResearch.WordTrace tailWord_1222600 prefixEnd_1222600 627781448187021805577371 := by
  unfold tailWord_1222600
  simp only [CollatzResearch.WordTrace]
  refine ⟨22295942685368239150708627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29727923580490985534278169 22295942685368239150708627)
  ·
    refine ⟨33443914028052358726062941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22295942685368239150708627 33443914028052358726062941)
    ·
      refine ⟨12541467760519634522273603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33443914028052358726062941 12541467760519634522273603)
      ·
        refine ⟨18812201640779451783410405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12541467760519634522273603 18812201640779451783410405)
        ·
          refine ⟨3527287807646147209389451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18812201640779451783410405 3527287807646147209389451)
          ·
            refine ⟨5290931711469220814084177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527287807646147209389451 5290931711469220814084177)
            ·
              refine ⟨3968198783601915610563133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290931711469220814084177 3968198783601915610563133)
              ·
                refine ⟨1488074543850718353961175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3968198783601915610563133 1488074543850718353961175)
                ·
                  refine ⟨2232111815776077530941763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488074543850718353961175 2232111815776077530941763)
                  ·
                    refine ⟨3348167723664116296412645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232111815776077530941763 3348167723664116296412645)
                    ·
                      refine ⟨627781448187021805577371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3348167723664116296412645 627781448187021805577371)
                      ·
                        rfl

theorem cell23_1222600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_1222600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222600 prefixEnd_1222600 := by exact prefixLift 1222600
  have htrace : WordTrace (prefixWord ++ tailWord_1222600) baseStart_1222600 baseEnd_1222600 := by
    simpa [prefixWord, tailWord_1222600, baseEnd_1222600] using wordTrace_append hprefix tailTrace_1222600
  have hstable : (prefixWord ++ tailWord_1222600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222600).length < 2 ^ (prefixWord ++ tailWord_1222600).sum := by decide
  have hdescent : baseEnd_1222600 < baseStart_1222600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222603 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5]
def baseStart_1222603 : Nat := 118140960795 + 1222603 * 2 ^ 59
def prefixEnd_1222603 : Nat := 4983230072969 + 3 ^ 40 * 1222603 * 2
def baseEnd_1222603 : Nat := 627782988628985293839857

theorem tailTrace_1222603 : CollatzResearch.WordTrace tailWord_1222603 prefixEnd_1222603 627782988628985293839857 := by
  unfold tailWord_1222603
  simp only [CollatzResearch.WordTrace]
  refine ⟨44591994789725609813776463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29727996526483739875850975 44591994789725609813776463)
  ·
    refine ⟨66887992184588414720664695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44591994789725609813776463 66887992184588414720664695)
    ·
      refine ⟨100331988276882622080997043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66887992184588414720664695 100331988276882622080997043)
      ·
        refine ⟨150497982415323933121495565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100331988276882622080997043 150497982415323933121495565)
        ·
          refine ⟨56436743405746474920560837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150497982415323933121495565 56436743405746474920560837)
          ·
            refine ⟨10581889388577464047605157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56436743405746474920560837 10581889388577464047605157)
            ·
              refine ⟨1984104260358274508925967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10581889388577464047605157 1984104260358274508925967)
              ·
                refine ⟨2976156390537411763388951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984104260358274508925967 2976156390537411763388951)
                ·
                  refine ⟨4464234585806117645083427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976156390537411763388951 4464234585806117645083427)
                  ·
                    refine ⟨6696351878709176467625141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464234585806117645083427 6696351878709176467625141)
                    ·
                      refine ⟨627782988628985293839857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6696351878709176467625141 627782988628985293839857)
                      ·
                        rfl

theorem cell23_1222603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5].length) (baseStart_1222603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222603 prefixEnd_1222603 := by exact prefixLift 1222603
  have htrace : WordTrace (prefixWord ++ tailWord_1222603) baseStart_1222603 baseEnd_1222603 := by
    simpa [prefixWord, tailWord_1222603, baseEnd_1222603] using wordTrace_append hprefix tailTrace_1222603
  have hstable : (prefixWord ++ tailWord_1222603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222603).length < 2 ^ (prefixWord ++ tailWord_1222603).sum := by decide
  have hdescent : baseEnd_1222603 < baseStart_1222603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222613 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1222613 : Nat := 118140960795 + 1222613 * 2 ^ 59
def prefixEnd_1222613 : Nat := 4983230072969 + 3 ^ 40 * 1222613 * 2
def baseEnd_1222613 : Nat := 627788123435530254714811

theorem tailTrace_1222613 : CollatzResearch.WordTrace tailWord_1222613 prefixEnd_1222613 627788123435530254714811 := by
  unfold tailWord_1222613
  simp only [CollatzResearch.WordTrace]
  refine ⟨44592359519689381521640493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29728239679792921014426995 44592359519689381521640493)
  ·
    refine ⟨16722134819883518070615185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44592359519689381521640493 16722134819883518070615185)
    ·
      refine ⟨12541601114912638552961389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16722134819883518070615185 12541601114912638552961389)
      ·
        refine ⟨4703100418092239457360521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12541601114912638552961389 4703100418092239457360521)
        ·
          refine ⟨3527325313569179593020391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703100418092239457360521 3527325313569179593020391)
          ·
            refine ⟨5290987970353769389530587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527325313569179593020391 5290987970353769389530587)
            ·
              refine ⟨7936481955530654084295881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290987970353769389530587 7936481955530654084295881)
              ·
                refine ⟨5952361466647990563221911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7936481955530654084295881 5952361466647990563221911)
                ·
                  refine ⟨8928542199971985844832867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952361466647990563221911 8928542199971985844832867)
                  ·
                    refine ⟨13392813299957978767249301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8928542199971985844832867 13392813299957978767249301)
                    ·
                      refine ⟨627788123435530254714811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13392813299957978767249301 627788123435530254714811)
                      ·
                        rfl

theorem cell23_1222613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1222613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222613 prefixEnd_1222613 := by exact prefixLift 1222613
  have htrace : WordTrace (prefixWord ++ tailWord_1222613) baseStart_1222613 baseEnd_1222613 := by
    simpa [prefixWord, tailWord_1222613, baseEnd_1222613] using wordTrace_append hprefix tailTrace_1222613
  have hstable : (prefixWord ++ tailWord_1222613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222613).length < 2 ^ (prefixWord ++ tailWord_1222613).sum := by decide
  have hdescent : baseEnd_1222613 < baseStart_1222613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222623 : List Nat := [1, 1, 2, 3, 4, 2, 2, 8]
def baseStart_1222623 : Nat := 118140960795 + 1222623 * 2 ^ 59
def prefixEnd_1222623 : Nat := 4983230072969 + 3 ^ 40 * 1222623 * 2
def baseEnd_1222623 : Nat := 23251602157113896873695

theorem tailTrace_1222623 : CollatzResearch.WordTrace tailWord_1222623 prefixEnd_1222623 23251602157113896873695 := by
  unfold tailWord_1222623
  simp only [CollatzResearch.WordTrace]
  refine ⟨44592724249653153229504523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29728482833102102153003015 44592724249653153229504523)
  ·
    refine ⟨66889086374479729844256785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44592724249653153229504523 66889086374479729844256785)
    ·
      refine ⟨50166814780859797383192589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66889086374479729844256785 50166814780859797383192589)
      ·
        refine ⟨18812555542822424018697221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50166814780859797383192589 18812555542822424018697221)
        ·
          refine ⟨3527354164279204503505729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18812555542822424018697221 3527354164279204503505729)
          ·
            refine ⟨2645515623209403377629297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3527354164279204503505729 2645515623209403377629297)
            ·
              refine ⟨1984136717407052533221973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645515623209403377629297 1984136717407052533221973)
              ·
                refine ⟨23251602157113896873695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1984136717407052533221973 23251602157113896873695)
                ·
                  rfl

theorem cell23_1222623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 8].length) (baseStart_1222623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222623 prefixEnd_1222623 := by exact prefixLift 1222623
  have htrace : WordTrace (prefixWord ++ tailWord_1222623) baseStart_1222623 baseEnd_1222623 := by
    simpa [prefixWord, tailWord_1222623, baseEnd_1222623] using wordTrace_append hprefix tailTrace_1222623
  have hstable : (prefixWord ++ tailWord_1222623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222623).length < 2 ^ (prefixWord ++ tailWord_1222623).sum := by decide
  have hdescent : baseEnd_1222623 < baseStart_1222623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222627 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 2, 4]
def baseStart_1222627 : Nat := 118140960795 + 1222627 * 2 ^ 59
def prefixEnd_1222627 : Nat := 4983230072969 + 3 ^ 40 * 1222627 * 2
def baseEnd_1222627 : Nat := 209265104054897733313249

theorem tailTrace_1222627 : CollatzResearch.WordTrace tailWord_1222627 prefixEnd_1222627 209265104054897733313249 := by
  unfold tailWord_1222627
  simp only [CollatzResearch.WordTrace]
  refine ⟨44592870141638661912650135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29728580094425774608433423 44592870141638661912650135)
  ·
    refine ⟨66889305212457992868975203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44592870141638661912650135 66889305212457992868975203)
    ·
      refine ⟨100333957818686989303462805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66889305212457992868975203 100333957818686989303462805)
      ·
        refine ⟨4703154272750952623599819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100333957818686989303462805 4703154272750952623599819)
        ·
          refine ⟨7054731409126428935399729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703154272750952623599819 7054731409126428935399729)
          ·
            refine ⟨5291048556844821701549797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7054731409126428935399729 5291048556844821701549797)
            ·
              refine ⟨992071604408404069040587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5291048556844821701549797 992071604408404069040587)
              ·
                refine ⟨1488107406612606103560881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992071604408404069040587 1488107406612606103560881)
                ·
                  refine ⟨1116080554959454577670661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488107406612606103560881 1116080554959454577670661)
                  ·
                    refine ⟨209265104054897733313249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116080554959454577670661 209265104054897733313249)
                    ·
                      rfl

theorem cell23_1222627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 4].length) (baseStart_1222627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222627 prefixEnd_1222627 := by exact prefixLift 1222627
  have htrace : WordTrace (prefixWord ++ tailWord_1222627) baseStart_1222627 baseEnd_1222627 := by
    simpa [prefixWord, tailWord_1222627, baseEnd_1222627] using wordTrace_append hprefix tailTrace_1222627
  have hstable : (prefixWord ++ tailWord_1222627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222627).length < 2 ^ (prefixWord ++ tailWord_1222627).sum := by decide
  have hdescent : baseEnd_1222627 < baseStart_1222627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222667 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 3]
def baseStart_1222667 : Nat := 118140960795 + 1222667 * 2 ^ 59
def prefixEnd_1222667 : Nat := 4983230072969 + 3 ^ 40 * 1222667 * 2
def baseEnd_1222667 : Nat := 627815851390873043439563

theorem tailTrace_1222667 : CollatzResearch.WordTrace tailWord_1222667 prefixEnd_1222667 627815851390873043439563 := by
  unfold tailWord_1222667
  simp only [CollatzResearch.WordTrace]
  refine ⟨44594329061493748744106255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29729552707662499162737503 44594329061493748744106255)
  ·
    refine ⟨66891493592240623116159383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44594329061493748744106255 66891493592240623116159383)
    ·
      refine ⟨100337240388360934674239075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66891493592240623116159383 100337240388360934674239075)
      ·
        refine ⟨150505860582541402011358613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100337240388360934674239075 150505860582541402011358613)
        ·
          refine ⟨7054962214806628219282435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150505860582541402011358613 7054962214806628219282435)
          ·
            refine ⟨10582443322209942328923653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7054962214806628219282435 10582443322209942328923653)
            ·
              refine ⟨1984208122914364186673185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10582443322209942328923653 1984208122914364186673185)
              ·
                refine ⟨1488156092185773140004889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984208122914364186673185 1488156092185773140004889)
                ·
                  refine ⟨1116117069139329855003667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488156092185773140004889 1116117069139329855003667)
                  ·
                    refine ⟨1674175603708994782505501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1116117069139329855003667 1674175603708994782505501)
                    ·
                      refine ⟨627815851390873043439563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674175603708994782505501 627815851390873043439563)
                      ·
                        rfl

theorem cell23_1222667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 3].length) (baseStart_1222667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222667 prefixEnd_1222667 := by exact prefixLift 1222667
  have htrace : WordTrace (prefixWord ++ tailWord_1222667) baseStart_1222667 baseEnd_1222667 := by
    simpa [prefixWord, tailWord_1222667, baseEnd_1222667] using wordTrace_append hprefix tailTrace_1222667
  have hstable : (prefixWord ++ tailWord_1222667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222667).length < 2 ^ (prefixWord ++ tailWord_1222667).sum := by decide
  have hdescent : baseEnd_1222667 < baseStart_1222667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222710 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1222710 : Nat := 118140960795 + 1222710 * 2 ^ 59
def prefixEnd_1222710 : Nat := 4983230072969 + 3 ^ 40 * 1222710 * 2
def baseEnd_1222710 : Nat := 627837931059016375201865

theorem tailTrace_1222710 : CollatzResearch.WordTrace tailWord_1222710 prefixEnd_1222710 627837931059016375201865 := by
  unfold tailWord_1222710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787243587521122942995099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29730598266891978058614389 2787243587521122942995099)
  ·
    refine ⟨4180865381281684414492649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2787243587521122942995099 4180865381281684414492649)
    ·
      refine ⟨3135649035961263310869487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4180865381281684414492649 3135649035961263310869487)
      ·
        refine ⟨4703473553941894966304231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135649035961263310869487 4703473553941894966304231)
        ·
          refine ⟨7055210330912842449456347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703473553941894966304231 7055210330912842449456347)
          ·
            refine ⟨10582815496369263674184521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055210330912842449456347 10582815496369263674184521)
            ·
              refine ⟨7937111622276947755638391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10582815496369263674184521 7937111622276947755638391)
              ·
                refine ⟨11905667433415421633457587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7937111622276947755638391 11905667433415421633457587)
                ·
                  refine ⟨17858501150123132450186381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11905667433415421633457587 17858501150123132450186381)
                  ·
                    refine ⟨6696937931296174668819893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17858501150123132450186381 6696937931296174668819893)
                    ·
                      refine ⟨627837931059016375201865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6696937931296174668819893 627837931059016375201865)
                      ·
                        rfl

theorem cell23_1222710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1222710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222710 prefixEnd_1222710 := by exact prefixLift 1222710
  have htrace : WordTrace (prefixWord ++ tailWord_1222710) baseStart_1222710 baseEnd_1222710 := by
    simpa [prefixWord, tailWord_1222710, baseEnd_1222710] using wordTrace_append hprefix tailTrace_1222710
  have hstable : (prefixWord ++ tailWord_1222710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222710).length < 2 ^ (prefixWord ++ tailWord_1222710).sum := by decide
  have hdescent : baseEnd_1222710 < baseStart_1222710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222718 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1222718 : Nat := 118140960795 + 1222718 * 2 ^ 59
def prefixEnd_1222718 : Nat := 4983230072969 + 3 ^ 40 * 1222718 * 2
def baseEnd_1222718 : Nat := 627842038904252343901829

theorem tailTrace_1222718 : CollatzResearch.WordTrace tailWord_1222718 prefixEnd_1222718 627842038904252343901829 := by
  unfold tailWord_1222718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574523648038623056776601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29730792789539322969475205 5574523648038623056776601)
  ·
    refine ⟨4180892736028967292582451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5574523648038623056776601 4180892736028967292582451)
    ·
      refine ⟨6271339104043450938873677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4180892736028967292582451 6271339104043450938873677)
      ·
        refine ⟨2351752164016294102077629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6271339104043450938873677 2351752164016294102077629)
        ·
          refine ⟨881907061506110288279111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351752164016294102077629 881907061506110288279111)
          ·
            refine ⟨1322860592259165432418667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881907061506110288279111 1322860592259165432418667)
            ·
              refine ⟨1984290888388748148628001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322860592259165432418667 1984290888388748148628001)
              ·
                refine ⟨1488218166291561111471001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984290888388748148628001 1488218166291561111471001)
                ·
                  refine ⟨1116163624718670833603251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488218166291561111471001 1116163624718670833603251)
                  ·
                    refine ⟨1674245437078006250404877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1116163624718670833603251 1674245437078006250404877)
                    ·
                      refine ⟨627842038904252343901829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674245437078006250404877 627842038904252343901829)
                      ·
                        rfl

theorem cell23_1222718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1222718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222718 prefixEnd_1222718 := by exact prefixLift 1222718
  have htrace : WordTrace (prefixWord ++ tailWord_1222718) baseStart_1222718 baseEnd_1222718 := by
    simpa [prefixWord, tailWord_1222718, baseEnd_1222718] using wordTrace_append hprefix tailTrace_1222718
  have hstable : (prefixWord ++ tailWord_1222718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222718).length < 2 ^ (prefixWord ++ tailWord_1222718).sum := by decide
  have hdescent : baseEnd_1222718 < baseStart_1222718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222741 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1222741 : Nat := 118140960795 + 1222741 * 2 ^ 59
def prefixEnd_1222741 : Nat := 4983230072969 + 3 ^ 40 * 1222741 * 2
def baseEnd_1222741 : Nat := 627853848959305753914223

theorem tailTrace_1222741 : CollatzResearch.WordTrace tailWord_1222741 prefixEnd_1222741 627853848959305753914223 := by
  unfold tailWord_1222741
  simp only [CollatzResearch.WordTrace]
  refine ⟨44597028063225659382300077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29731352042150439588200051 44597028063225659382300077)
  ·
    refine ⟨16723885523709622268362529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44597028063225659382300077 16723885523709622268362529)
    ·
      refine ⟨12542914142782216701271897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16723885523709622268362529 12542914142782216701271897)
      ·
        refine ⟨9407185607086662525953923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12542914142782216701271897 9407185607086662525953923)
        ·
          refine ⟨14110778410629993788930885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407185607086662525953923 14110778410629993788930885)
          ·
            refine ⟨2645770951993123835424541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14110778410629993788930885 2645770951993123835424541)
            ·
              refine ⟨992164106997421438284203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2645770951993123835424541 992164106997421438284203)
              ·
                refine ⟨1488246160496132157426305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992164106997421438284203 1488246160496132157426305)
                ·
                  refine ⟨1116184620372099118069729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488246160496132157426305 1116184620372099118069729)
                  ·
                    refine ⟨837138465279074338552297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1116184620372099118069729 837138465279074338552297)
                    ·
                      refine ⟨627853848959305753914223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837138465279074338552297 627853848959305753914223)
                      ·
                        rfl

theorem cell23_1222741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1222741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222741 prefixEnd_1222741 := by exact prefixLift 1222741
  have htrace : WordTrace (prefixWord ++ tailWord_1222741) baseStart_1222741 baseEnd_1222741 := by
    simpa [prefixWord, tailWord_1222741, baseEnd_1222741] using wordTrace_append hprefix tailTrace_1222741
  have hstable : (prefixWord ++ tailWord_1222741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222741).length < 2 ^ (prefixWord ++ tailWord_1222741).sum := by decide
  have hdescent : baseEnd_1222741 < baseStart_1222741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222743 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 7]
def baseStart_1222743 : Nat := 118140960795 + 1222743 * 2 ^ 59
def prefixEnd_1222743 : Nat := 4983230072969 + 3 ^ 40 * 1222743 * 2
def baseEnd_1222743 : Nat := 209284958640204915363071

theorem tailTrace_1222743 : CollatzResearch.WordTrace tailWord_1222743 prefixEnd_1222743 209284958640204915363071 := by
  unfold tailWord_1222743
  simp only [CollatzResearch.WordTrace]
  refine ⟨44597101009218413723872883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29731400672812275815915255 44597101009218413723872883)
  ·
    refine ⟨66895651513827620585809325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44597101009218413723872883 66895651513827620585809325)
    ·
      refine ⟨25085869317685357719678497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66895651513827620585809325 25085869317685357719678497)
      ·
        refine ⟨18814401988264018289758873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25085869317685357719678497 18814401988264018289758873)
        ·
          refine ⟨14110801491198013717319155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18814401988264018289758873 14110801491198013717319155)
          ·
            refine ⟨21166202236797020575978733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14110801491198013717319155 21166202236797020575978733)
            ·
              refine ⟨7937325838798882715992025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21166202236797020575978733 7937325838798882715992025)
              ·
                refine ⟨5952994379099162036994019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7937325838798882715992025 5952994379099162036994019)
                ·
                  refine ⟨8929491568648743055491029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952994379099162036994019 8929491568648743055491029)
                  ·
                    refine ⟨209284958640204915363071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8929491568648743055491029 209284958640204915363071)
                    ·
                      rfl

theorem cell23_1222743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_1222743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222743 prefixEnd_1222743 := by exact prefixLift 1222743
  have htrace : WordTrace (prefixWord ++ tailWord_1222743) baseStart_1222743 baseEnd_1222743 := by
    simpa [prefixWord, tailWord_1222743, baseEnd_1222743] using wordTrace_append hprefix tailTrace_1222743
  have hstable : (prefixWord ++ tailWord_1222743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222743).length < 2 ^ (prefixWord ++ tailWord_1222743).sum := by decide
  have hdescent : baseEnd_1222743 < baseStart_1222743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222753 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1222753 : Nat := 118140960795 + 1222753 * 2 ^ 59
def prefixEnd_1222753 : Nat := 4983230072969 + 3 ^ 40 * 1222753 * 2
def baseEnd_1222753 : Nat := 627860010727159706964167

theorem tailTrace_1222753 : CollatzResearch.WordTrace tailWord_1222753 prefixEnd_1222753 627860010727159706964167 := by
  unfold tailWord_1222753
  simp only [CollatzResearch.WordTrace]
  refine ⟨44597465739182185431736913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29731643826121456954491275 44597465739182185431736913)
  ·
    refine ⟨33448099304386639073802685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44597465739182185431736913 33448099304386639073802685)
    ·
      refine ⟨12543037239144989652676007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33448099304386639073802685 12543037239144989652676007)
      ·
        refine ⟨18814555858717484479014011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12543037239144989652676007 18814555858717484479014011)
        ·
          refine ⟨28221833788076226718521017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18814555858717484479014011 28221833788076226718521017)
          ·
            refine ⟨21166375341057170038890763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28221833788076226718521017 21166375341057170038890763)
            ·
              refine ⟨31749563011585755058336145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21166375341057170038890763 31749563011585755058336145)
              ·
                refine ⟨23812172258689316293752109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31749563011585755058336145 23812172258689316293752109)
                ·
                  refine ⟨8929564597008493610157041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23812172258689316293752109 8929564597008493610157041)
                  ·
                    refine ⟨6697173447756370207617781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8929564597008493610157041 6697173447756370207617781)
                    ·
                      refine ⟨627860010727159706964167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6697173447756370207617781 627860010727159706964167)
                      ·
                        rfl

theorem cell23_1222753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1222753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222753 prefixEnd_1222753 := by exact prefixLift 1222753
  have htrace : WordTrace (prefixWord ++ tailWord_1222753) baseStart_1222753 baseEnd_1222753 := by
    simpa [prefixWord, tailWord_1222753, baseEnd_1222753] using wordTrace_append hprefix tailTrace_1222753
  have hstable : (prefixWord ++ tailWord_1222753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222753).length < 2 ^ (prefixWord ++ tailWord_1222753).sum := by decide
  have hdescent : baseEnd_1222753 < baseStart_1222753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222780 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_1222780 : Nat := 118140960795 + 1222780 * 2 ^ 59
def prefixEnd_1222780 : Nat := 4983230072969 + 3 ^ 40 * 1222780 * 2
def baseEnd_1222780 : Nat := 627873874704831101326543

theorem tailTrace_1222780 : CollatzResearch.WordTrace tailWord_1222780 prefixEnd_1222780 627873874704831101326543 := by
  unfold tailWord_1222780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22299225255042184521484897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29732300340056246028646529 22299225255042184521484897)
  ·
    refine ⟨16724418941281638391113673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22299225255042184521484897 16724418941281638391113673)
    ·
      refine ⟨12543314205961228793335255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16724418941281638391113673 12543314205961228793335255)
      ·
        refine ⟨18814971308941843190002883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12543314205961228793335255 18814971308941843190002883)
        ·
          refine ⟨28222456963412764785004325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18814971308941843190002883 28222456963412764785004325)
          ·
            refine ⟨5291710680639893397188311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28222456963412764785004325 5291710680639893397188311)
            ·
              refine ⟨7937566020959840095782467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291710680639893397188311 7937566020959840095782467)
              ·
                refine ⟨11906349031439760143673701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7937566020959840095782467 11906349031439760143673701)
                ·
                  refine ⟨2232440443394955026938819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11906349031439760143673701 2232440443394955026938819)
                  ·
                    refine ⟨3348660665092432540408229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232440443394955026938819 3348660665092432540408229)
                    ·
                      refine ⟨627873874704831101326543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3348660665092432540408229 627873874704831101326543)
                      ·
                        rfl

theorem cell23_1222780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_1222780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222780 prefixEnd_1222780 := by exact prefixLift 1222780
  have htrace : WordTrace (prefixWord ++ tailWord_1222780) baseStart_1222780 baseEnd_1222780 := by
    simpa [prefixWord, tailWord_1222780, baseEnd_1222780] using wordTrace_append hprefix tailTrace_1222780
  have hstable : (prefixWord ++ tailWord_1222780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222780).length < 2 ^ (prefixWord ++ tailWord_1222780).sum := by decide
  have hdescent : baseEnd_1222780 < baseStart_1222780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222800 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_1222800 : Nat := 118140960795 + 1222800 * 2 ^ 59
def prefixEnd_1222800 : Nat := 4983230072969 + 3 ^ 40 * 1222800 * 2
def baseEnd_1222800 : Nat := 627884144317921023076451

theorem tailTrace_1222800 : CollatzResearch.WordTrace tailWord_1222800 prefixEnd_1222800 627884144317921023076451 := by
  unfold tailWord_1222800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22299589985005956229348927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29732786646674608305798569 22299589985005956229348927)
  ·
    refine ⟨33449384977508934344023391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22299589985005956229348927 33449384977508934344023391)
    ·
      refine ⟨50174077466263401516035087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33449384977508934344023391 50174077466263401516035087)
      ·
        refine ⟨75261116199395102274052631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50174077466263401516035087 75261116199395102274052631)
        ·
          refine ⟨112891674299092653411078947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75261116199395102274052631 112891674299092653411078947)
          ·
            refine ⟨169337511448638980116618421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112891674299092653411078947 169337511448638980116618421)
            ·
              refine ⟨15875391698309904385932977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169337511448638980116618421 15875391698309904385932977)
              ·
                refine ⟨11906543773732428289449733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15875391698309904385932977 11906543773732428289449733)
                ·
                  refine ⟨2232476957574830304271825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11906543773732428289449733 2232476957574830304271825)
                  ·
                    refine ⟨1674357718181122728203869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232476957574830304271825 1674357718181122728203869)
                    ·
                      refine ⟨627884144317921023076451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674357718181122728203869 627884144317921023076451)
                      ·
                        rfl

theorem cell23_1222800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_1222800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222800 prefixEnd_1222800 := by exact prefixLift 1222800
  have htrace : WordTrace (prefixWord ++ tailWord_1222800) baseStart_1222800 baseEnd_1222800 := by
    simpa [prefixWord, tailWord_1222800, baseEnd_1222800] using wordTrace_append hprefix tailTrace_1222800
  have hstable : (prefixWord ++ tailWord_1222800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222800).length < 2 ^ (prefixWord ++ tailWord_1222800).sum := by decide
  have hdescent : baseEnd_1222800 < baseStart_1222800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222817 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1222817 : Nat := 118140960795 + 1222817 * 2 ^ 59
def prefixEnd_1222817 : Nat := 4983230072969 + 3 ^ 40 * 1222817 * 2
def baseEnd_1222817 : Nat := 627892873489047456563873

theorem tailTrace_1222817 : CollatzResearch.WordTrace tailWord_1222817 prefixEnd_1222817 627892873489047456563873 := by
  unfold tailWord_1222817
  simp only [CollatzResearch.WordTrace]
  refine ⟨44599800010950324362066705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29733200007300216241377803 44599800010950324362066705)
  ·
    refine ⟨33449850008212743271550029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44599800010950324362066705 33449850008212743271550029)
    ·
      refine ⟨12543693753079778726831261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33449850008212743271550029 12543693753079778726831261)
      ·
        refine ⟨4703885157404917022561723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12543693753079778726831261 4703885157404917022561723)
        ·
          refine ⟨7055827736107375533842585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703885157404917022561723 7055827736107375533842585)
          ·
            refine ⟨5291870802080531650381939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7055827736107375533842585 5291870802080531650381939)
            ·
              refine ⟨7937806203120797475572909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291870802080531650381939 7937806203120797475572909)
              ·
                refine ⟨2976677326170299053339841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7937806203120797475572909 2976677326170299053339841)
                ·
                  refine ⟨2232507994627724290004881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976677326170299053339841 2232507994627724290004881)
                  ·
                    refine ⟨1674380995970793217503661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232507994627724290004881 1674380995970793217503661)
                    ·
                      refine ⟨627892873489047456563873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674380995970793217503661 627892873489047456563873)
                      ·
                        rfl

theorem cell23_1222817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1222817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222817 prefixEnd_1222817 := by exact prefixLift 1222817
  have htrace : WordTrace (prefixWord ++ tailWord_1222817) baseStart_1222817 baseEnd_1222817 := by
    simpa [prefixWord, tailWord_1222817, baseEnd_1222817] using wordTrace_append hprefix tailTrace_1222817
  have hstable : (prefixWord ++ tailWord_1222817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222817).length < 2 ^ (prefixWord ++ tailWord_1222817).sum := by decide
  have hdescent : baseEnd_1222817 < baseStart_1222817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222847 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 3]
def baseStart_1222847 : Nat := 118140960795 + 1222847 * 2 ^ 59
def prefixEnd_1222847 : Nat := 4983230072969 + 3 ^ 40 * 1222847 * 2
def baseEnd_1222847 : Nat := 627908277908682339188735

theorem tailTrace_1222847 : CollatzResearch.WordTrace tailWord_1222847 prefixEnd_1222847 627908277908682339188735 := by
  unfold tailWord_1222847
  simp only [CollatzResearch.WordTrace]
  refine ⟨44600894200841639485658795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29733929467227759657105863 44600894200841639485658795)
  ·
    refine ⟨66901341301262459228488193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44600894200841639485658795 66901341301262459228488193)
    ·
      refine ⟨50176005975946844421366145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66901341301262459228488193 50176005975946844421366145)
      ·
        refine ⟨37632004481960133316024609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50176005975946844421366145 37632004481960133316024609)
        ·
          refine ⟨28224003361470099987018457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37632004481960133316024609 28224003361470099987018457)
          ·
            refine ⟨21168002521102574990263843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28224003361470099987018457 21168002521102574990263843)
            ·
              refine ⟨31752003781653862485395765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21168002521102574990263843 31752003781653862485395765)
              ·
                refine ⟨2976750354530049608005853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31752003781653862485395765 2976750354530049608005853)
                ·
                  refine ⟨1116281382948768603002195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2976750354530049608005853 1116281382948768603002195)
                  ·
                    refine ⟨1674422074423152904503293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1116281382948768603002195 1674422074423152904503293)
                    ·
                      refine ⟨627908277908682339188735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674422074423152904503293 627908277908682339188735)
                      ·
                        rfl

theorem cell23_1222847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_1222847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222847 prefixEnd_1222847 := by exact prefixLift 1222847
  have htrace : WordTrace (prefixWord ++ tailWord_1222847) baseStart_1222847 baseEnd_1222847 := by
    simpa [prefixWord, tailWord_1222847, baseEnd_1222847] using wordTrace_append hprefix tailTrace_1222847
  have hstable : (prefixWord ++ tailWord_1222847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222847).length < 2 ^ (prefixWord ++ tailWord_1222847).sum := by decide
  have hdescent : baseEnd_1222847 < baseStart_1222847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222874 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_1222874 : Nat := 118140960795 + 1222874 * 2 ^ 59
def prefixEnd_1222874 : Nat := 4983230072969 + 3 ^ 40 * 1222874 * 2
def baseEnd_1222874 : Nat := 627922141886353733551111

theorem tailTrace_1222874 : CollatzResearch.WordTrace tailWord_1222874 prefixEnd_1222874 627922141886353733551111 := by
  unfold tailWord_1222874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150469742935955774222919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29734585981162548731261117 11150469742935955774222919)
  ·
    refine ⟨16725704614403933661334379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11150469742935955774222919 16725704614403933661334379)
    ·
      refine ⟨25088556921605900492001569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16725704614403933661334379 25088556921605900492001569)
      ·
        refine ⟨18816417691204425369001177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25088556921605900492001569 18816417691204425369001177)
        ·
          refine ⟨14112313268403319026750883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18816417691204425369001177 14112313268403319026750883)
          ·
            refine ⟨21168469902604978540126325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14112313268403319026750883 21168469902604978540126325)
            ·
              refine ⟨1984544053369216738136843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21168469902604978540126325 1984544053369216738136843)
              ·
                refine ⟨2976816080053825107205265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984544053369216738136843 2976816080053825107205265)
                ·
                  refine ⟨2232612060040368830403949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976816080053825107205265 2232612060040368830403949)
                  ·
                    refine ⟨837229522515138311401481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232612060040368830403949 837229522515138311401481)
                    ·
                      refine ⟨627922141886353733551111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837229522515138311401481 627922141886353733551111)
                      ·
                        rfl

theorem cell23_1222874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_1222874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222874 prefixEnd_1222874 := by exact prefixLift 1222874
  have htrace : WordTrace (prefixWord ++ tailWord_1222874) baseStart_1222874 baseEnd_1222874 := by
    simpa [prefixWord, tailWord_1222874, baseEnd_1222874] using wordTrace_append hprefix tailTrace_1222874
  have hstable : (prefixWord ++ tailWord_1222874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222874).length < 2 ^ (prefixWord ++ tailWord_1222874).sum := by decide
  have hdescent : baseEnd_1222874 < baseStart_1222874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222880 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_1222880 : Nat := 118140960795 + 1222880 * 2 ^ 59
def prefixEnd_1222880 : Nat := 4983230072969 + 3 ^ 40 * 1222880 * 2
def baseEnd_1222880 : Nat := 209308407590093570025361

theorem tailTrace_1222880 : CollatzResearch.WordTrace tailWord_1222880 prefixEnd_1222880 209308407590093570025361 := by
  unfold tailWord_1222880
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301048904861043060805047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29734731873148057414406729 22301048904861043060805047)
  ·
    refine ⟨33451573357291564591207571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22301048904861043060805047 33451573357291564591207571)
    ·
      refine ⟨50177360035937346886811357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33451573357291564591207571 50177360035937346886811357)
      ·
        refine ⟨18816510013476505082554259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50177360035937346886811357 18816510013476505082554259)
        ·
          refine ⟨28224765020214757623831389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18816510013476505082554259 28224765020214757623831389)
          ·
            refine ⟨10584286882580534108936771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28224765020214757623831389 10584286882580534108936771)
            ·
              refine ⟨15876430323870801163405157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10584286882580534108936771 15876430323870801163405157)
              ·
                refine ⟨2976830685725775218138467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15876430323870801163405157 2976830685725775218138467)
                ·
                  refine ⟨4465246028588662827207701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976830685725775218138467 4465246028588662827207701)
                  ·
                    refine ⟨209308407590093570025361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4465246028588662827207701 209308407590093570025361)
                    ·
                      rfl

theorem cell23_1222880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_1222880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222880 prefixEnd_1222880 := by exact prefixLift 1222880
  have htrace : WordTrace (prefixWord ++ tailWord_1222880) baseStart_1222880 baseEnd_1222880 := by
    simpa [prefixWord, tailWord_1222880, baseEnd_1222880] using wordTrace_append hprefix tailTrace_1222880
  have hstable : (prefixWord ++ tailWord_1222880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222880).length < 2 ^ (prefixWord ++ tailWord_1222880).sum := by decide
  have hdescent : baseEnd_1222880 < baseStart_1222880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222881 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_1222881 : Nat := 118140960795 + 1222881 * 2 ^ 59
def prefixEnd_1222881 : Nat := 4983230072969 + 3 ^ 40 * 1222881 * 2
def baseEnd_1222881 : Nat := 627925736250935206163579

theorem tailTrace_1222881 : CollatzResearch.WordTrace tailWord_1222881 prefixEnd_1222881 627925736250935206163579 := by
  unfold tailWord_1222881
  simp only [CollatzResearch.WordTrace]
  refine ⟨44602134282718463292396497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29734756188478975528264331 44602134282718463292396497)
  ·
    refine ⟨33451600712038847469297373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44602134282718463292396497 33451600712038847469297373)
    ·
      refine ⟨12544350267014567800986515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33451600712038847469297373 12544350267014567800986515)
      ·
        refine ⟨18816525400521851701479773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12544350267014567800986515 18816525400521851701479773)
        ·
          refine ⟨7056197025195694388054915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18816525400521851701479773 7056197025195694388054915)
          ·
            refine ⟨10584295537793541582082373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056197025195694388054915 10584295537793541582082373)
            ·
              refine ⟨1984555413336289046640445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10584295537793541582082373 1984555413336289046640445)
              ·
                refine ⟨744208280001108392490167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1984555413336289046640445 744208280001108392490167)
                ·
                  refine ⟨1116312420001662588735251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744208280001108392490167 1116312420001662588735251)
                  ·
                    refine ⟨1674468630002493883102877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1116312420001662588735251 1674468630002493883102877)
                    ·
                      refine ⟨627925736250935206163579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674468630002493883102877 627925736250935206163579)
                      ·
                        rfl

theorem cell23_1222881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_1222881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222881 prefixEnd_1222881 := by exact prefixLift 1222881
  have htrace : WordTrace (prefixWord ++ tailWord_1222881) baseStart_1222881 baseEnd_1222881 := by
    simpa [prefixWord, tailWord_1222881, baseEnd_1222881] using wordTrace_append hprefix tailTrace_1222881
  have hstable : (prefixWord ++ tailWord_1222881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222881).length < 2 ^ (prefixWord ++ tailWord_1222881).sum := by decide
  have hdescent : baseEnd_1222881 < baseStart_1222881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222914 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1222914 : Nat := 118140960795 + 1222914 * 2 ^ 59
def prefixEnd_1222914 : Nat := 4983230072969 + 3 ^ 40 * 1222914 * 2
def baseEnd_1222914 : Nat := 209314227037511192350309

theorem tailTrace_1222914 : CollatzResearch.WordTrace tailWord_1222914 prefixEnd_1222914 209314227037511192350309 := by
  unfold tailWord_1222914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150834472899727482086949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29735558594399273285565197 11150834472899727482086949)
  ·
    refine ⟨2090781463668698902891303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11150834472899727482086949 2090781463668698902891303)
    ·
      refine ⟨3136172195503048354336955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090781463668698902891303 3136172195503048354336955)
      ·
        refine ⟨4704258293254572531505433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136172195503048354336955 4704258293254572531505433)
        ·
          refine ⟨3528193719940929398629075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4704258293254572531505433 3528193719940929398629075)
          ·
            refine ⟨5292290579911394097943613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528193719940929398629075 5292290579911394097943613)
            ·
              refine ⟨1984608967466772786728855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5292290579911394097943613 1984608967466772786728855)
              ·
                refine ⟨2976913451200159180093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984608967466772786728855 2976913451200159180093283)
                ·
                  refine ⟨4465370176800238770139925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976913451200159180093283 4465370176800238770139925)
                  ·
                    refine ⟨209314227037511192350309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4465370176800238770139925 209314227037511192350309)
                    ·
                      rfl

theorem cell23_1222914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1222914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222914 prefixEnd_1222914 := by exact prefixLift 1222914
  have htrace : WordTrace (prefixWord ++ tailWord_1222914) baseStart_1222914 baseEnd_1222914 := by
    simpa [prefixWord, tailWord_1222914, baseEnd_1222914] using wordTrace_append hprefix tailTrace_1222914
  have hstable : (prefixWord ++ tailWord_1222914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222914).length < 2 ^ (prefixWord ++ tailWord_1222914).sum := by decide
  have hdescent : baseEnd_1222914 < baseStart_1222914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222924 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_1222924 : Nat := 118140960795 + 1222924 * 2 ^ 59
def prefixEnd_1222924 : Nat := 4983230072969 + 3 ^ 40 * 1222924 * 2
def baseEnd_1222924 : Nat := 627947815919078537925881

theorem tailTrace_1222924 : CollatzResearch.WordTrace tailWord_1222924 prefixEnd_1222924 627947815919078537925881 := by
  unfold tailWord_1222924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301851310781340818105913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29735801747708454424141217 22301851310781340818105913)
  ·
    refine ⟨16726388483086005613579435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22301851310781340818105913 16726388483086005613579435)
    ·
      refine ⟨25089582724629008420369153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16726388483086005613579435 25089582724629008420369153)
      ·
        refine ⟨18817187043471756315276865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25089582724629008420369153 18817187043471756315276865)
        ·
          refine ⟨14112890282603817236457649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18817187043471756315276865 14112890282603817236457649)
          ·
            refine ⟨10584667711952862927343237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14112890282603817236457649 10584667711952862927343237)
            ·
              refine ⟨1984625195991161798876857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10584667711952862927343237 1984625195991161798876857)
              ·
                refine ⟨1488468896993371349157643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984625195991161798876857 1488468896993371349157643)
                ·
                  refine ⟨2232703345490057023736465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488468896993371349157643 2232703345490057023736465)
                  ·
                    refine ⟨1674527509117542767802349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232703345490057023736465 1674527509117542767802349)
                    ·
                      refine ⟨627947815919078537925881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674527509117542767802349 627947815919078537925881)
                      ·
                        rfl

theorem cell23_1222924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_1222924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222924 prefixEnd_1222924 := by exact prefixLift 1222924
  have htrace : WordTrace (prefixWord ++ tailWord_1222924) baseStart_1222924 baseEnd_1222924 := by
    simpa [prefixWord, tailWord_1222924, baseEnd_1222924] using wordTrace_append hprefix tailTrace_1222924
  have hstable : (prefixWord ++ tailWord_1222924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222924).length < 2 ^ (prefixWord ++ tailWord_1222924).sum := by decide
  have hdescent : baseEnd_1222924 < baseStart_1222924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222940 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1222940 : Nat := 118140960795 + 1222940 * 2 ^ 59
def prefixEnd_1222940 : Nat := 4983230072969 + 3 ^ 40 * 1222940 * 2
def baseEnd_1222940 : Nat := 209318677203183491775269

theorem tailTrace_1222940 : CollatzResearch.WordTrace tailWord_1222940 prefixEnd_1222940 209318677203183491775269 := by
  unfold tailWord_1222940
  simp only [CollatzResearch.WordTrace]
  refine ⟨22302143094752358184397137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29736190793003144245862849 22302143094752358184397137)
  ·
    refine ⟨16726607321064268638297853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22302143094752358184397137 16726607321064268638297853)
    ·
      refine ⟨6272477745399100739361695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16726607321064268638297853 6272477745399100739361695)
      ·
        refine ⟨9408716618098651109042543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272477745399100739361695 9408716618098651109042543)
        ·
          refine ⟨14113074927147976663563815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408716618098651109042543 14113074927147976663563815)
          ·
            refine ⟨21169612390721964995345723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14113074927147976663563815 21169612390721964995345723)
            ·
              refine ⟨31754418586082947493018585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21169612390721964995345723 31754418586082947493018585)
              ·
                refine ⟨23815813939562210619763939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31754418586082947493018585 23815813939562210619763939)
                ·
                  refine ⟨35723720909343315929645909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23815813939562210619763939 35723720909343315929645909)
                  ·
                    refine ⟨209318677203183491775269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35723720909343315929645909 209318677203183491775269)
                    ·
                      rfl

theorem cell23_1222940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1222940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222940 prefixEnd_1222940 := by exact prefixLift 1222940
  have htrace : WordTrace (prefixWord ++ tailWord_1222940) baseStart_1222940 baseEnd_1222940 := by
    simpa [prefixWord, tailWord_1222940, baseEnd_1222940] using wordTrace_append hprefix tailTrace_1222940
  have hstable : (prefixWord ++ tailWord_1222940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222940).length < 2 ^ (prefixWord ++ tailWord_1222940).sum := by decide
  have hdescent : baseEnd_1222940 < baseStart_1222940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222994 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_1222994 : Nat := 118140960795 + 1222994 * 2 ^ 59
def prefixEnd_1222994 : Nat := 4983230072969 + 3 ^ 40 * 1222994 * 2
def baseEnd_1222994 : Nat := 627983759564893264050559

theorem tailTrace_1222994 : CollatzResearch.WordTrace tailWord_1222994 prefixEnd_1222994 627983759564893264050559 := by
  unfold tailWord_1222994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11151563932827270897815009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29737503820872722394173357 11151563932827270897815009)
  ·
    refine ⟨8363672949620453173361257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11151563932827270897815009 8363672949620453173361257)
    ·
      refine ⟨6272754712215339880020943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8363672949620453173361257 6272754712215339880020943)
      ·
        refine ⟨9409132068323009820031415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272754712215339880020943 9409132068323009820031415)
        ·
          refine ⟨14113698102484514730047123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409132068323009820031415 14113698102484514730047123)
          ·
            refine ⟨21170547153726772095070685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14113698102484514730047123 21170547153726772095070685)
            ·
              refine ⟨7938955182647539535651507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21170547153726772095070685 7938955182647539535651507)
              ·
                refine ⟨11908432773971309303477261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938955182647539535651507 11908432773971309303477261)
                ·
                  refine ⟨4465662290239240988803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11908432773971309303477261 4465662290239240988803973)
                  ·
                    refine ⟨837311679419857685400745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4465662290239240988803973 837311679419857685400745)
                    ·
                      refine ⟨627983759564893264050559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837311679419857685400745 627983759564893264050559)
                      ·
                        rfl

theorem cell23_1222994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_1222994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222994 prefixEnd_1222994 := by exact prefixLift 1222994
  have htrace : WordTrace (prefixWord ++ tailWord_1222994) baseStart_1222994 baseEnd_1222994 := by
    simpa [prefixWord, tailWord_1222994, baseEnd_1222994] using wordTrace_append hprefix tailTrace_1222994
  have hstable : (prefixWord ++ tailWord_1222994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222994).length < 2 ^ (prefixWord ++ tailWord_1222994).sum := by decide
  have hdescent : baseEnd_1222994 < baseStart_1222994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223000 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 11]
def baseStart_1223000 : Nat := 118140960795 + 1223000 * 2 ^ 59
def prefixEnd_1223000 : Nat := 4983230072969 + 3 ^ 40 * 1223000 * 2
def baseEnd_1223000 : Nat := 69776315605424471175059

theorem tailTrace_1223000 : CollatzResearch.WordTrace tailWord_1223000 prefixEnd_1223000 69776315605424471175059 := by
  unfold tailWord_1223000
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303237284643673307989227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29737649712858231077318969 22303237284643673307989227)
  ·
    refine ⟨33454855926965509961983841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22303237284643673307989227 33454855926965509961983841)
    ·
      refine ⟨25091141945224132471487881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33454855926965509961983841 25091141945224132471487881)
      ·
        refine ⟨18818356458918099353615911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25091141945224132471487881 18818356458918099353615911)
        ·
          refine ⟨28227534688377149030423867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18818356458918099353615911 28227534688377149030423867)
          ·
            refine ⟨42341302032565723545635801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28227534688377149030423867 42341302032565723545635801)
            ·
              refine ⟨31755976524424292659226851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42341302032565723545635801 31755976524424292659226851)
              ·
                refine ⟨47633964786636438988840277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31755976524424292659226851 47633964786636438988840277)
                ·
                  refine ⟨69776315605424471175059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 47633964786636438988840277 69776315605424471175059)
                  ·
                    rfl

theorem cell23_1223000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_1223000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223000 prefixEnd_1223000 := by exact prefixLift 1223000
  have htrace : WordTrace (prefixWord ++ tailWord_1223000) baseStart_1223000 baseEnd_1223000 := by
    simpa [prefixWord, tailWord_1223000, baseEnd_1223000] using wordTrace_append hprefix tailTrace_1223000
  have hstable : (prefixWord ++ tailWord_1223000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223000).length < 2 ^ (prefixWord ++ tailWord_1223000).sum := by decide
  have hdescent : baseEnd_1223000 < baseStart_1223000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223006 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1223006 : Nat := 118140960795 + 1223006 * 2 ^ 59
def prefixEnd_1223006 : Nat := 4983230072969 + 3 ^ 40 * 1223006 * 2
def baseEnd_1223006 : Nat := 627989921332747217100505

theorem tailTrace_1223006 : CollatzResearch.WordTrace tailWord_1223006 prefixEnd_1223006 627989921332747217100505 := by
  unfold tailWord_1223006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575836675908201205087109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29737795604843739760464581 5575836675908201205087109)
  ·
    refine ⟨1045469376732787725953833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5575836675908201205087109 1045469376732787725953833)
    ·
      refine ⟨784102032549590794465375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1045469376732787725953833 784102032549590794465375)
      ·
        refine ⟨1176153048824386191698063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784102032549590794465375 1176153048824386191698063)
        ·
          refine ⟨1764229573236579287547095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176153048824386191698063 1764229573236579287547095)
          ·
            refine ⟨2646344359854868931320643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764229573236579287547095 2646344359854868931320643)
            ·
              refine ⟨3969516539782303396980965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646344359854868931320643 3969516539782303396980965)
              ·
                refine ⟨744284351209181886933931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3969516539782303396980965 744284351209181886933931)
                ·
                  refine ⟨1116426526813772830400897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744284351209181886933931 1116426526813772830400897)
                  ·
                    refine ⟨837319895110329622800673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1116426526813772830400897 837319895110329622800673)
                    ·
                      refine ⟨627989921332747217100505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837319895110329622800673 627989921332747217100505)
                      ·
                        rfl

theorem cell23_1223006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1223006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223006 prefixEnd_1223006 := by exact prefixLift 1223006
  have htrace : WordTrace (prefixWord ++ tailWord_1223006) baseStart_1223006 baseEnd_1223006 := by
    simpa [prefixWord, tailWord_1223006, baseEnd_1223006] using wordTrace_append hprefix tailTrace_1223006
  have hstable : (prefixWord ++ tailWord_1223006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223006).length < 2 ^ (prefixWord ++ tailWord_1223006).sum := by decide
  have hdescent : baseEnd_1223006 < baseStart_1223006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223027 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3]
def baseStart_1223027 : Nat := 118140960795 + 1223027 * 2 ^ 59
def prefixEnd_1223027 : Nat := 4983230072969 + 3 ^ 40 * 1223027 * 2
def baseEnd_1223027 : Nat := 628000704426491634937907

theorem tailTrace_1223027 : CollatzResearch.WordTrace tailWord_1223027 prefixEnd_1223027 628000704426491634937907 := by
  unfold tailWord_1223027
  simp only [CollatzResearch.WordTrace]
  refine ⟨44607459340189530227211335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29738306226793020151474223 44607459340189530227211335)
  ·
    refine ⟨66911189010284295340817003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44607459340189530227211335 66911189010284295340817003)
    ·
      refine ⟨100366783515426443011225505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66911189010284295340817003 100366783515426443011225505)
      ·
        refine ⟨75275087636569832258419129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100366783515426443011225505 75275087636569832258419129)
        ·
          refine ⟨56456315727427374193814347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75275087636569832258419129 56456315727427374193814347)
          ·
            refine ⟨84684473591141061290721521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56456315727427374193814347 84684473591141061290721521)
            ·
              refine ⟨63513355193355795968041141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84684473591141061290721521 63513355193355795968041141)
              ·
                refine ⟨5954377049377105872003857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63513355193355795968041141 5954377049377105872003857)
                ·
                  refine ⟨4465782787032829404002893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5954377049377105872003857 4465782787032829404002893)
                  ·
                    refine ⟨1674668545137311026501085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4465782787032829404002893 1674668545137311026501085)
                    ·
                      refine ⟨628000704426491634937907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674668545137311026501085 628000704426491634937907)
                      ·
                        rfl

theorem cell23_1223027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_1223027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223027 prefixEnd_1223027 := by exact prefixLift 1223027
  have htrace : WordTrace (prefixWord ++ tailWord_1223027) baseStart_1223027 baseEnd_1223027 := by
    simpa [prefixWord, tailWord_1223027, baseEnd_1223027] using wordTrace_append hprefix tailTrace_1223027
  have hstable : (prefixWord ++ tailWord_1223027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223027).length < 2 ^ (prefixWord ++ tailWord_1223027).sum := by decide
  have hdescent : baseEnd_1223027 < baseStart_1223027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223047 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 7]
def baseStart_1223047 : Nat := 118140960795 + 1223047 * 2 ^ 59
def prefixEnd_1223047 : Nat := 4983230072969 + 3 ^ 40 * 1223047 * 2
def baseEnd_1223047 : Nat := 209336991346527185562605

theorem tailTrace_1223047 : CollatzResearch.WordTrace tailWord_1223047 prefixEnd_1223047 209336991346527185562605 := by
  unfold tailWord_1223047
  simp only [CollatzResearch.WordTrace]
  refine ⟨44608188800117073642939395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29738792533411382428626263 44608188800117073642939395)
  ·
    refine ⟨66912283200175610464409093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44608188800117073642939395 66912283200175610464409093)
    ·
      refine ⟨12546053100032926962076705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66912283200175610464409093 12546053100032926962076705)
      ·
        refine ⟨9409539825024695221557529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12546053100032926962076705 9409539825024695221557529)
        ·
          refine ⟨7057154868768521416168147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9409539825024695221557529 7057154868768521416168147)
          ·
            refine ⟨10585732303152782124252221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057154868768521416168147 10585732303152782124252221)
            ·
              refine ⟨3969649613682293296594583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10585732303152782124252221 3969649613682293296594583)
              ·
                refine ⟨5954474420523439944891875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969649613682293296594583 5954474420523439944891875)
                ·
                  refine ⟨8931711630785159917337813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5954474420523439944891875 8931711630785159917337813)
                  ·
                    refine ⟨209336991346527185562605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8931711630785159917337813 209336991346527185562605)
                    ·
                      rfl

theorem cell23_1223047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_1223047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223047 prefixEnd_1223047 := by exact prefixLift 1223047
  have htrace : WordTrace (prefixWord ++ tailWord_1223047) baseStart_1223047 baseEnd_1223047 := by
    simpa [prefixWord, tailWord_1223047, baseEnd_1223047] using wordTrace_append hprefix tailTrace_1223047
  have hstable : (prefixWord ++ tailWord_1223047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223047).length < 2 ^ (prefixWord ++ tailWord_1223047).sum := by decide
  have hdescent : baseEnd_1223047 < baseStart_1223047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223104 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_1223104 : Nat := 118140960795 + 1223104 * 2 ^ 59
def prefixEnd_1223104 : Nat := 4983230072969 + 3 ^ 40 * 1223104 * 2
def baseEnd_1223104 : Nat := 628040242436887833675053

theorem tailTrace_1223104 : CollatzResearch.WordTrace tailWord_1223104 prefixEnd_1223104 628040242436887833675053 := by
  unfold tailWord_1223104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305133880455286188882183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29740178507273714918509577 22305133880455286188882183)
  ·
    refine ⟨33457700820682929283323275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22305133880455286188882183 33457700820682929283323275)
    ·
      refine ⟨50186551231024393924984913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33457700820682929283323275 50186551231024393924984913)
      ·
        refine ⟨37639913423268295443738685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50186551231024393924984913 37639913423268295443738685)
        ·
          refine ⟨14114967533725610791402007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37639913423268295443738685 14114967533725610791402007)
          ·
            refine ⟨21172451300588416187103011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14114967533725610791402007 21172451300588416187103011)
            ·
              refine ⟨31758676950882624280654517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21172451300588416187103011 31758676950882624280654517)
              ·
                refine ⟨2977375964145246026311361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31758676950882624280654517 2977375964145246026311361)
                ·
                  refine ⟨2233031973108934519733521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2977375964145246026311361 2233031973108934519733521)
                  ·
                    refine ⟨1674773979831700889800141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2233031973108934519733521 1674773979831700889800141)
                    ·
                      refine ⟨628040242436887833675053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674773979831700889800141 628040242436887833675053)
                      ·
                        rfl

theorem cell23_1223104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_1223104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223104 prefixEnd_1223104 := by exact prefixLift 1223104
  have htrace : WordTrace (prefixWord ++ tailWord_1223104) baseStart_1223104 baseEnd_1223104 := by
    simpa [prefixWord, tailWord_1223104, baseEnd_1223104] using wordTrace_append hprefix tailTrace_1223104
  have hstable : (prefixWord ++ tailWord_1223104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223104).length < 2 ^ (prefixWord ++ tailWord_1223104).sum := by decide
  have hdescent : baseEnd_1223104 < baseStart_1223104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223124 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 8]
def baseStart_1223124 : Nat := 118140960795 + 1223124 * 2 ^ 59
def prefixEnd_1223124 : Nat := 4983230072969 + 3 ^ 40 * 1223124 * 2
def baseEnd_1223124 : Nat := 69783390227775306158329

theorem tailTrace_1223124 : CollatzResearch.WordTrace tailWord_1223124 prefixEnd_1223124 69783390227775306158329 := by
  unfold tailWord_1223124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305498610419057896746213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29740664813892077195661617 22305498610419057896746213)
  ·
    refine ⟨4182280989453573355639915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22305498610419057896746213 4182280989453573355639915)
    ·
      refine ⟨6273421484180360033459873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182280989453573355639915 6273421484180360033459873)
      ·
        refine ⟨4705066113135270025094905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6273421484180360033459873 4705066113135270025094905)
        ·
          refine ⟨3528799584851452518821179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4705066113135270025094905 3528799584851452518821179)
          ·
            refine ⟨5293199377277178778231769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528799584851452518821179 5293199377277178778231769)
            ·
              refine ⟨3969899532957884083673827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5293199377277178778231769 3969899532957884083673827)
              ·
                refine ⟨5954849299436826125510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969899532957884083673827 5954849299436826125510741)
                ·
                  refine ⟨69783390227775306158329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5954849299436826125510741 69783390227775306158329)
                  ·
                    rfl

theorem cell23_1223124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_1223124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223124 prefixEnd_1223124 := by exact prefixLift 1223124
  have htrace : WordTrace (prefixWord ++ tailWord_1223124) baseStart_1223124 baseEnd_1223124 := by
    simpa [prefixWord, tailWord_1223124, baseEnd_1223124] using wordTrace_append hprefix tailTrace_1223124
  have hstable : (prefixWord ++ tailWord_1223124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223124).length < 2 ^ (prefixWord ++ tailWord_1223124).sum := by decide
  have hdescent : baseEnd_1223124 < baseStart_1223124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223141 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 6]
def baseStart_1223141 : Nat := 118140960795 + 1223141 * 2 ^ 59
def prefixEnd_1223141 : Nat := 4983230072969 + 3 ^ 40 * 1223141 * 2
def baseEnd_1223141 : Nat := 69784360135678243212487

theorem tailTrace_1223141 : CollatzResearch.WordTrace tailWord_1223141 prefixEnd_1223141 69784360135678243212487 := by
  unfold tailWord_1223141
  simp only [CollatzResearch.WordTrace]
  refine ⟨44611617261776527696861277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29741078174517685131240851 44611617261776527696861277)
  ·
    refine ⟨16729356473166197886322979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44611617261776527696861277 16729356473166197886322979)
    ·
      refine ⟨25094034709749296829484469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16729356473166197886322979 25094034709749296829484469)
      ·
        refine ⟨2352565754038996577764169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25094034709749296829484469 2352565754038996577764169)
        ·
          refine ⟨1764424315529247433323127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352565754038996577764169 1764424315529247433323127)
          ·
            refine ⟨2646636473293871149984691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764424315529247433323127 2646636473293871149984691)
            ·
              refine ⟨3969954709940806724977037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646636473293871149984691 3969954709940806724977037)
              ·
                refine ⟨1488733016227802521866389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969954709940806724977037 1488733016227802521866389)
                ·
                  refine ⟨69784360135678243212487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1488733016227802521866389 69784360135678243212487)
                  ·
                    rfl

theorem cell23_1223141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_1223141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223141 prefixEnd_1223141 := by exact prefixLift 1223141
  have htrace : WordTrace (prefixWord ++ tailWord_1223141) baseStart_1223141 baseEnd_1223141 := by
    simpa [prefixWord, tailWord_1223141, baseEnd_1223141] using wordTrace_append hprefix tailTrace_1223141
  have hstable : (prefixWord ++ tailWord_1223141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223141).length < 2 ^ (prefixWord ++ tailWord_1223141).sum := by decide
  have hdescent : baseEnd_1223141 < baseStart_1223141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223161 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 2, 3, 2]
def baseStart_1223161 : Nat := 118140960795 + 1223161 * 2 ^ 59
def prefixEnd_1223161 : Nat := 4983230072969 + 3 ^ 40 * 1223161 * 2
def baseEnd_1223161 : Nat := 628069510834194110662291

theorem tailTrace_1223161 : CollatzResearch.WordTrace tailWord_1223161 prefixEnd_1223161 628069510834194110662291 := by
  unfold tailWord_1223161
  simp only [CollatzResearch.WordTrace]
  refine ⟨44612346721704071112589337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29741564481136047408392891 44612346721704071112589337)
  ·
    refine ⟨33459260041278053334442003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44612346721704071112589337 33459260041278053334442003)
    ·
      refine ⟨50188890061917080001663005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33459260041278053334442003 50188890061917080001663005)
      ·
        refine ⟨18820833773218905000623627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50188890061917080001663005 18820833773218905000623627)
        ·
          refine ⟨28231250659828357500935441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18820833773218905000623627 28231250659828357500935441)
          ·
            refine ⟨21173437994871268125701581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28231250659828357500935441 21173437994871268125701581)
            ·
              refine ⟨7940039248076725547138093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21173437994871268125701581 7940039248076725547138093)
              ·
                refine ⟨2977514718028772080176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7940039248076725547138093 2977514718028772080176785)
                ·
                  refine ⟨2233136038521579060132589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2977514718028772080176785 2233136038521579060132589)
                  ·
                    refine ⟨837426014445592147549721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233136038521579060132589 837426014445592147549721)
                    ·
                      refine ⟨628069510834194110662291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837426014445592147549721 628069510834194110662291)
                      ·
                        rfl

theorem cell23_1223161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_1223161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223161 prefixEnd_1223161 := by exact prefixLift 1223161
  have htrace : WordTrace (prefixWord ++ tailWord_1223161) baseStart_1223161 baseEnd_1223161 := by
    simpa [prefixWord, tailWord_1223161, baseEnd_1223161] using wordTrace_append hprefix tailTrace_1223161
  have hstable : (prefixWord ++ tailWord_1223161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223161).length < 2 ^ (prefixWord ++ tailWord_1223161).sum := by decide
  have hdescent : baseEnd_1223161 < baseStart_1223161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223171 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 1, 5]
def baseStart_1223171 : Nat := 118140960795 + 1223171 * 2 ^ 59
def prefixEnd_1223171 : Nat := 4983230072969 + 3 ^ 40 * 1223171 * 2
def baseEnd_1223171 : Nat := 209358215213579690512415

theorem tailTrace_1223171 : CollatzResearch.WordTrace tailWord_1223171 prefixEnd_1223171 209358215213579690512415 := by
  unfold tailWord_1223171
  simp only [CollatzResearch.WordTrace]
  refine ⟨44612711451667842820453367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29741807634445228546968911 44612711451667842820453367)
  ·
    refine ⟨66919067177501764230680051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44612711451667842820453367 66919067177501764230680051)
    ·
      refine ⟨100378600766252646346020077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66919067177501764230680051 100378600766252646346020077)
      ·
        refine ⟨37641975287344742379757529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100378600766252646346020077 37641975287344742379757529)
        ·
          refine ⟨28231481465508556784818147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37641975287344742379757529 28231481465508556784818147)
          ·
            refine ⟨42347222198262835177227221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28231481465508556784818147 42347222198262835177227221)
            ·
              refine ⟨992513020271785199466263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42347222198262835177227221 992513020271785199466263)
              ·
                refine ⟨1488769530407677799199395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992513020271785199466263 1488769530407677799199395)
                ·
                  refine ⟨2233154295611516698799093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488769530407677799199395 2233154295611516698799093)
                  ·
                    refine ⟨209358215213579690512415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2233154295611516698799093 209358215213579690512415)
                    ·
                      rfl

theorem cell23_1223171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 5].length) (baseStart_1223171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223171 prefixEnd_1223171 := by exact prefixLift 1223171
  have htrace : WordTrace (prefixWord ++ tailWord_1223171) baseStart_1223171 baseEnd_1223171 := by
    simpa [prefixWord, tailWord_1223171, baseEnd_1223171] using wordTrace_append hprefix tailTrace_1223171
  have hstable : (prefixWord ++ tailWord_1223171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223171).length < 2 ^ (prefixWord ++ tailWord_1223171).sum := by decide
  have hdescent : baseEnd_1223171 < baseStart_1223171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223194 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1223194 : Nat := 118140960795 + 1223194 * 2 ^ 59
def prefixEnd_1223194 : Nat := 4983230072969 + 3 ^ 40 * 1223194 * 2
def baseEnd_1223194 : Nat := 628086455695792481549639

theorem tailTrace_1223194 : CollatzResearch.WordTrace tailWord_1223194 prefixEnd_1223194 628086455695792481549639 := by
  unfold tailWord_1223194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11153387582646129437135159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29742366887056345165693757 11153387582646129437135159)
  ·
    refine ⟨16730081373969194155702739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11153387582646129437135159 16730081373969194155702739)
    ·
      refine ⟨25095122060953791233554109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16730081373969194155702739 25095122060953791233554109)
      ·
        refine ⟨9410670772857671712582791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25095122060953791233554109 9410670772857671712582791)
        ·
          refine ⟨14116006159286507568874187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9410670772857671712582791 14116006159286507568874187)
          ·
            refine ⟨21174009238929761353311281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14116006159286507568874187 21174009238929761353311281)
            ·
              refine ⟨15880506929197321014983461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21174009238929761353311281 15880506929197321014983461)
              ·
                refine ⟨2977595049224497690309399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15880506929197321014983461 2977595049224497690309399)
                ·
                  refine ⟨4466392573836746535464099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977595049224497690309399 4466392573836746535464099)
                  ·
                    refine ⟨6699588860755119803196149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466392573836746535464099 6699588860755119803196149)
                    ·
                      refine ⟨628086455695792481549639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6699588860755119803196149 628086455695792481549639)
                      ·
                        rfl

theorem cell23_1223194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1223194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223194 prefixEnd_1223194 := by exact prefixLift 1223194
  have htrace : WordTrace (prefixWord ++ tailWord_1223194) baseStart_1223194 baseEnd_1223194 := by
    simpa [prefixWord, tailWord_1223194, baseEnd_1223194] using wordTrace_append hprefix tailTrace_1223194
  have hstable : (prefixWord ++ tailWord_1223194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223194).length < 2 ^ (prefixWord ++ tailWord_1223194).sum := by decide
  have hdescent : baseEnd_1223194 < baseStart_1223194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223201 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1223201 : Nat := 118140960795 + 1223201 * 2 ^ 59
def prefixEnd_1223201 : Nat := 4983230072969 + 3 ^ 40 * 1223201 * 2
def baseEnd_1223201 : Nat := 209363350020124651387369

theorem tailTrace_1223201 : CollatzResearch.WordTrace tailWord_1223201 prefixEnd_1223201 209363350020124651387369 := by
  unfold tailWord_1223201
  simp only [CollatzResearch.WordTrace]
  refine ⟨44613805641559157944045457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29742537094372771962696971 44613805641559157944045457)
  ·
    refine ⟨33460354231169368458034093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44613805641559157944045457 33460354231169368458034093)
    ·
      refine ⟨12547632836688513171762785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33460354231169368458034093 12547632836688513171762785)
      ·
        refine ⟨9410724627516384878822089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12547632836688513171762785 9410724627516384878822089)
        ·
          refine ⟨7058043470637288659116567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9410724627516384878822089 7058043470637288659116567)
          ·
            refine ⟨10587065205955932988674851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058043470637288659116567 10587065205955932988674851)
            ·
              refine ⟨15880597808933899483012277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10587065205955932988674851 15880597808933899483012277)
              ·
                refine ⟨1488806044587553076532401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15880597808933899483012277 1488806044587553076532401)
                ·
                  refine ⟨1116604533440664807399301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488806044587553076532401 1116604533440664807399301)
                  ·
                    refine ⟨209363350020124651387369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116604533440664807399301 209363350020124651387369)
                    ·
                      rfl

theorem cell23_1223201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1223201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223201 prefixEnd_1223201 := by exact prefixLift 1223201
  have htrace : WordTrace (prefixWord ++ tailWord_1223201) baseStart_1223201 baseEnd_1223201 := by
    simpa [prefixWord, tailWord_1223201, baseEnd_1223201] using wordTrace_append hprefix tailTrace_1223201
  have hstable : (prefixWord ++ tailWord_1223201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223201).length < 2 ^ (prefixWord ++ tailWord_1223201).sum := by decide
  have hdescent : baseEnd_1223201 < baseStart_1223201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223228 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_1223228 : Nat := 118140960795 + 1223228 * 2 ^ 59
def prefixEnd_1223228 : Nat := 4983230072969 + 3 ^ 40 * 1223228 * 2
def baseEnd_1223228 : Nat := 628103914038045348524483

theorem tailTrace_1223228 : CollatzResearch.WordTrace tailWord_1223228 prefixEnd_1223228 628103914038045348524483 := by
  unfold tailWord_1223228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22307395206230670777639169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29743193608307561036852225 22307395206230670777639169)
  ·
    refine ⟨16730546404673003083229377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22307395206230670777639169 16730546404673003083229377)
    ·
      refine ⟨12547909803504752312422033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16730546404673003083229377 12547909803504752312422033)
      ·
        refine ⟨9410932352628564234316525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12547909803504752312422033 9410932352628564234316525)
        ·
          refine ⟨3529099632235711587868697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9410932352628564234316525 3529099632235711587868697)
          ·
            refine ⟨2646824724176783690901523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529099632235711587868697 2646824724176783690901523)
            ·
              refine ⟨3970237086265175536352285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646824724176783690901523 3970237086265175536352285)
              ·
                refine ⟨1488838907349440826132107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3970237086265175536352285 1488838907349440826132107)
                ·
                  refine ⟨2233258361024161239198161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488838907349440826132107 2233258361024161239198161)
                  ·
                    refine ⟨1674943770768120929398621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2233258361024161239198161 1674943770768120929398621)
                    ·
                      refine ⟨628103914038045348524483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1674943770768120929398621 628103914038045348524483)
                      ·
                        rfl

theorem cell23_1223228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_1223228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223228 prefixEnd_1223228 := by exact prefixLift 1223228
  have htrace : WordTrace (prefixWord ++ tailWord_1223228) baseStart_1223228 baseEnd_1223228 := by
    simpa [prefixWord, tailWord_1223228, baseEnd_1223228] using wordTrace_append hprefix tailTrace_1223228
  have hstable : (prefixWord ++ tailWord_1223228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223228).length < 2 ^ (prefixWord ++ tailWord_1223228).sum := by decide
  have hdescent : baseEnd_1223228 < baseStart_1223228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223264 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1223264 : Nat := 118140960795 + 1223264 * 2 ^ 59
def prefixEnd_1223264 : Nat := 4983230072969 + 3 ^ 40 * 1223264 * 2
def baseEnd_1223264 : Nat := 628122399341607207674317

theorem tailTrace_1223264 : CollatzResearch.WordTrace tailWord_1223264 prefixEnd_1223264 628122399341607207674317 := by
  unfold tailWord_1223264
  simp only [CollatzResearch.WordTrace]
  refine ⟨22308051720165459851794423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29744068960220613135725897 22308051720165459851794423)
  ·
    refine ⟨33462077580248189777691635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22308051720165459851794423 33462077580248189777691635)
    ·
      refine ⟨50193116370372284666537453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33462077580248189777691635 50193116370372284666537453)
      ·
        refine ⟨18822418638889606749951545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50193116370372284666537453 18822418638889606749951545)
        ·
          refine ⟨14116813979167205062463659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18822418638889606749951545 14116813979167205062463659)
          ·
            refine ⟨21175220968750807593695489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14116813979167205062463659 21175220968750807593695489)
            ·
              refine ⟨15881415726563105695271617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21175220968750807593695489 15881415726563105695271617)
              ·
                refine ⟨11911061794922329271453713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15881415726563105695271617 11911061794922329271453713)
                ·
                  refine ⟨8933296346191746953590285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11911061794922329271453713 8933296346191746953590285)
                  ·
                    refine ⟨3349986129821905107596357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8933296346191746953590285 3349986129821905107596357)
                    ·
                      refine ⟨628122399341607207674317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3349986129821905107596357 628122399341607207674317)
                      ·
                        rfl

theorem cell23_1223264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1223264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223264 prefixEnd_1223264 := by exact prefixLift 1223264
  have htrace : WordTrace (prefixWord ++ tailWord_1223264) baseStart_1223264 baseEnd_1223264 := by
    simpa [prefixWord, tailWord_1223264, baseEnd_1223264] using wordTrace_append hprefix tailTrace_1223264
  have hstable : (prefixWord ++ tailWord_1223264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223264).length < 2 ^ (prefixWord ++ tailWord_1223264).sum := by decide
  have hdescent : baseEnd_1223264 < baseStart_1223264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223358 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_1223358 : Nat := 118140960795 + 1223358 * 2 ^ 59
def prefixEnd_1223358 : Nat := 4983230072969 + 3 ^ 40 * 1223358 * 2
def baseEnd_1223358 : Nat := 628170666523129839898885

theorem tailTrace_1223358 : CollatzResearch.WordTrace tailWord_1223358 prefixEnd_1223358 628170666523129839898885 := by
  unfold tailWord_1223358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577441487748796719688841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29746354601326915838340485 5577441487748796719688841)
  ·
    refine ⟨4183081115811597539766631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5577441487748796719688841 4183081115811597539766631)
    ·
      refine ⟨6274621673717396309649947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183081115811597539766631 6274621673717396309649947)
      ·
        refine ⟨9411932510576094464474921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274621673717396309649947 9411932510576094464474921)
        ·
          refine ⟨7058949382932070848356191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9411932510576094464474921 7058949382932070848356191)
          ·
            refine ⟨10588424074398106272534287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058949382932070848356191 10588424074398106272534287)
            ·
              refine ⟨15882636111597159408801431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588424074398106272534287 15882636111597159408801431)
              ·
                refine ⟨23823954167395739113202147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15882636111597159408801431 23823954167395739113202147)
                ·
                  refine ⟨35735931251093608669803221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23823954167395739113202147 35735931251093608669803221)
                  ·
                    refine ⟨837560888697506453198513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35735931251093608669803221 837560888697506453198513)
                    ·
                      refine ⟨628170666523129839898885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837560888697506453198513 628170666523129839898885)
                      ·
                        rfl

theorem cell23_1223358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_1223358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223358 prefixEnd_1223358 := by exact prefixLift 1223358
  have htrace : WordTrace (prefixWord ++ tailWord_1223358) baseStart_1223358 baseEnd_1223358 := by
    simpa [prefixWord, tailWord_1223358, baseEnd_1223358] using wordTrace_append hprefix tailTrace_1223358
  have hstable : (prefixWord ++ tailWord_1223358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223358).length < 2 ^ (prefixWord ++ tailWord_1223358).sum := by decide
  have hdescent : baseEnd_1223358 < baseStart_1223358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223441 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_1223441 : Nat := 118140960795 + 1223441 * 2 ^ 59
def prefixEnd_1223441 : Nat := 4983230072969 + 3 ^ 40 * 1223441 * 2
def baseEnd_1223441 : Nat := 209404428472484338387001

theorem tailTrace_1223441 : CollatzResearch.WordTrace tailWord_1223441 prefixEnd_1223441 209404428472484338387001 := by
  unfold tailWord_1223441
  simp only [CollatzResearch.WordTrace]
  refine ⟨44622559160689678932782177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29748372773793119288521451 44622559160689678932782177)
  ·
    refine ⟨33466919370517259199586633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44622559160689678932782177 33466919370517259199586633)
    ·
      refine ⟨25100189527887944399689975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33466919370517259199586633 25100189527887944399689975)
      ·
        refine ⟨37650284291831916599534963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25100189527887944399689975 37650284291831916599534963)
        ·
          refine ⟨56475426437747874899302445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37650284291831916599534963 56475426437747874899302445)
          ·
            refine ⟨21178284914155453087238417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56475426437747874899302445 21178284914155453087238417)
            ·
              refine ⟨15883713685616589815428813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21178284914155453087238417 15883713685616589815428813)
              ·
                refine ⟨5956392632106221180785805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15883713685616589815428813 5956392632106221180785805)
                ·
                  refine ⟨2233647237039832942794677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5956392632106221180785805 2233647237039832942794677)
                  ·
                    refine ⟨209404428472484338387001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2233647237039832942794677 209404428472484338387001)
                    ·
                      rfl

theorem cell23_1223441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_1223441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223441 prefixEnd_1223441 := by exact prefixLift 1223441
  have htrace : WordTrace (prefixWord ++ tailWord_1223441) baseStart_1223441 baseEnd_1223441 := by
    simpa [prefixWord, tailWord_1223441, baseEnd_1223441] using wordTrace_append hprefix tailTrace_1223441
  have hstable : (prefixWord ++ tailWord_1223441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223441).length < 2 ^ (prefixWord ++ tailWord_1223441).sum := by decide
  have hdescent : baseEnd_1223441 < baseStart_1223441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223466 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1223466 : Nat := 118140960795 + 1223466 * 2 ^ 59
def prefixEnd_1223466 : Nat := 4983230072969 + 3 ^ 40 * 1223466 * 2
def baseEnd_1223466 : Nat := 209408707477938472449463

theorem tailTrace_1223466 : CollatzResearch.WordTrace tailWord_1223466 prefixEnd_1223466 209408707477938472449463 := by
  unfold tailWord_1223466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155867746399777050610563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29748980657066072134961501 11155867746399777050610563)
  ·
    refine ⟨16733801619599665575915845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11155867746399777050610563 16733801619599665575915845)
    ·
      refine ⟨3137587803674937295484221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16733801619599665575915845 3137587803674937295484221)
      ·
        refine ⟨1176595426378101485806583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3137587803674937295484221 1176595426378101485806583)
        ·
          refine ⟨1764893139567152228709875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176595426378101485806583 1764893139567152228709875)
          ·
            refine ⟨2647339709350728343064813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764893139567152228709875 2647339709350728343064813)
            ·
              refine ⟨992752391006523128649305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2647339709350728343064813 992752391006523128649305)
              ·
                refine ⟨744564293254892346486979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992752391006523128649305 744564293254892346486979)
                ·
                  refine ⟨1116846439882338519730469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744564293254892346486979 1116846439882338519730469)
                  ·
                    refine ⟨209408707477938472449463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116846439882338519730469 209408707477938472449463)
                    ·
                      rfl

theorem cell23_1223466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1223466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223466 prefixEnd_1223466 := by exact prefixLift 1223466
  have htrace : WordTrace (prefixWord ++ tailWord_1223466) baseStart_1223466 baseEnd_1223466 := by
    simpa [prefixWord, tailWord_1223466, baseEnd_1223466] using wordTrace_append hprefix tailTrace_1223466
  have hstable : (prefixWord ++ tailWord_1223466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223466).length < 2 ^ (prefixWord ++ tailWord_1223466).sum := by decide
  have hdescent : baseEnd_1223466 < baseStart_1223466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223491 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1223491 : Nat := 118140960795 + 1223491 * 2 ^ 59
def prefixEnd_1223491 : Nat := 4983230072969 + 3 ^ 40 * 1223491 * 2
def baseEnd_1223491 : Nat := 628238959450177819535773

theorem tailTrace_1223491 : CollatzResearch.WordTrace tailWord_1223491 prefixEnd_1223491 628238959450177819535773 := by
  unfold tailWord_1223491
  simp only [CollatzResearch.WordTrace]
  refine ⟨44624382810508537472102327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29749588540339024981401551 44624382810508537472102327)
  ·
    refine ⟨66936574215762806208153491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44624382810508537472102327 66936574215762806208153491)
    ·
      refine ⟨100404861323644209312230237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66936574215762806208153491 100404861323644209312230237)
      ·
        refine ⟨37651822996366578492086339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100404861323644209312230237 37651822996366578492086339)
        ·
          refine ⟨56477734494549867738129509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37651822996366578492086339 56477734494549867738129509)
          ·
            refine ⟨10589575217728100200899283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56477734494549867738129509 10589575217728100200899283)
            ·
              refine ⟨15884362826592150301348925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10589575217728100200899283 15884362826592150301348925)
              ·
                refine ⟨5956636059972056363005847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15884362826592150301348925 5956636059972056363005847)
                ·
                  refine ⟨8934954089958084544508771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5956636059972056363005847 8934954089958084544508771)
                  ·
                    refine ⟨13402431134937126816763157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8934954089958084544508771 13402431134937126816763157)
                    ·
                      refine ⟨628238959450177819535773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13402431134937126816763157 628238959450177819535773)
                      ·
                        rfl

theorem cell23_1223491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1223491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223491 prefixEnd_1223491 := by exact prefixLift 1223491
  have htrace : WordTrace (prefixWord ++ tailWord_1223491) baseStart_1223491 baseEnd_1223491 := by
    simpa [prefixWord, tailWord_1223491, baseEnd_1223491] using wordTrace_append hprefix tailTrace_1223491
  have hstable : (prefixWord ++ tailWord_1223491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223491).length < 2 ^ (prefixWord ++ tailWord_1223491).sum := by decide
  have hdescent : baseEnd_1223491 < baseStart_1223491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223492 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1223492 : Nat := 118140960795 + 1223492 * 2 ^ 59
def prefixEnd_1223492 : Nat := 4983230072969 + 3 ^ 40 * 1223492 * 2
def baseEnd_1223492 : Nat := 209413157643610771874423

theorem tailTrace_1223492 : CollatzResearch.WordTrace tailWord_1223492 prefixEnd_1223492 209413157643610771874423 := by
  unfold tailWord_1223492
  simp only [CollatzResearch.WordTrace]
  refine ⟨22312209641752457321444365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29749612855669943095259153 22312209641752457321444365)
  ·
    refine ⟨8367078615657171495541637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22312209641752457321444365 8367078615657171495541637)
    ·
      refine ⟨1568827240435719655414057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8367078615657171495541637 1568827240435719655414057)
      ·
        refine ⟨1176620430326789741560543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568827240435719655414057 1176620430326789741560543)
        ·
          refine ⟨1764930645490184612340815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176620430326789741560543 1764930645490184612340815)
          ·
            refine ⟨2647395968235276918511223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764930645490184612340815 2647395968235276918511223)
            ·
              refine ⟨3971093952352915377766835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647395968235276918511223 3971093952352915377766835)
              ·
                refine ⟨5956640928529373066650253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971093952352915377766835 5956640928529373066650253)
                ·
                  refine ⟨2233740348198514899993845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5956640928529373066650253 2233740348198514899993845)
                  ·
                    refine ⟨209413157643610771874423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2233740348198514899993845 209413157643610771874423)
                    ·
                      rfl

theorem cell23_1223492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1223492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223492 prefixEnd_1223492 := by exact prefixLift 1223492
  have htrace : WordTrace (prefixWord ++ tailWord_1223492) baseStart_1223492 baseEnd_1223492 := by
    simpa [prefixWord, tailWord_1223492, baseEnd_1223492] using wordTrace_append hprefix tailTrace_1223492
  have hstable : (prefixWord ++ tailWord_1223492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223492).length < 2 ^ (prefixWord ++ tailWord_1223492).sum := by decide
  have hdescent : baseEnd_1223492 < baseStart_1223492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223495 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_1223495 : Nat := 118140960795 + 1223495 * 2 ^ 59
def prefixEnd_1223495 : Nat := 4983230072969 + 3 ^ 40 * 1223495 * 2
def baseEnd_1223495 : Nat := 628241013372795803885755

theorem tailTrace_1223495 : CollatzResearch.WordTrace tailWord_1223495 prefixEnd_1223495 628241013372795803885755 := by
  unfold tailWord_1223495
  simp only [CollatzResearch.WordTrace]
  refine ⟨44624528702494046155247939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29749685801662697436831959 44624528702494046155247939)
  ·
    refine ⟨66936793053741069232871909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44624528702494046155247939 66936793053741069232871909)
    ·
      refine ⟨12550648697576450481163483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66936793053741069232871909 12550648697576450481163483)
      ·
        refine ⟨18825973046364675721745225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12550648697576450481163483 18825973046364675721745225)
        ·
          refine ⟨14119479784773506791308919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18825973046364675721745225 14119479784773506791308919)
          ·
            refine ⟨21179219677160260186963379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14119479784773506791308919 21179219677160260186963379)
            ·
              refine ⟨31768829515740390280445069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21179219677160260186963379 31768829515740390280445069)
              ·
                refine ⟨11913311068402646355166901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31768829515740390280445069 11913311068402646355166901)
                ·
                  refine ⟨1116872912662748095796897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11913311068402646355166901 1116872912662748095796897)
                  ·
                    refine ⟨837654684497061071847673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1116872912662748095796897 837654684497061071847673)
                    ·
                      refine ⟨628241013372795803885755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837654684497061071847673 628241013372795803885755)
                      ·
                        rfl

theorem cell23_1223495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_1223495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223495 prefixEnd_1223495 := by exact prefixLift 1223495
  have htrace : WordTrace (prefixWord ++ tailWord_1223495) baseStart_1223495 baseEnd_1223495 := by
    simpa [prefixWord, tailWord_1223495, baseEnd_1223495] using wordTrace_append hprefix tailTrace_1223495
  have hstable : (prefixWord ++ tailWord_1223495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223495).length < 2 ^ (prefixWord ++ tailWord_1223495).sum := by decide
  have hdescent : baseEnd_1223495 < baseStart_1223495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223521 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1223521 : Nat := 118140960795 + 1223521 * 2 ^ 59
def prefixEnd_1223521 : Nat := 4983230072969 + 3 ^ 40 * 1223521 * 2
def baseEnd_1223521 : Nat := 628254363869812702160635

theorem tailTrace_1223521 : CollatzResearch.WordTrace tailWord_1223521 prefixEnd_1223521 628254363869812702160635 := by
  unfold tailWord_1223521
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625477000399852595694417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29750318000266568397129611 44625477000399852595694417)
  ·
    refine ⟨33469107750299889446770813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44625477000399852595694417 33469107750299889446770813)
    ·
      refine ⟨12550915406362458542539055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33469107750299889446770813 12550915406362458542539055)
      ·
        refine ⟨18826373109543687813808583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12550915406362458542539055 18826373109543687813808583)
        ·
          refine ⟨28239559664315531720712875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18826373109543687813808583 28239559664315531720712875)
          ·
            refine ⟨42359339496473297581069313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28239559664315531720712875 42359339496473297581069313)
            ·
              refine ⟨31769504622354973185801985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42359339496473297581069313 31769504622354973185801985)
              ·
                refine ⟨23827128466766229889351489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31769504622354973185801985 23827128466766229889351489)
                ·
                  refine ⟨17870346350074672417013617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23827128466766229889351489 17870346350074672417013617)
                  ·
                    refine ⟨13402759762556004312760213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17870346350074672417013617 13402759762556004312760213)
                    ·
                      refine ⟨628254363869812702160635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13402759762556004312760213 628254363869812702160635)
                      ·
                        rfl

theorem cell23_1223521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1223521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223521 prefixEnd_1223521 := by exact prefixLift 1223521
  have htrace : WordTrace (prefixWord ++ tailWord_1223521) baseStart_1223521 baseEnd_1223521 := by
    simpa [prefixWord, tailWord_1223521, baseEnd_1223521] using wordTrace_append hprefix tailTrace_1223521
  have hstable : (prefixWord ++ tailWord_1223521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223521).length < 2 ^ (prefixWord ++ tailWord_1223521).sum := by decide
  have hdescent : baseEnd_1223521 < baseStart_1223521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223531 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 7]
def baseStart_1223531 : Nat := 118140960795 + 1223531 * 2 ^ 59
def prefixEnd_1223531 : Nat := 4983230072969 + 3 ^ 40 * 1223531 * 2
def baseEnd_1223531 : Nat := 209419832892119221011863

theorem tailTrace_1223531 : CollatzResearch.WordTrace tailWord_1223531 prefixEnd_1223531 209419832892119221011863 := by
  unfold tailWord_1223531
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625841730363624303558447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29750561153575749535705631 44625841730363624303558447)
  ·
    refine ⟨66938762595545436455337671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44625841730363624303558447 66938762595545436455337671)
    ·
      refine ⟨100408143893318154683006507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66938762595545436455337671 100408143893318154683006507)
      ·
        refine ⟨150612215839977232024509761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100408143893318154683006507 150612215839977232024509761)
        ·
          refine ⟨112959161879982924018382321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150612215839977232024509761 112959161879982924018382321)
          ·
            refine ⟨84719371409987193013786741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112959161879982924018382321 84719371409987193013786741)
            ·
              refine ⟨7942441069686299345042507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84719371409987193013786741 7942441069686299345042507)
              ·
                refine ⟨11913661604529449017563761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7942441069686299345042507 11913661604529449017563761)
                ·
                  refine ⟨8935246203397086763172821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11913661604529449017563761 8935246203397086763172821)
                  ·
                    refine ⟨209419832892119221011863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8935246203397086763172821 209419832892119221011863)
                    ·
                      rfl

theorem cell23_1223531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_1223531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223531 prefixEnd_1223531 := by exact prefixLift 1223531
  have htrace : WordTrace (prefixWord ++ tailWord_1223531) baseStart_1223531 baseEnd_1223531 := by
    simpa [prefixWord, tailWord_1223531, baseEnd_1223531] using wordTrace_append hprefix tailTrace_1223531
  have hstable : (prefixWord ++ tailWord_1223531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223531).length < 2 ^ (prefixWord ++ tailWord_1223531).sum := by decide
  have hdescent : baseEnd_1223531 < baseStart_1223531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223542 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1223542 : Nat := 118140960795 + 1223542 * 2 ^ 59
def prefixEnd_1223542 : Nat := 4983230072969 + 3 ^ 40 * 1223542 * 2
def baseEnd_1223542 : Nat := 628265146963557119998039

theorem tailTrace_1223542 : CollatzResearch.WordTrace tailWord_1223542 prefixEnd_1223542 628265146963557119998039 := by
  unfold tailWord_1223542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789140183332735823888055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29750828622215848788139253 2789140183332735823888055)
  ·
    refine ⟨4183710274999103735832083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2789140183332735823888055 4183710274999103735832083)
    ·
      refine ⟨6275565412498655603748125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183710274999103735832083 6275565412498655603748125)
      ·
        refine ⟨2353337029686995851405547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6275565412498655603748125 2353337029686995851405547)
        ·
          refine ⟨3530005544530493777108321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353337029686995851405547 3530005544530493777108321)
          ·
            refine ⟨2647504158397870332831241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530005544530493777108321 2647504158397870332831241)
            ·
              refine ⟨1985628118798402749623431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2647504158397870332831241 1985628118798402749623431)
              ·
                refine ⟨2978442178197604124435147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985628118798402749623431 2978442178197604124435147)
                ·
                  refine ⟨4467663267296406186652721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978442178197604124435147 4467663267296406186652721)
                  ·
                    refine ⟨3350747450472304639989541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4467663267296406186652721 3350747450472304639989541)
                    ·
                      refine ⟨628265146963557119998039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3350747450472304639989541 628265146963557119998039)
                      ·
                        rfl

theorem cell23_1223542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1223542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223542 prefixEnd_1223542 := by exact prefixLift 1223542
  have htrace : WordTrace (prefixWord ++ tailWord_1223542) baseStart_1223542 baseEnd_1223542 := by
    simpa [prefixWord, tailWord_1223542, baseEnd_1223542] using wordTrace_append hprefix tailTrace_1223542
  have hstable : (prefixWord ++ tailWord_1223542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223542).length < 2 ^ (prefixWord ++ tailWord_1223542).sum := by decide
  have hdescent : baseEnd_1223542 < baseStart_1223542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223545 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1223545 : Nat := 118140960795 + 1223545 * 2 ^ 59
def prefixEnd_1223545 : Nat := 4983230072969 + 3 ^ 40 * 1223545 * 2
def baseEnd_1223545 : Nat := 628266687405520608260525

theorem tailTrace_1223545 : CollatzResearch.WordTrace tailWord_1223545 prefixEnd_1223545 628266687405520608260525 := by
  unfold tailWord_1223545
  simp only [CollatzResearch.WordTrace]
  refine ⟨44626352352312904694568089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29750901568208603129712059 44626352352312904694568089)
  ·
    refine ⟨33469764264234678520926067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44626352352312904694568089 33469764264234678520926067)
    ·
      refine ⟨50204646396352017781389101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33469764264234678520926067 50204646396352017781389101)
      ·
        refine ⟨18826742398632006668020913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50204646396352017781389101 18826742398632006668020913)
        ·
          refine ⟨14120056798974005001015685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18826742398632006668020913 14120056798974005001015685)
          ·
            refine ⟨2647510649807625937690441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14120056798974005001015685 2647510649807625937690441)
            ·
              refine ⟨1985632987355719453267831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2647510649807625937690441 1985632987355719453267831)
              ·
                refine ⟨2978449481033579179901747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985632987355719453267831 2978449481033579179901747)
                ·
                  refine ⟨4467674221550368769852621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978449481033579179901747 4467674221550368769852621)
                  ·
                    refine ⟨1675377833081388288694733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4467674221550368769852621 1675377833081388288694733)
                    ·
                      refine ⟨628266687405520608260525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1675377833081388288694733 628266687405520608260525)
                      ·
                        rfl

theorem cell23_1223545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1223545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223545 prefixEnd_1223545 := by exact prefixLift 1223545
  have htrace : WordTrace (prefixWord ++ tailWord_1223545) baseStart_1223545 baseEnd_1223545 := by
    simpa [prefixWord, tailWord_1223545, baseEnd_1223545] using wordTrace_append hprefix tailTrace_1223545
  have hstable : (prefixWord ++ tailWord_1223545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223545).length < 2 ^ (prefixWord ++ tailWord_1223545).sum := by decide
  have hdescent : baseEnd_1223545 < baseStart_1223545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223555 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 3, 3, 2]
def baseStart_1223555 : Nat := 118140960795 + 1223555 * 2 ^ 59
def prefixEnd_1223555 : Nat := 4983230072969 + 3 ^ 40 * 1223555 * 2
def baseEnd_1223555 : Nat := 628271822212065569135479

theorem tailTrace_1223555 : CollatzResearch.WordTrace tailWord_1223555 prefixEnd_1223555 628271822212065569135479 := by
  unfold tailWord_1223555
  simp only [CollatzResearch.WordTrace]
  refine ⟨44626717082276676402432119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29751144721517784268288079 44626717082276676402432119)
  ·
    refine ⟨66940075623415014603648179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44626717082276676402432119 66940075623415014603648179)
    ·
      refine ⟨100410113435122521905472269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66940075623415014603648179 100410113435122521905472269)
      ·
        refine ⟨37653792538170945714552101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100410113435122521905472269 37653792538170945714552101)
        ·
          refine ⟨7060086100907052321478519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37653792538170945714552101 7060086100907052321478519)
          ·
            refine ⟨10590129151360578482217779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7060086100907052321478519 10590129151360578482217779)
            ·
              refine ⟨15885193727040867723326669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10590129151360578482217779 15885193727040867723326669)
              ·
                refine ⟨5956947647640325396247501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15885193727040867723326669 5956947647640325396247501)
                ·
                  refine ⟨2233855367865122023592813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5956947647640325396247501 2233855367865122023592813)
                  ·
                    refine ⟨837695762949420758847305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233855367865122023592813 837695762949420758847305)
                    ·
                      refine ⟨628271822212065569135479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837695762949420758847305 628271822212065569135479)
                      ·
                        rfl

theorem cell23_1223555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_1223555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223555 prefixEnd_1223555 := by exact prefixLift 1223555
  have htrace : WordTrace (prefixWord ++ tailWord_1223555) baseStart_1223555 baseEnd_1223555 := by
    simpa [prefixWord, tailWord_1223555, baseEnd_1223555] using wordTrace_append hprefix tailTrace_1223555
  have hstable : (prefixWord ++ tailWord_1223555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223555).length < 2 ^ (prefixWord ++ tailWord_1223555).sum := by decide
  have hdescent : baseEnd_1223555 < baseStart_1223555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223608 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 7]
def baseStart_1223608 : Nat := 118140960795 + 1223608 * 2 ^ 59
def prefixEnd_1223608 : Nat := 4983230072969 + 3 ^ 40 * 1223608 * 2
def baseEnd_1223608 : Nat := 69811004076305984641415

theorem tailTrace_1223608 : CollatzResearch.WordTrace tailWord_1223608 prefixEnd_1223608 69811004076305984641415 := by
  unfold tailWord_1223608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314325075542333227055739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29752433434056444302740985 22314325075542333227055739)
  ·
    refine ⟨33471487613313499840583609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22314325075542333227055739 33471487613313499840583609)
    ·
      refine ⟨25103615709985124880437707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33471487613313499840583609 25103615709985124880437707)
      ·
        refine ⟨37655423564977687320656561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25103615709985124880437707 37655423564977687320656561)
        ·
          refine ⟨28241567673733265490492421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37655423564977687320656561 28241567673733265490492421)
          ·
            refine ⟨5295293938824987279467329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28241567673733265490492421 5295293938824987279467329)
            ·
              refine ⟨3971470454118740459600497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295293938824987279467329 3971470454118740459600497)
              ·
                refine ⟨2978602840589055344700373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971470454118740459600497 2978602840589055344700373)
                ·
                  refine ⟨69811004076305984641415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2978602840589055344700373 69811004076305984641415)
                  ·
                    rfl

theorem cell23_1223608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_1223608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223608 prefixEnd_1223608 := by exact prefixLift 1223608
  have htrace : WordTrace (prefixWord ++ tailWord_1223608) baseStart_1223608 baseEnd_1223608 := by
    simpa [prefixWord, tailWord_1223608, baseEnd_1223608] using wordTrace_append hprefix tailTrace_1223608
  have hstable : (prefixWord ++ tailWord_1223608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223608).length < 2 ^ (prefixWord ++ tailWord_1223608).sum := by decide
  have hdescent : baseEnd_1223608 < baseStart_1223608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223675 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 4, 4, 2]
def baseStart_1223675 : Nat := 118140960795 + 1223675 * 2 ^ 59
def prefixEnd_1223675 : Nat := 4983230072969 + 3 ^ 40 * 1223675 * 2
def baseEnd_1223675 : Nat := 628333439890605099634927

theorem tailTrace_1223675 : CollatzResearch.WordTrace tailWord_1223675 prefixEnd_1223675 628333439890605099634927 := by
  unfold tailWord_1223675
  simp only [CollatzResearch.WordTrace]
  refine ⟨44631093841841936896800479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29754062561227957931200319 44631093841841936896800479)
  ·
    refine ⟨66946640762762905345200719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44631093841841936896800479 66946640762762905345200719)
    ·
      refine ⟨100419961144144358017801079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66946640762762905345200719 100419961144144358017801079)
      ·
        refine ⟨150629941716216537026701619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100419961144144358017801079 150629941716216537026701619)
        ·
          refine ⟨225944912574324805540052429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150629941716216537026701619 225944912574324805540052429)
          ·
            refine ⟨84729342215371802077519661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225944912574324805540052429 84729342215371802077519661)
            ·
              refine ⟨31773503330764425779069873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84729342215371802077519661 31773503330764425779069873)
              ·
                refine ⟨23830127498073319334302405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31773503330764425779069873 23830127498073319334302405)
                ·
                  refine ⟨4468148905888747375181701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23830127498073319334302405 4468148905888747375181701)
                  ·
                    refine ⟨837777919854140132846569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468148905888747375181701 837777919854140132846569)
                    ·
                      refine ⟨628333439890605099634927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837777919854140132846569 628333439890605099634927)
                      ·
                        rfl

theorem cell23_1223675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4, 2].length) (baseStart_1223675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223675 prefixEnd_1223675 := by exact prefixLift 1223675
  have htrace : WordTrace (prefixWord ++ tailWord_1223675) baseStart_1223675 baseEnd_1223675 := by
    simpa [prefixWord, tailWord_1223675, baseEnd_1223675] using wordTrace_append hprefix tailTrace_1223675
  have hstable : (prefixWord ++ tailWord_1223675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223675).length < 2 ^ (prefixWord ++ tailWord_1223675).sum := by decide
  have hdescent : baseEnd_1223675 < baseStart_1223675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223709 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1223709 : Nat := 118140960795 + 1223709 * 2 ^ 59
def prefixEnd_1223709 : Nat := 4983230072969 + 3 ^ 40 * 1223709 * 2
def baseEnd_1223709 : Nat := 628350898232857966609771

theorem tailTrace_1223709 : CollatzResearch.WordTrace tailWord_1223709 prefixEnd_1223709 628350898232857966609771 := by
  unfold tailWord_1223709
  simp only [CollatzResearch.WordTrace]
  refine ⟨44632333923718760703538181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29754889282479173802358787 44632333923718760703538181)
  ·
    refine ⟨8368562610697267631913409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44632333923718760703538181 8368562610697267631913409)
    ·
      refine ⟨6276421958022950723935057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8368562610697267631913409 6276421958022950723935057)
      ·
        refine ⟨4707316468517213042951293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6276421958022950723935057 4707316468517213042951293)
        ·
          refine ⟨1765243675693954891106735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4707316468517213042951293 1765243675693954891106735)
          ·
            refine ⟨2647865513540932336660103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765243675693954891106735 2647865513540932336660103)
            ·
              refine ⟨3971798270311398504990155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647865513540932336660103 3971798270311398504990155)
              ·
                refine ⟨5957697405467097757485233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971798270311398504990155 5957697405467097757485233)
                ·
                  refine ⟨4468273054100323318113925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5957697405467097757485233 4468273054100323318113925)
                  ·
                    refine ⟨837801197643810622146361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468273054100323318113925 837801197643810622146361)
                    ·
                      refine ⟨628350898232857966609771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837801197643810622146361 628350898232857966609771)
                      ·
                        rfl

theorem cell23_1223709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1223709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223709 prefixEnd_1223709 := by exact prefixLift 1223709
  have htrace : WordTrace (prefixWord ++ tailWord_1223709) baseStart_1223709 baseEnd_1223709 := by
    simpa [prefixWord, tailWord_1223709, baseEnd_1223709] using wordTrace_append hprefix tailTrace_1223709
  have hstable : (prefixWord ++ tailWord_1223709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223709).length < 2 ^ (prefixWord ++ tailWord_1223709).sum := by decide
  have hdescent : baseEnd_1223709 < baseStart_1223709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223715 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 6]
def baseStart_1223715 : Nat := 118140960795 + 1223715 * 2 ^ 59
def prefixEnd_1223715 : Nat := 4983230072969 + 3 ^ 40 * 1223715 * 2
def baseEnd_1223715 : Nat := 69817108790753882570527

theorem tailTrace_1223715 : CollatzResearch.WordTrace tailWord_1223715 prefixEnd_1223715 69817108790753882570527 := by
  unfold tailWord_1223715
  simp only [CollatzResearch.WordTrace]
  refine ⟨44632552761697023728256599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29755035174464682485504399 44632552761697023728256599)
  ·
    refine ⟨66948829142545535592384899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44632552761697023728256599 66948829142545535592384899)
    ·
      refine ⟨100423243713818303388577349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66948829142545535592384899 100423243713818303388577349)
      ·
        refine ⟨18829358196340931885358253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100423243713818303388577349 18829358196340931885358253)
        ·
          refine ⟨7061009323627849457009345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18829358196340931885358253 7061009323627849457009345)
          ·
            refine ⟨5295756992720887092757009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7061009323627849457009345 5295756992720887092757009)
            ·
              refine ⟨3971817744540665319567757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295756992720887092757009 3971817744540665319567757)
              ·
                refine ⟨1489431654202749494837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3971817744540665319567757 1489431654202749494837909)
                ·
                  refine ⟨69817108790753882570527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1489431654202749494837909 69817108790753882570527)
                  ·
                    rfl

theorem cell23_1223715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 6].length) (baseStart_1223715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223715 prefixEnd_1223715 := by exact prefixLift 1223715
  have htrace : WordTrace (prefixWord ++ tailWord_1223715) baseStart_1223715 baseEnd_1223715 := by
    simpa [prefixWord, tailWord_1223715, baseEnd_1223715] using wordTrace_append hprefix tailTrace_1223715
  have hstable : (prefixWord ++ tailWord_1223715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223715).length < 2 ^ (prefixWord ++ tailWord_1223715).sum := by decide
  have hdescent : baseEnd_1223715 < baseStart_1223715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223719 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1223719 : Nat := 118140960795 + 1223719 * 2 ^ 59
def prefixEnd_1223719 : Nat := 4983230072969 + 3 ^ 40 * 1223719 * 2
def baseEnd_1223719 : Nat := 209452011013134309161575

theorem tailTrace_1223719 : CollatzResearch.WordTrace tailWord_1223719 prefixEnd_1223719 209452011013134309161575 := by
  unfold tailWord_1223719
  simp only [CollatzResearch.WordTrace]
  refine ⟨44632698653682532411402211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29755132435788354940934807 44632698653682532411402211)
  ·
    refine ⟨66949047980523798617103317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44632698653682532411402211 66949047980523798617103317)
    ·
      refine ⟨1569118312043526530088359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66949047980523798617103317 1569118312043526530088359)
      ·
        refine ⟨2353677468065289795132539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569118312043526530088359 2353677468065289795132539)
        ·
          refine ⟨3530516202097934692698809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353677468065289795132539 3530516202097934692698809)
          ·
            refine ⟨2647887151573451019524107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530516202097934692698809 2647887151573451019524107)
            ·
              refine ⟨3971830727360176529286161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647887151573451019524107 3971830727360176529286161)
              ·
                refine ⟨2978873045520132396964621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971830727360176529286161 2978873045520132396964621)
                ·
                  refine ⟨1117077392070049648861733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2978873045520132396964621 1117077392070049648861733)
                  ·
                    refine ⟨209452011013134309161575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117077392070049648861733 209452011013134309161575)
                    ·
                      rfl

theorem cell23_1223719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1223719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223719 prefixEnd_1223719 := by exact prefixLift 1223719
  have htrace : WordTrace (prefixWord ++ tailWord_1223719) baseStart_1223719 baseEnd_1223719 := by
    simpa [prefixWord, tailWord_1223719, baseEnd_1223719] using wordTrace_append hprefix tailTrace_1223719
  have hstable : (prefixWord ++ tailWord_1223719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223719).length < 2 ^ (prefixWord ++ tailWord_1223719).sum := by decide
  have hdescent : baseEnd_1223719 < baseStart_1223719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223752 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_1223752 : Nat := 118140960795 + 1223752 * 2 ^ 59
def prefixEnd_1223752 : Nat := 4983230072969 + 3 ^ 40 * 1223752 * 2
def baseEnd_1223752 : Nat := 628372977901001298372073

theorem tailTrace_1223752 : CollatzResearch.WordTrace tailWord_1223752 prefixEnd_1223752 628372977901001298372073 := by
  unfold tailWord_1223752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316951131281489523676755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29755934841708652698235673 22316951131281489523676755)
  ·
    refine ⟨33475426696922234285515133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22316951131281489523676755 33475426696922234285515133)
    ·
      refine ⟨12553285011345837857068175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33475426696922234285515133 12553285011345837857068175)
      ·
        refine ⟨18829927517018756785602263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553285011345837857068175 18829927517018756785602263)
        ·
          refine ⟨28244891275528135178403395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18829927517018756785602263 28244891275528135178403395)
          ·
            refine ⟨42367336913292202767605093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28244891275528135178403395 42367336913292202767605093)
            ·
              refine ⟨7943875671242288018925955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42367336913292202767605093 7943875671242288018925955)
              ·
                refine ⟨11915813506863432028388933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7943875671242288018925955 11915813506863432028388933)
                ·
                  refine ⟨2234215032536893505322925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11915813506863432028388933 2234215032536893505322925)
                  ·
                    refine ⟨837830637201335064496097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234215032536893505322925 837830637201335064496097)
                    ·
                      refine ⟨628372977901001298372073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837830637201335064496097 628372977901001298372073)
                      ·
                        rfl

theorem cell23_1223752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_1223752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223752 prefixEnd_1223752 := by exact prefixLift 1223752
  have htrace : WordTrace (prefixWord ++ tailWord_1223752) baseStart_1223752 baseEnd_1223752 := by
    simpa [prefixWord, tailWord_1223752, baseEnd_1223752] using wordTrace_append hprefix tailTrace_1223752
  have hstable : (prefixWord ++ tailWord_1223752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223752).length < 2 ^ (prefixWord ++ tailWord_1223752).sum := by decide
  have hdescent : baseEnd_1223752 < baseStart_1223752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223822 : List Nat := [4, 1, 1, 3, 2, 2, 2, 8]
def baseStart_1223822 : Nat := 118140960795 + 1223822 * 2 ^ 59
def prefixEnd_1223822 : Nat := 4983230072969 + 3 ^ 40 * 1223822 * 2
def baseEnd_1223822 : Nat := 23274404501733926833213

theorem tailTrace_1223822 : CollatzResearch.WordTrace tailWord_1223822 prefixEnd_1223822 23274404501733926833213 := by
  unfold tailWord_1223822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5579556921538672625300215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29757636914872920668267813 5579556921538672625300215)
  ·
    refine ⟨8369335382308008937950323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5579556921538672625300215 8369335382308008937950323)
    ·
      refine ⟨12554003073462013406925485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8369335382308008937950323 12554003073462013406925485)
      ·
        refine ⟨4707751152548255027597057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12554003073462013406925485 4707751152548255027597057)
        ·
          refine ⟨3530813364411191270697793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4707751152548255027597057 3530813364411191270697793)
          ·
            refine ⟨2648110023308393453023345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530813364411191270697793 2648110023308393453023345)
            ·
              refine ⟨1986082517481295089767509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648110023308393453023345 1986082517481295089767509)
              ·
                refine ⟨23274404501733926833213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1986082517481295089767509 23274404501733926833213)
                ·
                  rfl

theorem cell23_1223822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_1223822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223822 prefixEnd_1223822 := by exact prefixLift 1223822
  have htrace : WordTrace (prefixWord ++ tailWord_1223822) baseStart_1223822 baseEnd_1223822 := by
    simpa [prefixWord, tailWord_1223822, baseEnd_1223822] using wordTrace_append hprefix tailTrace_1223822
  have hstable : (prefixWord ++ tailWord_1223822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223822).length < 2 ^ (prefixWord ++ tailWord_1223822).sum := by decide
  have hdescent : baseEnd_1223822 < baseStart_1223822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223826 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1223826 : Nat := 118140960795 + 1223826 * 2 ^ 59
def prefixEnd_1223826 : Nat := 4983230072969 + 3 ^ 40 * 1223826 * 2
def baseEnd_1223826 : Nat := 209470325156478002948911

theorem tailTrace_1223826 : CollatzResearch.WordTrace tailWord_1223826 prefixEnd_1223826 209470325156478002948911 := by
  unfold tailWord_1223826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159150316073722421386833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29757734176196593123698221 11159150316073722421386833)
  ·
    refine ⟨8369362737055291816040125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11159150316073722421386833 8369362737055291816040125)
    ·
      refine ⟨3138511026395734431015047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8369362737055291816040125 3138511026395734431015047)
      ·
        refine ⟨4707766539593601646522571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138511026395734431015047 4707766539593601646522571)
        ·
          refine ⟨7061649809390402469783857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4707766539593601646522571 7061649809390402469783857)
          ·
            refine ⟨5296237357042801852337893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7061649809390402469783857 5296237357042801852337893)
            ·
              refine ⟨993044504445525347313355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5296237357042801852337893 993044504445525347313355)
              ·
                refine ⟨1489566756668288020970033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993044504445525347313355 1489566756668288020970033)
                ·
                  refine ⟨1117175067501216015727525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1489566756668288020970033 1117175067501216015727525)
                  ·
                    refine ⟨209470325156478002948911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117175067501216015727525 209470325156478002948911)
                    ·
                      rfl

theorem cell23_1223826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1223826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223826 prefixEnd_1223826 := by exact prefixLift 1223826
  have htrace : WordTrace (prefixWord ++ tailWord_1223826) baseStart_1223826 baseEnd_1223826 := by
    simpa [prefixWord, tailWord_1223826, baseEnd_1223826] using wordTrace_append hprefix tailTrace_1223826
  have hstable : (prefixWord ++ tailWord_1223826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223826).length < 2 ^ (prefixWord ++ tailWord_1223826).sum := by decide
  have hdescent : baseEnd_1223826 < baseStart_1223826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223836 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1223836 : Nat := 118140960795 + 1223836 * 2 ^ 59
def prefixEnd_1223836 : Nat := 4983230072969 + 3 ^ 40 * 1223836 * 2
def baseEnd_1223836 : Nat := 628416110275978969721687

theorem tailTrace_1223836 : CollatzResearch.WordTrace tailWord_1223836 prefixEnd_1223836 628416110275978969721687 := by
  unfold tailWord_1223836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22318482997129330696705681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29757977329505774262274241 22318482997129330696705681)
  ·
    refine ⟨16738862247846998022529261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22318482997129330696705681 16738862247846998022529261)
    ·
      refine ⟨6277073342942624258448473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16738862247846998022529261 6277073342942624258448473)
      ·
        refine ⟨4707805007206968193836355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6277073342942624258448473 4707805007206968193836355)
        ·
          refine ⟨7061707510810452290754533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4707805007206968193836355 7061707510810452290754533)
          ·
            refine ⟨1324070158276959804516475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7061707510810452290754533 1324070158276959804516475)
            ·
              refine ⟨1986105237415439706774713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324070158276959804516475 1986105237415439706774713)
              ·
                refine ⟨1489578928061579780081035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986105237415439706774713 1489578928061579780081035)
                ·
                  refine ⟨2234368392092369670121553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489578928061579780081035 2234368392092369670121553)
                  ·
                    refine ⟨1675776294069277252591165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2234368392092369670121553 1675776294069277252591165)
                    ·
                      refine ⟨628416110275978969721687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1675776294069277252591165 628416110275978969721687)
                      ·
                        rfl

theorem cell23_1223836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1223836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223836 prefixEnd_1223836 := by exact prefixLift 1223836
  have htrace : WordTrace (prefixWord ++ tailWord_1223836) baseStart_1223836 baseEnd_1223836 := by
    simpa [prefixWord, tailWord_1223836, baseEnd_1223836] using wordTrace_append hprefix tailTrace_1223836
  have hstable : (prefixWord ++ tailWord_1223836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223836).length < 2 ^ (prefixWord ++ tailWord_1223836).sum := by decide
  have hdescent : baseEnd_1223836 < baseStart_1223836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223853 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1223853 : Nat := 118140960795 + 1223853 * 2 ^ 59
def prefixEnd_1223853 : Nat := 4983230072969 + 3 ^ 40 * 1223853 * 2
def baseEnd_1223853 : Nat := 628424839447105403209109

theorem tailTrace_1223853 : CollatzResearch.WordTrace tailWord_1223853 prefixEnd_1223853 628424839447105403209109 := by
  unfold tailWord_1223853
  simp only [CollatzResearch.WordTrace]
  refine ⟨44637586035197073296780213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29758390690131382197853475 44637586035197073296780213)
  ·
    refine ⟨4184773690799725621573145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44637586035197073296780213 4184773690799725621573145)
    ·
      refine ⟨3138580268099794216179859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4184773690799725621573145 3138580268099794216179859)
      ·
        refine ⟨4707870402149691324269789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138580268099794216179859 4707870402149691324269789)
        ·
          refine ⟨1765451400806134246601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4707870402149691324269789 1765451400806134246601171)
          ·
            refine ⟨2648177101209201369901757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765451400806134246601171 2648177101209201369901757)
            ·
              refine ⟨993066412953450513713159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648177101209201369901757 993066412953450513713159)
              ·
                refine ⟨1489599619430175770569739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993066412953450513713159 1489599619430175770569739)
                ·
                  refine ⟨2234399429145263655854609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489599619430175770569739 2234399429145263655854609)
                  ·
                    refine ⟨1675799571858947741890957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2234399429145263655854609 1675799571858947741890957)
                    ·
                      refine ⟨628424839447105403209109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1675799571858947741890957 628424839447105403209109)
                      ·
                        rfl

theorem cell23_1223853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1223853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223853 prefixEnd_1223853 := by exact prefixLift 1223853
  have htrace : WordTrace (prefixWord ++ tailWord_1223853) baseStart_1223853 baseEnd_1223853 := by
    simpa [prefixWord, tailWord_1223853, baseEnd_1223853] using wordTrace_append hprefix tailTrace_1223853
  have hstable : (prefixWord ++ tailWord_1223853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223853).length < 2 ^ (prefixWord ++ tailWord_1223853).sum := by decide
  have hdescent : baseEnd_1223853 < baseStart_1223853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223859 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 1, 3, 2]
def baseStart_1223859 : Nat := 118140960795 + 1223859 * 2 ^ 59
def prefixEnd_1223859 : Nat := 4983230072969 + 3 ^ 40 * 1223859 * 2
def baseEnd_1223859 : Nat := 628427920331032379734081

theorem tailTrace_1223859 : CollatzResearch.WordTrace tailWord_1223859 prefixEnd_1223859 628427920331032379734081 := by
  unfold tailWord_1223859
  simp only [CollatzResearch.WordTrace]
  refine ⟨44637804873175336321498631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29758536582116890880999087 44637804873175336321498631)
  ·
    refine ⟨66956707309763004482247947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44637804873175336321498631 66956707309763004482247947)
    ·
      refine ⟨100435060964644506723371921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66956707309763004482247947 100435060964644506723371921)
      ·
        refine ⟨75326295723483380042528941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100435060964644506723371921 75326295723483380042528941)
        ·
          refine ⟨28247360896306267515948353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75326295723483380042528941 28247360896306267515948353)
          ·
            refine ⟨21185520672229700636961265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28247360896306267515948353 21185520672229700636961265)
            ·
              refine ⟨15889140504172275477720949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21185520672229700636961265 15889140504172275477720949)
              ·
                refine ⟨1489606922266150826036339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15889140504172275477720949 1489606922266150826036339)
                ·
                  refine ⟨2234410383399226239054509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489606922266150826036339 2234410383399226239054509)
                  ·
                    refine ⟨837903893774709839645441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234410383399226239054509 837903893774709839645441)
                    ·
                      refine ⟨628427920331032379734081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837903893774709839645441 628427920331032379734081)
                      ·
                        rfl

theorem cell23_1223859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3, 2].length) (baseStart_1223859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223859 prefixEnd_1223859 := by exact prefixLift 1223859
  have htrace : WordTrace (prefixWord ++ tailWord_1223859) baseStart_1223859 baseEnd_1223859 := by
    simpa [prefixWord, tailWord_1223859, baseEnd_1223859] using wordTrace_append hprefix tailTrace_1223859
  have hstable : (prefixWord ++ tailWord_1223859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223859).length < 2 ^ (prefixWord ++ tailWord_1223859).sum := by decide
  have hdescent : baseEnd_1223859 < baseStart_1223859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_1223875 : Nat := 118140960795 + 1223875 * 2 ^ 59
def prefixEnd_1223875 : Nat := 4983230072969 + 3 ^ 40 * 1223875 * 2
def baseEnd_1223875 : Nat := 628436136021504317134007

theorem tailTrace_1223875 : CollatzResearch.WordTrace tailWord_1223875 prefixEnd_1223875 628436136021504317134007 := by
  unfold tailWord_1223875
  simp only [CollatzResearch.WordTrace]
  refine ⟨44638388441117371054081079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29758925627411580702720719 44638388441117371054081079)
  ·
    refine ⟨66957582661676056581121619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44638388441117371054081079 66957582661676056581121619)
    ·
      refine ⟨100436373992514084871682429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66957582661676056581121619 100436373992514084871682429)
      ·
        refine ⟨37663640247192781826880911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100436373992514084871682429 37663640247192781826880911)
        ·
          refine ⟨56495460370789172740321367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37663640247192781826880911 56495460370789172740321367)
          ·
            refine ⟨84743190556183759110482051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56495460370789172740321367 84743190556183759110482051)
            ·
              refine ⟨127114785834275638665723077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84743190556183759110482051 127114785834275638665723077)
              ·
                refine ⟨23834022343926682249823077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127114785834275638665723077 23834022343926682249823077)
                ·
                  refine ⟨4468879189486252921841827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23834022343926682249823077 4468879189486252921841827)
                  ·
                    refine ⟨6703318784229379382762741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468879189486252921841827 6703318784229379382762741)
                    ·
                      refine ⟨628436136021504317134007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6703318784229379382762741 628436136021504317134007)
                      ·
                        rfl

theorem cell23_1223875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_1223875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223875 prefixEnd_1223875 := by exact prefixLift 1223875
  have htrace : WordTrace (prefixWord ++ tailWord_1223875) baseStart_1223875 baseEnd_1223875 := by
    simpa [prefixWord, tailWord_1223875, baseEnd_1223875] using wordTrace_append hprefix tailTrace_1223875
  have hstable : (prefixWord ++ tailWord_1223875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223875).length < 2 ^ (prefixWord ++ tailWord_1223875).sum := by decide
  have hdescent : baseEnd_1223875 < baseStart_1223875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223882 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1223882 : Nat := 118140960795 + 1223882 * 2 ^ 59
def prefixEnd_1223882 : Nat := 4983230072969 + 3 ^ 40 * 1223882 * 2
def baseEnd_1223882 : Nat := 209479910128695263248825

theorem tailTrace_1223882 : CollatzResearch.WordTrace tailWord_1223882 prefixEnd_1223882 209479910128695263248825 := by
  unfold tailWord_1223882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159660938023002812396475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29759095834728007499723933 11159660938023002812396475)
  ·
    refine ⟨16739491407034504218594713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11159660938023002812396475 16739491407034504218594713)
    ·
      refine ⟨12554618555275878163946035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16739491407034504218594713 12554618555275878163946035)
      ·
        refine ⟨18831927832913817245919053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12554618555275878163946035 18831927832913817245919053)
        ·
          refine ⟨7061972937342681467219645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18831927832913817245919053 7061972937342681467219645)
          ·
            refine ⟨2648239851503505550207367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7061972937342681467219645 2648239851503505550207367)
            ·
              refine ⟨3972359777255258325311051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648239851503505550207367 3972359777255258325311051)
              ·
                refine ⟨5958539665882887487966577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972359777255258325311051 5958539665882887487966577)
                ·
                  refine ⟨4468904749412165615974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958539665882887487966577 4468904749412165615974933)
                  ·
                    refine ⟨209479910128695263248825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4468904749412165615974933 209479910128695263248825)
                    ·
                      rfl

theorem cell23_1223882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1223882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223882 prefixEnd_1223882 := by exact prefixLift 1223882
  have htrace : WordTrace (prefixWord ++ tailWord_1223882) baseStart_1223882 baseEnd_1223882 := by
    simpa [prefixWord, tailWord_1223882, baseEnd_1223882] using wordTrace_append hprefix tailTrace_1223882
  have hstable : (prefixWord ++ tailWord_1223882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223882).length < 2 ^ (prefixWord ++ tailWord_1223882).sum := by decide
  have hdescent : baseEnd_1223882 < baseStart_1223882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223889 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_1223889 : Nat := 118140960795 + 1223889 * 2 ^ 59
def prefixEnd_1223889 : Nat := 4983230072969 + 3 ^ 40 * 1223889 * 2
def baseEnd_1223889 : Nat := 628443324750667262358943

theorem tailTrace_1223889 : CollatzResearch.WordTrace tailWord_1223889 prefixEnd_1223889 628443324750667262358943 := by
  unfold tailWord_1223889
  simp only [CollatzResearch.WordTrace]
  refine ⟨44638899063066651445090721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29759266042044434296727147 44638899063066651445090721)
  ·
    refine ⟨33479174297299988583818041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44638899063066651445090721 33479174297299988583818041)
    ·
      refine ⟨25109380722974991437863531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33479174297299988583818041 25109380722974991437863531)
      ·
        refine ⟨37664071084462487156795297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25109380722974991437863531 37664071084462487156795297)
        ·
          refine ⟨28248053313346865367596473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37664071084462487156795297 28248053313346865367596473)
          ·
            refine ⟨21186039985010149025697355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28248053313346865367596473 21186039985010149025697355)
            ·
              refine ⟨31779059977515223538546033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186039985010149025697355 31779059977515223538546033)
              ·
                refine ⟨23834294983136417653909525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31779059977515223538546033 23834294983136417653909525)
                ·
                  refine ⟨1117232577334519577527009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23834294983136417653909525 1117232577334519577527009)
                  ·
                    refine ⟨837924433000889683145257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117232577334519577527009 837924433000889683145257)
                    ·
                      refine ⟨628443324750667262358943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837924433000889683145257 628443324750667262358943)
                      ·
                        rfl

theorem cell23_1223889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_1223889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223889 prefixEnd_1223889 := by exact prefixLift 1223889
  have htrace : WordTrace (prefixWord ++ tailWord_1223889) baseStart_1223889 baseEnd_1223889 := by
    simpa [prefixWord, tailWord_1223889, baseEnd_1223889] using wordTrace_append hprefix tailTrace_1223889
  have hstable : (prefixWord ++ tailWord_1223889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223889).length < 2 ^ (prefixWord ++ tailWord_1223889).sum := by decide
  have hdescent : baseEnd_1223889 < baseStart_1223889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223895 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 9]
def baseStart_1223895 : Nat := 118140960795 + 1223895 * 2 ^ 59
def prefixEnd_1223895 : Nat := 4983230072969 + 3 ^ 40 * 1223895 * 2
def baseEnd_1223895 : Nat := 69827378403843804320435

theorem tailTrace_1223895 : CollatzResearch.WordTrace tailWord_1223895 prefixEnd_1223895 69827378403843804320435 := by
  unfold tailWord_1223895
  simp only [CollatzResearch.WordTrace]
  refine ⟨44639117901044914469809139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29759411934029942979872759 44639117901044914469809139)
  ·
    refine ⟨66958676851567371704713709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44639117901044914469809139 66958676851567371704713709)
    ·
      refine ⟨25109503819337764389267641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66958676851567371704713709 25109503819337764389267641)
      ·
        refine ⟨18832127864503323291950731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25109503819337764389267641 18832127864503323291950731)
        ·
          refine ⟨28248191796754984937926097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18832127864503323291950731 28248191796754984937926097)
          ·
            refine ⟨21186143847566238703444573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28248191796754984937926097 21186143847566238703444573)
            ·
              refine ⟨7944803942837339513791715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21186143847566238703444573 7944803942837339513791715)
              ·
                refine ⟨11917205914256009270687573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944803942837339513791715 11917205914256009270687573)
                ·
                  refine ⟨69827378403843804320435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11917205914256009270687573 69827378403843804320435)
                  ·
                    rfl

theorem cell23_1223895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 9].length) (baseStart_1223895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223895 prefixEnd_1223895 := by exact prefixLift 1223895
  have htrace : WordTrace (prefixWord ++ tailWord_1223895) baseStart_1223895 baseEnd_1223895 := by
    simpa [prefixWord, tailWord_1223895, baseEnd_1223895] using wordTrace_append hprefix tailTrace_1223895
  have hstable : (prefixWord ++ tailWord_1223895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223895).length < 2 ^ (prefixWord ++ tailWord_1223895).sum := by decide
  have hdescent : baseEnd_1223895 < baseStart_1223895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223923 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 2, 2, 2]
def baseStart_1223923 : Nat := 118140960795 + 1223923 * 2 ^ 59
def prefixEnd_1223923 : Nat := 4983230072969 + 3 ^ 40 * 1223923 * 2
def baseEnd_1223923 : Nat := 628460783092920129333787

theorem tailTrace_1223923 : CollatzResearch.WordTrace tailWord_1223923 prefixEnd_1223923 628460783092920129333787 := by
  unfold tailWord_1223923
  simp only [CollatzResearch.WordTrace]
  refine ⟨44640139144943475251828423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29760092763295650167885615 44640139144943475251828423)
  ·
    refine ⟨66960208717415212877742635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44640139144943475251828423 66960208717415212877742635)
    ·
      refine ⟨100440313076122819316613953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66960208717415212877742635 100440313076122819316613953)
      ·
        refine ⟨75330234807092114487460465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100440313076122819316613953 75330234807092114487460465)
        ·
          refine ⟨56497676105319085865595349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75330234807092114487460465 56497676105319085865595349)
          ·
            refine ⟨1324164283718416074974891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56497676105319085865595349 1324164283718416074974891)
            ·
              refine ⟨1986246425577624112462337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324164283718416074974891 1986246425577624112462337)
              ·
                refine ⟨1489684819183218084346753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986246425577624112462337 1489684819183218084346753)
                ·
                  refine ⟨1117263614387413563260065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1489684819183218084346753 1117263614387413563260065)
                  ·
                    refine ⟨837947710790560172445049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117263614387413563260065 837947710790560172445049)
                    ·
                      refine ⟨628460783092920129333787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837947710790560172445049 628460783092920129333787)
                      ·
                        rfl

theorem cell23_1223923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2, 2].length) (baseStart_1223923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223923 prefixEnd_1223923 := by exact prefixLift 1223923
  have htrace : WordTrace (prefixWord ++ tailWord_1223923) baseStart_1223923 baseEnd_1223923 := by
    simpa [prefixWord, tailWord_1223923, baseEnd_1223923] using wordTrace_append hprefix tailTrace_1223923
  have hstable : (prefixWord ++ tailWord_1223923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223923).length < 2 ^ (prefixWord ++ tailWord_1223923).sum := by decide
  have hdescent : baseEnd_1223923 < baseStart_1223923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223940 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_1223940 : Nat := 118140960795 + 1223940 * 2 ^ 59
def prefixEnd_1223940 : Nat := 4983230072969 + 3 ^ 40 * 1223940 * 2
def baseEnd_1223940 : Nat := 628469512264046562821209

theorem tailTrace_1223940 : CollatzResearch.WordTrace tailWord_1223940 prefixEnd_1223940 628469512264046562821209 := by
  unfold tailWord_1223940
  simp only [CollatzResearch.WordTrace]
  refine ⟨22320379592940943577598637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29760506123921258103464849 22320379592940943577598637)
  ·
    refine ⟨8370142347352853841599489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22320379592940943577598637 8370142347352853841599489)
    ·
      refine ⟨6277606760514640381199617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8370142347352853841599489 6277606760514640381199617)
      ·
        refine ⟨4708205070385980285899713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6277606760514640381199617 4708205070385980285899713)
        ·
          refine ⟨3531153802789485214424785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4708205070385980285899713 3531153802789485214424785)
          ·
            refine ⟨2648365352092113910818589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3531153802789485214424785 2648365352092113910818589)
            ·
              refine ⟨993137007034542716556971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648365352092113910818589 993137007034542716556971)
              ·
                refine ⟨1489705510551814074835457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993137007034542716556971 1489705510551814074835457)
                ·
                  refine ⟨1117279132913860556126593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1489705510551814074835457 1117279132913860556126593)
                  ·
                    refine ⟨837959349685395417094945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117279132913860556126593 837959349685395417094945)
                    ·
                      refine ⟨628469512264046562821209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 837959349685395417094945 628469512264046562821209)
                      ·
                        rfl

theorem cell23_1223940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_1223940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1223940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1223940 prefixEnd_1223940 := by exact prefixLift 1223940
  have htrace : WordTrace (prefixWord ++ tailWord_1223940) baseStart_1223940 baseEnd_1223940 := by
    simpa [prefixWord, tailWord_1223940, baseEnd_1223940] using wordTrace_append hprefix tailTrace_1223940
  have hstable : (prefixWord ++ tailWord_1223940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223940).length < 2 ^ (prefixWord ++ tailWord_1223940).sum := by decide
  have hdescent : baseEnd_1223940 < baseStart_1223940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224069 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_1224069 : Nat := 118140960795 + 1224069 * 2 ^ 59
def prefixEnd_1224069 : Nat := 4983230072969 + 3 ^ 40 * 1224069 * 2
def baseEnd_1224069 : Nat := 628535751268476558108115

theorem tailTrace_1224069 : CollatzResearch.WordTrace tailWord_1224069 prefixEnd_1224069 628535751268476558108115 := by
  unfold tailWord_1224069
  simp only [CollatzResearch.WordTrace]
  refine ⟨44645464202414542186643261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29763642801609694791095507 44645464202414542186643261)
  ·
    refine ⟨16742049075905453319991223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44645464202414542186643261 16742049075905453319991223)
    ·
      refine ⟨25113073613858179979986835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16742049075905453319991223 25113073613858179979986835)
      ·
        refine ⟨37669610420787269969980253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25113073613858179979986835 37669610420787269969980253)
        ·
          refine ⟨14126103907795226238742595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37669610420787269969980253 14126103907795226238742595)
          ·
            refine ⟨21189155861692839358113893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14126103907795226238742595 21189155861692839358113893)
            ·
              refine ⟨3972966724067407379646355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21189155861692839358113893 3972966724067407379646355)
              ·
                refine ⟨5959450086101111069469533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972966724067407379646355 5959450086101111069469533)
                ·
                  refine ⟨2234793782287916651051075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5959450086101111069469533 2234793782287916651051075)
                  ·
                    refine ⟨3352190673431874976576613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2234793782287916651051075 3352190673431874976576613)
                    ·
                      refine ⟨628535751268476558108115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3352190673431874976576613 628535751268476558108115)
                      ·
                        rfl

theorem cell23_1224069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_1224069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224069 prefixEnd_1224069 := by exact prefixLift 1224069
  have htrace : WordTrace (prefixWord ++ tailWord_1224069) baseStart_1224069 baseEnd_1224069 := by
    simpa [prefixWord, tailWord_1224069, baseEnd_1224069] using wordTrace_append hprefix tailTrace_1224069
  have hstable : (prefixWord ++ tailWord_1224069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224069).length < 2 ^ (prefixWord ++ tailWord_1224069).sum := by decide
  have hdescent : baseEnd_1224069 < baseStart_1224069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224112 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_1224112 : Nat := 118140960795 + 1224112 * 2 ^ 59
def prefixEnd_1224112 : Nat := 4983230072969 + 3 ^ 40 * 1224112 * 2
def baseEnd_1224112 : Nat := 628557830936619889870417

theorem tailTrace_1224112 : CollatzResearch.WordTrace tailWord_1224112 prefixEnd_1224112 628557830936619889870417 := by
  unfold tailWord_1224112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323516270629380265229295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29764688360839173686972393 22323516270629380265229295)
  ·
    refine ⟨33485274405944070397843943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22323516270629380265229295 33485274405944070397843943)
    ·
      refine ⟨50227911608916105596765915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33485274405944070397843943 50227911608916105596765915)
      ·
        refine ⟨75341867413374158395148873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50227911608916105596765915 75341867413374158395148873)
        ·
          refine ⟨56506400560030618796361655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75341867413374158395148873 56506400560030618796361655)
          ·
            refine ⟨84759600840045928194542483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56506400560030618796361655 84759600840045928194542483)
            ·
              refine ⟨127139401260068892291813725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84759600840045928194542483 127139401260068892291813725)
              ·
                refine ⟨47677275472525834609430147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127139401260068892291813725 47677275472525834609430147)
                ·
                  refine ⟨71515913208788751914145221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47677275472525834609430147 71515913208788751914145221)
                  ·
                    refine ⟨13409233726647890983902229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71515913208788751914145221 13409233726647890983902229)
                    ·
                      refine ⟨628557830936619889870417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13409233726647890983902229 628557830936619889870417)
                      ·
                        rfl

theorem cell23_1224112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_1224112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224112 prefixEnd_1224112 := by exact prefixLift 1224112
  have htrace : WordTrace (prefixWord ++ tailWord_1224112) baseStart_1224112 baseEnd_1224112 := by
    simpa [prefixWord, tailWord_1224112, baseEnd_1224112] using wordTrace_append hprefix tailTrace_1224112
  have hstable : (prefixWord ++ tailWord_1224112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224112).length < 2 ^ (prefixWord ++ tailWord_1224112).sum := by decide
  have hdescent : baseEnd_1224112 < baseStart_1224112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224113 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 2, 4]
def baseStart_1224113 : Nat := 118140960795 + 1224113 * 2 ^ 59
def prefixEnd_1224113 : Nat := 4983230072969 + 3 ^ 40 * 1224113 * 2
def baseEnd_1224113 : Nat := 209519448139091461985971

theorem tailTrace_1224113 : CollatzResearch.WordTrace tailWord_1224113 prefixEnd_1224113 209519448139091461985971 := by
  unfold tailWord_1224113
  simp only [CollatzResearch.WordTrace]
  refine ⟨44647069014255137701244993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29764712676170091800829995 44647069014255137701244993)
  ·
    refine ⟨33485301760691353275933745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44647069014255137701244993 33485301760691353275933745)
    ·
      refine ⟨25113976320518514956950309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33485301760691353275933745 25113976320518514956950309)
      ·
        refine ⟨4708870560097221554428183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25113976320518514956950309 4708870560097221554428183)
        ·
          refine ⟨7063305840145832331642275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708870560097221554428183 7063305840145832331642275)
          ·
            refine ⟨10594958760218748497463413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063305840145832331642275 10594958760218748497463413)
            ·
              refine ⟨993277383770507671637195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10594958760218748497463413 993277383770507671637195)
              ·
                refine ⟨1489916075655761507455793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993277383770507671637195 1489916075655761507455793)
                ·
                  refine ⟨1117437056741821130591845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1489916075655761507455793 1117437056741821130591845)
                  ·
                    refine ⟨209519448139091461985971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117437056741821130591845 209519448139091461985971)
                    ·
                      rfl

theorem cell23_1224113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_1224113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224113 prefixEnd_1224113 := by exact prefixLift 1224113
  have htrace : WordTrace (prefixWord ++ tailWord_1224113) baseStart_1224113 baseEnd_1224113 := by
    simpa [prefixWord, tailWord_1224113, baseEnd_1224113] using wordTrace_append hprefix tailTrace_1224113
  have hstable : (prefixWord ++ tailWord_1224113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224113).length < 2 ^ (prefixWord ++ tailWord_1224113).sum := by decide
  have hdescent : baseEnd_1224113 < baseStart_1224113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224136 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_1224136 : Nat := 118140960795 + 1224136 * 2 ^ 59
def prefixEnd_1224136 : Nat := 4983230072969 + 3 ^ 40 * 1224136 * 2
def baseEnd_1224136 : Nat := 628570154472327795970307

theorem tailTrace_1224136 : CollatzResearch.WordTrace tailWord_1224136 prefixEnd_1224136 628570154472327795970307 := by
  unfold tailWord_1224136
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323953946585906314666131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29765271928781208419554841 22323953946585906314666131)
  ·
    refine ⟨33485930919878859471999197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22323953946585906314666131 33485930919878859471999197)
    ·
      refine ⟨12557224094954572301999699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33485930919878859471999197 12557224094954572301999699)
      ·
        refine ⟨18835836142431858452999549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557224094954572301999699 18835836142431858452999549)
        ·
          refine ⟨7063438553411946919874831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18835836142431858452999549 7063438553411946919874831)
          ·
            refine ⟨10595157830117920379812247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063438553411946919874831 10595157830117920379812247)
            ·
              refine ⟨15892736745176880569718371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595157830117920379812247 15892736745176880569718371)
              ·
                refine ⟨23839105117765320854577557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15892736745176880569718371 23839105117765320854577557)
                ·
                  refine ⟨1117458052395249415058323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23839105117765320854577557 1117458052395249415058323)
                  ·
                    refine ⟨1676187078592874122587485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1117458052395249415058323 1676187078592874122587485)
                    ·
                      refine ⟨628570154472327795970307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676187078592874122587485 628570154472327795970307)
                      ·
                        rfl

theorem cell23_1224136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_1224136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224136 prefixEnd_1224136 := by exact prefixLift 1224136
  have htrace : WordTrace (prefixWord ++ tailWord_1224136) baseStart_1224136 baseEnd_1224136 := by
    simpa [prefixWord, tailWord_1224136, baseEnd_1224136] using wordTrace_append hprefix tailTrace_1224136
  have hstable : (prefixWord ++ tailWord_1224136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224136).length < 2 ^ (prefixWord ++ tailWord_1224136).sum := by decide
  have hdescent : baseEnd_1224136 < baseStart_1224136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224149 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1224149 : Nat := 118140960795 + 1224149 * 2 ^ 59
def prefixEnd_1224149 : Nat := 4983230072969 + 3 ^ 40 * 1224149 * 2
def baseEnd_1224149 : Nat := 628576829720836245107747

theorem tailTrace_1224149 : CollatzResearch.WordTrace tailWord_1224149 prefixEnd_1224149 628576829720836245107747 := by
  unfold tailWord_1224149
  simp only [CollatzResearch.WordTrace]
  refine ⟨44648382042124715849555501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29765588028083143899703667 44648382042124715849555501)
  ·
    refine ⟨16743143265796768443583313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44648382042124715849555501 16743143265796768443583313)
    ·
      refine ⟨12557357449347576332687485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16743143265796768443583313 12557357449347576332687485)
      ·
        refine ⟨4709009043505341124757807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12557357449347576332687485 4709009043505341124757807)
        ·
          refine ⟨7063513565258011687136711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709009043505341124757807 7063513565258011687136711)
          ·
            refine ⟨10595270347887017530705067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063513565258011687136711 10595270347887017530705067)
            ·
              refine ⟨15892905521830526296057601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595270347887017530705067 15892905521830526296057601)
              ·
                refine ⟨11919679141372894722043201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15892905521830526296057601 11919679141372894722043201)
                ·
                  refine ⟨8939759356029671041532401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11919679141372894722043201 8939759356029671041532401)
                  ·
                    refine ⟨6704819517022253281149301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8939759356029671041532401 6704819517022253281149301)
                    ·
                      refine ⟨628576829720836245107747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6704819517022253281149301 628576829720836245107747)
                      ·
                        rfl

theorem cell23_1224149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1224149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224149 prefixEnd_1224149 := by exact prefixLift 1224149
  have htrace : WordTrace (prefixWord ++ tailWord_1224149) baseStart_1224149 baseEnd_1224149 := by
    simpa [prefixWord, tailWord_1224149, baseEnd_1224149] using wordTrace_append hprefix tailTrace_1224149
  have hstable : (prefixWord ++ tailWord_1224149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224149).length < 2 ^ (prefixWord ++ tailWord_1224149).sum := by decide
  have hdescent : baseEnd_1224149 < baseStart_1224149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224159 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1224159 : Nat := 118140960795 + 1224159 * 2 ^ 59
def prefixEnd_1224159 : Nat := 4983230072969 + 3 ^ 40 * 1224159 * 2
def baseEnd_1224159 : Nat := 628581964527381205982701

theorem tailTrace_1224159 : CollatzResearch.WordTrace tailWord_1224159 prefixEnd_1224159 628581964527381205982701 := by
  unfold tailWord_1224159
  simp only [CollatzResearch.WordTrace]
  refine ⟨44648746772088487557419531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29765831181392325038279687 44648746772088487557419531)
  ·
    refine ⟨66973120158132731336129297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44648746772088487557419531 66973120158132731336129297)
    ·
      refine ⟨50229840118599548502096973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66973120158132731336129297 50229840118599548502096973)
      ·
        refine ⟨18836190044474830688286365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50229840118599548502096973 18836190044474830688286365)
        ·
          refine ⟨7063571266678061508107387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18836190044474830688286365 7063571266678061508107387)
          ·
            refine ⟨10595356900017092262161081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063571266678061508107387 10595356900017092262161081)
            ·
              refine ⟨7946517675012819196620811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10595356900017092262161081 7946517675012819196620811)
              ·
                refine ⟨11919776512519228794931217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946517675012819196620811 11919776512519228794931217)
                ·
                  refine ⟨8939832384389421596198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11919776512519228794931217 8939832384389421596198413)
                  ·
                    refine ⟨3352437144146033098574405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8939832384389421596198413 3352437144146033098574405)
                    ·
                      refine ⟨628581964527381205982701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3352437144146033098574405 628581964527381205982701)
                      ·
                        rfl

theorem cell23_1224159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1224159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224159 prefixEnd_1224159 := by exact prefixLift 1224159
  have htrace : WordTrace (prefixWord ++ tailWord_1224159) baseStart_1224159 baseEnd_1224159 := by
    simpa [prefixWord, tailWord_1224159, baseEnd_1224159] using wordTrace_append hprefix tailTrace_1224159
  have hstable : (prefixWord ++ tailWord_1224159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224159).length < 2 ^ (prefixWord ++ tailWord_1224159).sum := by decide
  have hdescent : baseEnd_1224159 < baseStart_1224159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224170 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_1224170 : Nat := 118140960795 + 1224170 * 2 ^ 59
def prefixEnd_1224170 : Nat := 4983230072969 + 3 ^ 40 * 1224170 * 2
def baseEnd_1224170 : Nat := 628587612814580662945151

theorem tailTrace_1224170 : CollatzResearch.WordTrace tailWord_1224170 prefixEnd_1224170 628587612814580662945151 := by
  unfold tailWord_1224170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162286993762159109017491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29766098650032424290713309 11162286993762159109017491)
  ·
    refine ⟨16743430490643238663526237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11162286993762159109017491 16743430490643238663526237)
    ·
      refine ⟨6278786433991214498822339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16743430490643238663526237 6278786433991214498822339)
      ·
        refine ⟨9418179650986821748233509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6278786433991214498822339 9418179650986821748233509)
        ·
          refine ⟨1765908684560029077793783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9418179650986821748233509 1765908684560029077793783)
          ·
            refine ⟨2648863026840043616690675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765908684560029077793783 2648863026840043616690675)
            ·
              refine ⟨3973294540260065425036013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648863026840043616690675 3973294540260065425036013)
              ·
                refine ⟨1489985452597524534388505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3973294540260065425036013 1489985452597524534388505)
                ·
                  refine ⟨1117489089448143400791379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1489985452597524534388505 1117489089448143400791379)
                  ·
                    refine ⟨1676233634172215101187069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1117489089448143400791379 1676233634172215101187069)
                    ·
                      refine ⟨628587612814580662945151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676233634172215101187069 628587612814580662945151)
                      ·
                        rfl

theorem cell23_1224170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_1224170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224170 prefixEnd_1224170 := by exact prefixLift 1224170
  have htrace : WordTrace (prefixWord ++ tailWord_1224170) baseStart_1224170 baseEnd_1224170 := by
    simpa [prefixWord, tailWord_1224170, baseEnd_1224170] using wordTrace_append hprefix tailTrace_1224170
  have hstable : (prefixWord ++ tailWord_1224170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224170).length < 2 ^ (prefixWord ++ tailWord_1224170).sum := by decide
  have hdescent : baseEnd_1224170 < baseStart_1224170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224179 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3]
def baseStart_1224179 : Nat := 118140960795 + 1224179 * 2 ^ 59
def prefixEnd_1224179 : Nat := 4983230072969 + 3 ^ 40 * 1224179 * 2
def baseEnd_1224179 : Nat := 628592234140471127732609

theorem tailTrace_1224179 : CollatzResearch.WordTrace tailWord_1224179 prefixEnd_1224179 628592234140471127732609 := by
  unfold tailWord_1224179
  simp only [CollatzResearch.WordTrace]
  refine ⟨44649476232016030973147591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29766317488010687315431727 44649476232016030973147591)
  ·
    refine ⟨66974214348024046459721387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44649476232016030973147591 66974214348024046459721387)
    ·
      refine ⟨100461321522036069689582081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66974214348024046459721387 100461321522036069689582081)
      ·
        refine ⟨75345991141527052267186561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100461321522036069689582081 75345991141527052267186561)
        ·
          refine ⟨56509493356145289200389921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75345991141527052267186561 56509493356145289200389921)
          ·
            refine ⟨42382120017108966900292441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56509493356145289200389921 42382120017108966900292441)
            ·
              refine ⟨31786590012831725175219331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42382120017108966900292441 31786590012831725175219331)
              ·
                refine ⟨47679885019247587762828997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31786590012831725175219331 47679885019247587762828997)
                ·
                  refine ⟨8939978441108922705530437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47679885019247587762828997 8939978441108922705530437)
                  ·
                    refine ⟨1676245957707923007286957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8939978441108922705530437 1676245957707923007286957)
                    ·
                      refine ⟨628592234140471127732609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676245957707923007286957 628592234140471127732609)
                      ·
                        rfl

theorem cell23_1224179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_1224179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224179 prefixEnd_1224179 := by exact prefixLift 1224179
  have htrace : WordTrace (prefixWord ++ tailWord_1224179) baseStart_1224179 baseEnd_1224179 := by
    simpa [prefixWord, tailWord_1224179, baseEnd_1224179] using wordTrace_append hprefix tailTrace_1224179
  have hstable : (prefixWord ++ tailWord_1224179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224179).length < 2 ^ (prefixWord ++ tailWord_1224179).sum := by decide
  have hdescent : baseEnd_1224179 < baseStart_1224179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224205 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1224205 : Nat := 118140960795 + 1224205 * 2 ^ 59
def prefixEnd_1224205 : Nat := 4983230072969 + 3 ^ 40 * 1224205 * 2
def baseEnd_1224205 : Nat := 628605584637488026007491

theorem tailTrace_1224205 : CollatzResearch.WordTrace tailWord_1224205 prefixEnd_1224205 628605584637488026007491 := by
  unfold tailWord_1224205
  simp only [CollatzResearch.WordTrace]
  refine ⟨44650424529921837413594069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29766949686614558275729379 44650424529921837413594069)
  ·
    refine ⟨1046494324920043064381111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 44650424529921837413594069 1046494324920043064381111)
    ·
      refine ⟨1569741487380064596571667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046494324920043064381111 1569741487380064596571667)
      ·
        refine ⟨2354612231070096894857501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569741487380064596571667 2354612231070096894857501)
        ·
          refine ⟨882979586651286335571563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2354612231070096894857501 882979586651286335571563)
          ·
            refine ⟨1324469379976929503357345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882979586651286335571563 1324469379976929503357345)
            ·
              refine ⟨993352034982697127518009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324469379976929503357345 993352034982697127518009)
              ·
                refine ⟨745014026237022845638507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993352034982697127518009 745014026237022845638507)
                ·
                  refine ⟨1117521039355534268457761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745014026237022845638507 1117521039355534268457761)
                  ·
                    refine ⟨838140779516650701343321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117521039355534268457761 838140779516650701343321)
                    ·
                      refine ⟨628605584637488026007491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838140779516650701343321 628605584637488026007491)
                      ·
                        rfl

theorem cell23_1224205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1224205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224205 prefixEnd_1224205 := by exact prefixLift 1224205
  have htrace : WordTrace (prefixWord ++ tailWord_1224205) baseStart_1224205 baseEnd_1224205 := by
    simpa [prefixWord, tailWord_1224205, baseEnd_1224205] using wordTrace_append hprefix tailTrace_1224205
  have hstable : (prefixWord ++ tailWord_1224205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224205).length < 2 ^ (prefixWord ++ tailWord_1224205).sum := by decide
  have hdescent : baseEnd_1224205 < baseStart_1224205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224226 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1224226 : Nat := 118140960795 + 1224226 * 2 ^ 59
def prefixEnd_1224226 : Nat := 4983230072969 + 3 ^ 40 * 1224226 * 2
def baseEnd_1224226 : Nat := 628616367731232443844893

theorem tailTrace_1224226 : CollatzResearch.WordTrace tailWord_1224226 prefixEnd_1224226 628616367731232443844893 := by
  unfold tailWord_1224226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162797615711439500027133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29767460308563838666739021 11162797615711439500027133)
  ·
    refine ⟨4186049105891789812510175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11162797615711439500027133 4186049105891789812510175)
    ·
      refine ⟨6279073658837684718765263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4186049105891789812510175 6279073658837684718765263)
      ·
        refine ⟨9418610488256527078147895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6279073658837684718765263 9418610488256527078147895)
        ·
          refine ⟨14127915732384790617221843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9418610488256527078147895 14127915732384790617221843)
          ·
            refine ⟨21191873598577185925832765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14127915732384790617221843 21191873598577185925832765)
            ·
              refine ⟨7946952599466444722187287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21191873598577185925832765 7946952599466444722187287)
              ·
                refine ⟨11920428899199667083280931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946952599466444722187287 11920428899199667083280931)
                ·
                  refine ⟨17880643348799500624921397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11920428899199667083280931 17880643348799500624921397)
                  ·
                    refine ⟨1676310313949953183586381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17880643348799500624921397 1676310313949953183586381)
                    ·
                      refine ⟨628616367731232443844893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1676310313949953183586381 628616367731232443844893)
                      ·
                        rfl

theorem cell23_1224226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1224226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224226 prefixEnd_1224226 := by exact prefixLift 1224226
  have htrace : WordTrace (prefixWord ++ tailWord_1224226) baseStart_1224226 baseEnd_1224226 := by
    simpa [prefixWord, tailWord_1224226, baseEnd_1224226] using wordTrace_append hprefix tailTrace_1224226
  have hstable : (prefixWord ++ tailWord_1224226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224226).length < 2 ^ (prefixWord ++ tailWord_1224226).sum := by decide
  have hdescent : baseEnd_1224226 < baseStart_1224226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224229 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_1224229 : Nat := 118140960795 + 1224229 * 2 ^ 59
def prefixEnd_1224229 : Nat := 4983230072969 + 3 ^ 40 * 1224229 * 2
def baseEnd_1224229 : Nat := 209539302724398644035793

theorem tailTrace_1224229 : CollatzResearch.WordTrace tailWord_1224229 prefixEnd_1224229 209539302724398644035793 := by
  unfold tailWord_1224229
  simp only [CollatzResearch.WordTrace]
  refine ⟨44651299881834889512467741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29767533254556593008311827 44651299881834889512467741)
  ·
    refine ⟨16744237455688083567175403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44651299881834889512467741 16744237455688083567175403)
    ·
      refine ⟨25116356183532125350763105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16744237455688083567175403 25116356183532125350763105)
      ·
        refine ⟨18837267137649094013072329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25116356183532125350763105 18837267137649094013072329)
        ·
          refine ⟨14127950353236820509804247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18837267137649094013072329 14127950353236820509804247)
          ·
            refine ⟨21191925529855230764706371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14127950353236820509804247 21191925529855230764706371)
            ·
              refine ⟨31787888294782846147059557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21191925529855230764706371 31787888294782846147059557)
              ·
                refine ⟨5960229055271783652573667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31787888294782846147059557 5960229055271783652573667)
                ·
                  refine ⟨8940343582907675478860501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960229055271783652573667 8940343582907675478860501)
                  ·
                    refine ⟨209539302724398644035793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8940343582907675478860501 209539302724398644035793)
                    ·
                      rfl

theorem cell23_1224229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1224229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224229 prefixEnd_1224229 := by exact prefixLift 1224229
  have htrace : WordTrace (prefixWord ++ tailWord_1224229) baseStart_1224229 baseEnd_1224229 := by
    simpa [prefixWord, tailWord_1224229, baseEnd_1224229] using wordTrace_append hprefix tailTrace_1224229
  have hstable : (prefixWord ++ tailWord_1224229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224229).length < 2 ^ (prefixWord ++ tailWord_1224229).sum := by decide
  have hdescent : baseEnd_1224229 < baseStart_1224229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224266 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1224266 : Nat := 118140960795 + 1224266 * 2 ^ 59
def prefixEnd_1224266 : Nat := 4983230072969 + 3 ^ 40 * 1224266 * 2
def baseEnd_1224266 : Nat := 628636906957412287344709

theorem tailTrace_1224266 : CollatzResearch.WordTrace tailWord_1224266 prefixEnd_1224266 628636906957412287344709 := by
  unfold tailWord_1224266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163162345675211207891163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29768432921800563221043101 11163162345675211207891163)
  ·
    refine ⟨16744743518512816811836745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163162345675211207891163 16744743518512816811836745)
    ·
      refine ⟨12558557638884612608877559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16744743518512816811836745 12558557638884612608877559)
      ·
        refine ⟨18837836458326918913316339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12558557638884612608877559 18837836458326918913316339)
        ·
          refine ⟨28256754687490378369974509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18837836458326918913316339 28256754687490378369974509)
          ·
            refine ⟨10596283007808891888740441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28256754687490378369974509 10596283007808891888740441)
            ·
              refine ⟨7947212255856668916555331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10596283007808891888740441 7947212255856668916555331)
              ·
                refine ⟨11920818383785003374832997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7947212255856668916555331 11920818383785003374832997)
                ·
                  refine ⟨2235153446959688132781187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11920818383785003374832997 2235153446959688132781187)
                  ·
                    refine ⟨3352730170439532199171781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235153446959688132781187 3352730170439532199171781)
                    ·
                      refine ⟨628636906957412287344709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3352730170439532199171781 628636906957412287344709)
                      ·
                        rfl

theorem cell23_1224266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1224266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224266 prefixEnd_1224266 := by exact prefixLift 1224266
  have htrace : WordTrace (prefixWord ++ tailWord_1224266) baseStart_1224266 baseEnd_1224266 := by
    simpa [prefixWord, tailWord_1224266, baseEnd_1224266] using wordTrace_append hprefix tailTrace_1224266
  have hstable : (prefixWord ++ tailWord_1224266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224266).length < 2 ^ (prefixWord ++ tailWord_1224266).sum := by decide
  have hdescent : baseEnd_1224266 < baseStart_1224266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224278 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1224278 : Nat := 118140960795 + 1224278 * 2 ^ 59
def prefixEnd_1224278 : Nat := 4983230072969 + 3 ^ 40 * 1224278 * 2
def baseEnd_1224278 : Nat := 628643068725266240394655

theorem tailTrace_1224278 : CollatzResearch.WordTrace tailWord_1224278 prefixEnd_1224278 628643068725266240394655 := by
  unfold tailWord_1224278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790817941166085680062593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29768724705771580587334325 2790817941166085680062593)
  ·
    refine ⟨2093113455874564260046945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2790817941166085680062593 2093113455874564260046945)
    ·
      refine ⟨1569835091905923195035209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2093113455874564260046945 1569835091905923195035209)
      ·
        refine ⟨1177376318929442396276407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1569835091905923195035209 1177376318929442396276407)
        ·
          refine ⟨1766064478394163594414611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177376318929442396276407 1766064478394163594414611)
          ·
            refine ⟨2649096717591245391621917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766064478394163594414611 2649096717591245391621917)
            ·
              refine ⟨993411269096717021858219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2649096717591245391621917 993411269096717021858219)
              ·
                refine ⟨1490116903645075532787329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993411269096717021858219 1490116903645075532787329)
                ·
                  refine ⟨1117587677733806649590497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490116903645075532787329 1117587677733806649590497)
                  ·
                    refine ⟨838190758300354987192873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117587677733806649590497 838190758300354987192873)
                    ·
                      refine ⟨628643068725266240394655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 838190758300354987192873 628643068725266240394655)
                      ·
                        rfl

theorem cell23_1224278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1224278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224278 prefixEnd_1224278 := by exact prefixLift 1224278
  have htrace : WordTrace (prefixWord ++ tailWord_1224278) baseStart_1224278 baseEnd_1224278 := by
    simpa [prefixWord, tailWord_1224278, baseEnd_1224278] using wordTrace_append hprefix tailTrace_1224278
  have hstable : (prefixWord ++ tailWord_1224278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224278).length < 2 ^ (prefixWord ++ tailWord_1224278).sum := by decide
  have hdescent : baseEnd_1224278 < baseStart_1224278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224293 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1224293 : Nat := 118140960795 + 1224293 * 2 ^ 59
def prefixEnd_1224293 : Nat := 4983230072969 + 3 ^ 40 * 1224293 * 2
def baseEnd_1224293 : Nat := 209550256978361227235695

theorem tailTrace_1224293 : CollatzResearch.WordTrace tailWord_1224293 prefixEnd_1224293 209550256978361227235695 := by
  unfold tailWord_1224293
  simp only [CollatzResearch.WordTrace]
  refine ⟨44653634153603028442797533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29769089435735352295198355 44653634153603028442797533)
  ·
    refine ⟨16745112807601135666049075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44653634153603028442797533 16745112807601135666049075)
    ·
      refine ⟨25117669211401703499073613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16745112807601135666049075 25117669211401703499073613)
      ·
        refine ⟨9419125954275638812152605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25117669211401703499073613 9419125954275638812152605)
        ·
          refine ⟨3532172232853364554557227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9419125954275638812152605 3532172232853364554557227)
          ·
            refine ⟨5298258349280046831835841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532172232853364554557227 5298258349280046831835841)
            ·
              refine ⟨3973693761960035123876881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5298258349280046831835841 3973693761960035123876881)
              ·
                refine ⟨2980270321470026342907661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973693761960035123876881 2980270321470026342907661)
                ·
                  refine ⟨1117601370551259878590373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2980270321470026342907661 1117601370551259878590373)
                  ·
                    refine ⟨209550256978361227235695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117601370551259878590373 209550256978361227235695)
                    ·
                      rfl

theorem cell23_1224293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1224293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224293 prefixEnd_1224293 := by exact prefixLift 1224293
  have htrace : WordTrace (prefixWord ++ tailWord_1224293) baseStart_1224293 baseEnd_1224293 := by
    simpa [prefixWord, tailWord_1224293, baseEnd_1224293] using wordTrace_append hprefix tailTrace_1224293
  have hstable : (prefixWord ++ tailWord_1224293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224293).length < 2 ^ (prefixWord ++ tailWord_1224293).sum := by decide
  have hdescent : baseEnd_1224293 < baseStart_1224293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224306 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_1224306 : Nat := 118140960795 + 1224306 * 2 ^ 59
def prefixEnd_1224306 : Nat := 4983230072969 + 3 ^ 40 * 1224306 * 2
def baseEnd_1224306 : Nat := 69850827353732458982725

theorem tailTrace_1224306 : CollatzResearch.WordTrace tailWord_1224306 prefixEnd_1224306 69850827353732458982725 := by
  unfold tailWord_1224306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163527075638982915755193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29769405535037287775347181 11163527075638982915755193)
  ·
    refine ⟨8372645306729237186816395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11163527075638982915755193 8372645306729237186816395)
    ·
      refine ⟨12558967960093855780224593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8372645306729237186816395 12558967960093855780224593)
      ·
        refine ⟨9419225970070391835168445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12558967960093855780224593 9419225970070391835168445)
        ·
          refine ⟨3532209738776396938188167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9419225970070391835168445 3532209738776396938188167)
          ·
            refine ⟨5298314608164595407282251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532209738776396938188167 5298314608164595407282251)
            ·
              refine ⟨7947471912246893110923377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298314608164595407282251 7947471912246893110923377)
              ·
                refine ⟨5960603934185169833192533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7947471912246893110923377 5960603934185169833192533)
                ·
                  refine ⟨69850827353732458982725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5960603934185169833192533 69850827353732458982725)
                  ·
                    rfl

theorem cell23_1224306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_1224306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1224306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1224306 prefixEnd_1224306 := by exact prefixLift 1224306
  have htrace : WordTrace (prefixWord ++ tailWord_1224306) baseStart_1224306 baseEnd_1224306 := by
    simpa [prefixWord, tailWord_1224306, baseEnd_1224306] using wordTrace_append hprefix tailTrace_1224306
  have hstable : (prefixWord ++ tailWord_1224306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224306).length < 2 ^ (prefixWord ++ tailWord_1224306).sum := by decide
  have hdescent : baseEnd_1224306 < baseStart_1224306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
