import V185TrunkScan21Chunk059

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_727348 : List Nat := [2, 5, 1, 1, 1, 11]
def baseStart_727348 : Nat := 118140960795 + 727348 * 2 ^ 59
def prefixEnd_727348 : Nat := 4983230072969 + 3 ^ 40 * 727348 * 2
def baseEnd_727348 : Nat := 6147804561095069651111

theorem tailTrace_727348 : CollatzResearch.WordTrace tailWord_727348 prefixEnd_727348 6147804561095069651111 := by
  unfold tailWord_727348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13264280484474945996879349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17685707312633261329172465 13264280484474945996879349)
  ·
    refine ⟨1243526295419526187207439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13264280484474945996879349 1243526295419526187207439)
    ·
      refine ⟨1865289443129289280811159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243526295419526187207439 1865289443129289280811159)
      ·
        refine ⟨2797934164693933921216739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865289443129289280811159 2797934164693933921216739)
        ·
          refine ⟨4196901247040900881825109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797934164693933921216739 4196901247040900881825109)
          ·
            refine ⟨6147804561095069651111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4196901247040900881825109 6147804561095069651111)
            ·
              rfl

theorem cell21_727348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 11].length) (baseStart_727348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727348 prefixEnd_727348 := by exact prefixLift 727348
  have htrace : WordTrace (prefixWord ++ tailWord_727348) baseStart_727348 baseEnd_727348 := by
    simpa [prefixWord, tailWord_727348, baseEnd_727348] using wordTrace_append hprefix tailTrace_727348
  have hstable : (prefixWord ++ tailWord_727348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727348).length < 2 ^ (prefixWord ++ tailWord_727348).sum := by decide
  have hdescent : baseEnd_727348 < baseStart_727348 := by decide
  rcases family_descends (prefixWord ++ tailWord_727348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727396 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_727396 : Nat := 118140960795 + 727396 * 2 ^ 59
def prefixEnd_727396 : Nat := 4983230072969 + 3 ^ 40 * 727396 * 2
def baseEnd_727396 : Nat := 166001677403529463779899

theorem tailTrace_727396 : CollatzResearch.WordTrace tailWord_727396 prefixEnd_727396 166001677403529463779899 := by
  unfold tailWord_727396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13265155836387998095753021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17686874448517330794337361 13265155836387998095753021)
  ·
    refine ⟨4974433438645499285907383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13265155836387998095753021 4974433438645499285907383)
    ·
      refine ⟨7461650157968248928861075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974433438645499285907383 7461650157968248928861075)
      ·
        refine ⟨11192475236952373393291613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461650157968248928861075 11192475236952373393291613)
        ·
          refine ⟨4197178213857140022484355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11192475236952373393291613 4197178213857140022484355)
          ·
            refine ⟨6295767320785710033726533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197178213857140022484355 6295767320785710033726533)
            ·
              refine ⟨1180456372647320631323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6295767320785710033726533 1180456372647320631323725)
              ·
                refine ⟨442671139742745236746397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180456372647320631323725 442671139742745236746397)
                ·
                  refine ⟨166001677403529463779899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442671139742745236746397 166001677403529463779899)
                  ·
                    rfl

theorem cell21_727396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_727396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727396 prefixEnd_727396 := by exact prefixLift 727396
  have htrace : WordTrace (prefixWord ++ tailWord_727396) baseStart_727396 baseEnd_727396 := by
    simpa [prefixWord, tailWord_727396, baseEnd_727396] using wordTrace_append hprefix tailTrace_727396
  have hstable : (prefixWord ++ tailWord_727396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727396).length < 2 ^ (prefixWord ++ tailWord_727396).sum := by decide
  have hdescent : baseEnd_727396 < baseStart_727396 := by decide
  rcases family_descends (prefixWord ++ tailWord_727396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727410 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_727410 : Nat := 118140960795 + 727410 * 2 ^ 59
def prefixEnd_727410 : Nat := 4983230072969 + 3 ^ 40 * 727410 * 2
def baseEnd_727410 : Nat := 166004872394268550546537

theorem tailTrace_727410 : CollatzResearch.WordTrace tailWord_727410 prefixEnd_727410 166004872394268550546537 := by
  unfold tailWord_727410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632705573681319145628921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17687214863150184388343789 6632705573681319145628921)
  ·
    refine ⟨4974529180260989359221691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6632705573681319145628921 4974529180260989359221691)
    ·
      refine ⟨7461793770391484038832537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974529180260989359221691 7461793770391484038832537)
      ·
        refine ⟨5596345327793613029124403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7461793770391484038832537 5596345327793613029124403)
        ·
          refine ⟨8394517991690419543686605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596345327793613029124403 8394517991690419543686605)
          ·
            refine ⟨3147944246883907328882477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8394517991690419543686605 3147944246883907328882477)
            ·
              refine ⟨1180479092581465248330929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3147944246883907328882477 1180479092581465248330929)
              ·
                refine ⟨885359319436098936248197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180479092581465248330929 885359319436098936248197)
                ·
                  refine ⟨166004872394268550546537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885359319436098936248197 166004872394268550546537)
                  ·
                    rfl

theorem cell21_727410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_727410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727410 prefixEnd_727410 := by exact prefixLift 727410
  have htrace : WordTrace (prefixWord ++ tailWord_727410) baseStart_727410 baseEnd_727410 := by
    simpa [prefixWord, tailWord_727410, baseEnd_727410] using wordTrace_append hprefix tailTrace_727410
  have hstable : (prefixWord ++ tailWord_727410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727410).length < 2 ^ (prefixWord ++ tailWord_727410).sum := by decide
  have hdescent : baseEnd_727410 < baseStart_727410 := by decide
  rcases family_descends (prefixWord ++ tailWord_727410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727427 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 4]
def baseStart_727427 : Nat := 118140960795 + 727427 * 2 ^ 59
def prefixEnd_727427 : Nat := 4983230072969 + 3 ^ 40 * 727427 * 2
def baseEnd_727427 : Nat := 166008752025880298763169

theorem tailTrace_727427 : CollatzResearch.WordTrace tailWord_727427 prefixEnd_727427 166008752025880298763169 := by
  unfold tailWord_727427
  simp only [CollatzResearch.WordTrace]
  refine ⟨26531442335663688485884535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17687628223775792323923023 26531442335663688485884535)
  ·
    refine ⟨39797163503495532728826803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26531442335663688485884535 39797163503495532728826803)
    ·
      refine ⟨59695745255243299093240205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39797163503495532728826803 59695745255243299093240205)
      ·
        refine ⟨22385904470716237159965077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59695745255243299093240205 22385904470716237159965077)
        ·
          refine ⟨1049339272064823616873363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22385904470716237159965077 1049339272064823616873363)
          ·
            refine ⟨1574008908097235425310045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049339272064823616873363 1574008908097235425310045)
            ·
              refine ⟨590253340536463284491267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1574008908097235425310045 590253340536463284491267)
              ·
                refine ⟨885380010804694926736901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590253340536463284491267 885380010804694926736901)
                ·
                  refine ⟨166008752025880298763169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885380010804694926736901 166008752025880298763169)
                  ·
                    rfl

theorem cell21_727427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 4].length) (baseStart_727427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727427 prefixEnd_727427 := by exact prefixLift 727427
  have htrace : WordTrace (prefixWord ++ tailWord_727427) baseStart_727427 baseEnd_727427 := by
    simpa [prefixWord, tailWord_727427, baseEnd_727427] using wordTrace_append hprefix tailTrace_727427
  have hstable : (prefixWord ++ tailWord_727427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727427).length < 2 ^ (prefixWord ++ tailWord_727427).sum := by decide
  have hdescent : baseEnd_727427 < baseStart_727427 := by decide
  rcases family_descends (prefixWord ++ tailWord_727427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727531 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 3]
def baseStart_727531 : Nat := 118140960795 + 727531 * 2 ^ 59
def prefixEnd_727531 : Nat := 4983230072969 + 3 ^ 40 * 727531 * 2
def baseEnd_727531 : Nat := 166032486242799229029623

theorem tailTrace_727531 : CollatzResearch.WordTrace tailWord_727531 prefixEnd_727531 166032486242799229029623 := by
  unfold tailWord_727531
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535235527286914247670447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17690157018191276165113631 26535235527286914247670447)
  ·
    refine ⟨39802853290930371371505671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26535235527286914247670447 39802853290930371371505671)
    ·
      refine ⟨59704279936395557057258507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39802853290930371371505671 59704279936395557057258507)
      ·
        refine ⟨89556419904593335585887761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59704279936395557057258507 89556419904593335585887761)
        ·
          refine ⟨67167314928445001689415821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89556419904593335585887761 67167314928445001689415821)
          ·
            refine ⟨25187743098166875633530933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67167314928445001689415821 25187743098166875633530933)
            ·
              refine ⟨2361350915453144590643525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25187743098166875633530933 2361350915453144590643525)
              ·
                refine ⟨442753296647464610745661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2361350915453144590643525 442753296647464610745661)
                ·
                  refine ⟨166032486242799229029623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442753296647464610745661 166032486242799229029623)
                  ·
                    rfl

theorem cell21_727531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3].length) (baseStart_727531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727531 prefixEnd_727531 := by exact prefixLift 727531
  have htrace : WordTrace (prefixWord ++ tailWord_727531) baseStart_727531 baseEnd_727531 := by
    simpa [prefixWord, tailWord_727531, baseEnd_727531] using wordTrace_append hprefix tailTrace_727531
  have hstable : (prefixWord ++ tailWord_727531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727531).length < 2 ^ (prefixWord ++ tailWord_727531).sum := by decide
  have hdescent : baseEnd_727531 < baseStart_727531 := by decide
  rcases family_descends (prefixWord ++ tailWord_727531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727545 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_727545 : Nat := 118140960795 + 727545 * 2 ^ 59
def prefixEnd_727545 : Nat := 4983230072969 + 3 ^ 40 * 727545 * 2
def baseEnd_727545 : Nat := 166035681233538315796261

theorem tailTrace_727545 : CollatzResearch.WordTrace tailWord_727545 prefixEnd_727545 166035681233538315796261 := by
  unfold tailWord_727545
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535746149236194638680089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17690497432824129759120059 26535746149236194638680089)
  ·
    refine ⟨19901809611927145979010067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26535746149236194638680089 19901809611927145979010067)
    ·
      refine ⟨29852714417890718968515101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19901809611927145979010067 29852714417890718968515101)
      ·
        refine ⟨11194767906709019613193163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29852714417890718968515101 11194767906709019613193163)
        ·
          refine ⟨16792151860063529419789745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11194767906709019613193163 16792151860063529419789745)
          ·
            refine ⟨12594113895047647064842309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16792151860063529419789745 12594113895047647064842309)
            ·
              refine ⟨2361396355321433824657933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12594113895047647064842309 2361396355321433824657933)
              ·
                refine ⟨885523633245537684246725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2361396355321433824657933 885523633245537684246725)
                ·
                  refine ⟨166035681233538315796261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885523633245537684246725 166035681233538315796261)
                  ·
                    rfl

theorem cell21_727545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_727545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727545 prefixEnd_727545 := by exact prefixLift 727545
  have htrace : WordTrace (prefixWord ++ tailWord_727545) baseStart_727545 baseEnd_727545 := by
    simpa [prefixWord, tailWord_727545, baseEnd_727545] using wordTrace_append hprefix tailTrace_727545
  have hstable : (prefixWord ++ tailWord_727545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727545).length < 2 ^ (prefixWord ++ tailWord_727545).sum := by decide
  have hdescent : baseEnd_727545 < baseStart_727545 := by decide
  rcases family_descends (prefixWord ++ tailWord_727545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727734 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_727734 : Nat := 118140960795 + 727734 * 2 ^ 59
def prefixEnd_727734 : Nat := 4983230072969 + 3 ^ 40 * 727734 * 2
def baseEnd_727734 : Nat := 166078813608515987145875

theorem tailTrace_727734 : CollatzResearch.WordTrace tailWord_727734 prefixEnd_727734 166078813608515987145875 := by
  unfold tailWord_727734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658914971596967494831891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17695093030367653278206837 1658914971596967494831891)
  ·
    refine ⟨2488372457395451242247837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1658914971596967494831891 2488372457395451242247837)
    ·
      refine ⟨933139671523294215842939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2488372457395451242247837 933139671523294215842939)
      ·
        refine ⟨1399709507284941323764409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933139671523294215842939 1399709507284941323764409)
        ·
          refine ⟨1049782130463705992823307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399709507284941323764409 1049782130463705992823307)
          ·
            refine ⟨1574673195695558989234961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049782130463705992823307 1574673195695558989234961)
            ·
              refine ⟨1181004896771669241926221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574673195695558989234961 1181004896771669241926221)
              ·
                refine ⟨442876836289375965722333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181004896771669241926221 442876836289375965722333)
                ·
                  refine ⟨166078813608515987145875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442876836289375965722333 166078813608515987145875)
                  ·
                    rfl

theorem cell21_727734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_727734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727734 prefixEnd_727734 := by exact prefixLift 727734
  have htrace : WordTrace (prefixWord ++ tailWord_727734) baseStart_727734 baseEnd_727734 := by
    simpa [prefixWord, tailWord_727734, baseEnd_727734] using wordTrace_append hprefix tailTrace_727734
  have hstable : (prefixWord ++ tailWord_727734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727734).length < 2 ^ (prefixWord ++ tailWord_727734).sum := by decide
  have hdescent : baseEnd_727734 < baseStart_727734 := by decide
  rcases family_descends (prefixWord ++ tailWord_727734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727742 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_727742 : Nat := 118140960795 + 727742 * 2 ^ 59
def prefixEnd_727742 : Nat := 4983230072969 + 3 ^ 40 * 727742 * 2
def baseEnd_727742 : Nat := 166080639317509751012525

theorem tailTrace_727742 : CollatzResearch.WordTrace tailWord_727742 prefixEnd_727742 166080639317509751012525 := by
  unfold tailWord_727742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317866416190312160450185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17695287553014998189067653 3317866416190312160450185)
  ·
    refine ⟨2488399812142734120337639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3317866416190312160450185 2488399812142734120337639)
    ·
      refine ⟨3732599718214101180506459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488399812142734120337639 3732599718214101180506459)
      ·
        refine ⟨5598899577321151770759689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732599718214101180506459 5598899577321151770759689)
        ·
          refine ⟨4199174682990863828069767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5598899577321151770759689 4199174682990863828069767)
          ·
            refine ⟨6298762024486295742104651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199174682990863828069767 6298762024486295742104651)
            ·
              refine ⟨9448143036729443613156977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298762024486295742104651 9448143036729443613156977)
              ·
                refine ⟨7086107277547082709867733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9448143036729443613156977 7086107277547082709867733)
                ·
                  refine ⟨166080639317509751012525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7086107277547082709867733 166080639317509751012525)
                  ·
                    rfl

theorem cell21_727742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_727742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727742 prefixEnd_727742 := by exact prefixLift 727742
  have htrace : WordTrace (prefixWord ++ tailWord_727742) baseStart_727742 baseEnd_727742 := by
    simpa [prefixWord, tailWord_727742, baseEnd_727742] using wordTrace_append hprefix tailTrace_727742
  have hstable : (prefixWord ++ tailWord_727742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727742).length < 2 ^ (prefixWord ++ tailWord_727742).sum := by decide
  have hdescent : baseEnd_727742 < baseStart_727742 := by decide
  rcases family_descends (prefixWord ++ tailWord_727742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727745 : List Nat := [1, 2, 6, 2, 1, 1, 8]
def baseStart_727745 : Nat := 118140960795 + 727745 * 2 ^ 59
def prefixEnd_727745 : Nat := 4983230072969 + 3 ^ 40 * 727745 * 2
def baseEnd_727745 : Nat := 18453480439820268051391

theorem tailTrace_727745 : CollatzResearch.WordTrace tailWord_727745 prefixEnd_727745 18453480439820268051391 := by
  unfold tailWord_727745
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543040748511628795960689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17695360499007752530640459 26543040748511628795960689)
  ·
    refine ⟨19907280561383721596970517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26543040748511628795960689 19907280561383721596970517)
    ·
      refine ⟨933153776314861949857993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19907280561383721596970517 933153776314861949857993)
      ·
        refine ⟨699865332236146462393495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933153776314861949857993 699865332236146462393495)
        ·
          refine ⟨1049797998354219693590243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699865332236146462393495 1049797998354219693590243)
          ·
            refine ⟨1574696997531329540385365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049797998354219693590243 1574696997531329540385365)
            ·
              refine ⟨18453480439820268051391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1574696997531329540385365 18453480439820268051391)
              ·
                rfl

theorem cell21_727745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 8].length) (baseStart_727745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727745 prefixEnd_727745 := by exact prefixLift 727745
  have htrace : WordTrace (prefixWord ++ tailWord_727745) baseStart_727745 baseEnd_727745 := by
    simpa [prefixWord, tailWord_727745, baseEnd_727745] using wordTrace_append hprefix tailTrace_727745
  have hstable : (prefixWord ++ tailWord_727745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727745).length < 2 ^ (prefixWord ++ tailWord_727745).sum := by decide
  have hdescent : baseEnd_727745 < baseStart_727745 := by decide
  rcases family_descends (prefixWord ++ tailWord_727745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727801 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_727801 : Nat := 118140960795 + 727801 * 2 ^ 59
def prefixEnd_727801 : Nat := 4983230072969 + 3 ^ 40 * 727801 * 2
def baseEnd_727801 : Nat := 166094103921338759529071

theorem tailTrace_727801 : CollatzResearch.WordTrace tailWord_727801 prefixEnd_727801 166094103921338759529071 := by
  unfold tailWord_727801
  simp only [CollatzResearch.WordTrace]
  refine ⟨26545083236308750359999257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17696722157539166906666171 26545083236308750359999257)
  ·
    refine ⟨19908812427231562769999443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26545083236308750359999257 19908812427231562769999443)
    ·
      refine ⟨29863218640847344154999165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19908812427231562769999443 29863218640847344154999165)
      ·
        refine ⟨11198706990317754058124687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29863218640847344154999165 11198706990317754058124687)
        ·
          refine ⟨16798060485476631087187031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11198706990317754058124687 16798060485476631087187031)
          ·
            refine ⟨25197090728214946630780547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16798060485476631087187031 25197090728214946630780547)
            ·
              refine ⟨37795636092322419946170821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25197090728214946630780547 37795636092322419946170821)
              ·
                refine ⟨7086681767310453739907029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37795636092322419946170821 7086681767310453739907029)
                ·
                  refine ⟨166094103921338759529071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7086681767310453739907029 166094103921338759529071)
                  ·
                    rfl

theorem cell21_727801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_727801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727801 prefixEnd_727801 := by exact prefixLift 727801
  have htrace : WordTrace (prefixWord ++ tailWord_727801) baseStart_727801 baseEnd_727801 := by
    simpa [prefixWord, tailWord_727801, baseEnd_727801] using wordTrace_append hprefix tailTrace_727801
  have hstable : (prefixWord ++ tailWord_727801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727801).length < 2 ^ (prefixWord ++ tailWord_727801).sum := by decide
  have hdescent : baseEnd_727801 < baseStart_727801 := by decide
  rcases family_descends (prefixWord ++ tailWord_727801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727866 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_727866 : Nat := 118140960795 + 727866 * 2 ^ 59
def prefixEnd_727866 : Nat := 4983230072969 + 3 ^ 40 * 727866 * 2
def baseEnd_727866 : Nat := 166108937806913090945605

theorem tailTrace_727866 : CollatzResearch.WordTrace tailWord_727866 prefixEnd_727866 166108937806913090945605 := by
  unfold tailWord_727866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636863495268316615278863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17698302654048844307410301 6636863495268316615278863)
  ·
    refine ⟨9955295242902474922918295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6636863495268316615278863 9955295242902474922918295)
    ·
      refine ⟨14932942864353712384377443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9955295242902474922918295 14932942864353712384377443)
      ·
        refine ⟨22399414296530568576566165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14932942864353712384377443 22399414296530568576566165)
        ·
          refine ⟨1049972545149870402026539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22399414296530568576566165 1049972545149870402026539)
          ·
            refine ⟨1574958817724805603039809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049972545149870402026539 1574958817724805603039809)
            ·
              refine ⟨1181219113293604202279857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574958817724805603039809 1181219113293604202279857)
              ·
                refine ⟨885914334970203151709893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181219113293604202279857 885914334970203151709893)
                ·
                  refine ⟨166108937806913090945605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885914334970203151709893 166108937806913090945605)
                  ·
                    rfl

theorem cell21_727866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_727866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727866 prefixEnd_727866 := by exact prefixLift 727866
  have htrace : WordTrace (prefixWord ++ tailWord_727866) baseStart_727866 baseEnd_727866 := by
    simpa [prefixWord, tailWord_727866, baseEnd_727866] using wordTrace_append hprefix tailTrace_727866
  have hstable : (prefixWord ++ tailWord_727866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727866).length < 2 ^ (prefixWord ++ tailWord_727866).sum := by decide
  have hdescent : baseEnd_727866 < baseStart_727866 := by decide
  rcases family_descends (prefixWord ++ tailWord_727866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727911 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 3]
def baseStart_727911 : Nat := 118140960795 + 727911 * 2 ^ 59
def prefixEnd_727911 : Nat := 4983230072969 + 3 ^ 40 * 727911 * 2
def baseEnd_727911 : Nat := 166119207420003012695513

theorem tailTrace_727911 : CollatzResearch.WordTrace tailWord_727911 prefixEnd_727911 166119207420003012695513 := by
  unfold tailWord_727911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26549095265910239146503587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17699396843940159431002391 26549095265910239146503587)
  ·
    refine ⟨39823642898865358719755381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26549095265910239146503587 39823642898865358719755381)
    ·
      refine ⟨3733466521768627379977067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39823642898865358719755381 3733466521768627379977067)
      ·
        refine ⟨5600199782652941069965601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733466521768627379977067 5600199782652941069965601)
        ·
          refine ⟨4200149836989705802474201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600199782652941069965601 4200149836989705802474201)
          ·
            refine ⟨3150112377742279351855651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200149836989705802474201 3150112377742279351855651)
            ·
              refine ⟨4725168566613419027783477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150112377742279351855651 4725168566613419027783477)
              ·
                refine ⟨442984553120008033854701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4725168566613419027783477 442984553120008033854701)
                ·
                  refine ⟨166119207420003012695513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442984553120008033854701 166119207420003012695513)
                  ·
                    rfl

theorem cell21_727911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3].length) (baseStart_727911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727911 prefixEnd_727911 := by exact prefixLift 727911
  have htrace : WordTrace (prefixWord ++ tailWord_727911) baseStart_727911 baseEnd_727911 := by
    simpa [prefixWord, tailWord_727911, baseEnd_727911] using wordTrace_append hprefix tailTrace_727911
  have hstable : (prefixWord ++ tailWord_727911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727911).length < 2 ^ (prefixWord ++ tailWord_727911).sum := by decide
  have hdescent : baseEnd_727911 < baseStart_727911 := by decide
  rcases family_descends (prefixWord ++ tailWord_727911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727925 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_727925 : Nat := 118140960795 + 727925 * 2 ^ 59
def prefixEnd_727925 : Nat := 4983230072969 + 3 ^ 40 * 727925 * 2
def baseEnd_727925 : Nat := 166122402410742099462151

theorem tailTrace_727925 : CollatzResearch.WordTrace tailWord_727925 prefixEnd_727925 166122402410742099462151 := by
  unfold tailWord_727925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26549605887859519537513229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17699737258573013025008819 26549605887859519537513229)
  ·
    refine ⟨9956102207947319826567461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26549605887859519537513229 9956102207947319826567461)
    ·
      refine ⟨1866769163990122467481399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9956102207947319826567461 1866769163990122467481399)
      ·
        refine ⟨2800153745985183701222099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866769163990122467481399 2800153745985183701222099)
        ·
          refine ⟨4200230618977775551833149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800153745985183701222099 4200230618977775551833149)
          ·
            refine ⟨1575086482116665831937431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4200230618977775551833149 1575086482116665831937431)
            ·
              refine ⟨2362629723174998747906147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575086482116665831937431 2362629723174998747906147)
              ·
                refine ⟨3543944584762498121859221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362629723174998747906147 3543944584762498121859221)
                ·
                  refine ⟨166122402410742099462151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3543944584762498121859221 166122402410742099462151)
                  ·
                    rfl

theorem cell21_727925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_727925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727925 prefixEnd_727925 := by exact prefixLift 727925
  have htrace : WordTrace (prefixWord ++ tailWord_727925) baseStart_727925 baseEnd_727925 := by
    simpa [prefixWord, tailWord_727925, baseEnd_727925] using wordTrace_append hprefix tailTrace_727925
  have hstable : (prefixWord ++ tailWord_727925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727925).length < 2 ^ (prefixWord ++ tailWord_727925).sum := by decide
  have hdescent : baseEnd_727925 < baseStart_727925 := by decide
  rcases family_descends (prefixWord ++ tailWord_727925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728066 : List Nat := [3, 4, 1, 3, 1, 1, 3, 5]
def baseStart_728066 : Nat := 118140960795 + 728066 * 2 ^ 59
def prefixEnd_728066 : Nat := 4983230072969 + 3 ^ 40 * 728066 * 2
def baseEnd_728066 : Nat := 55384860177252395870621

theorem tailTrace_728066 : CollatzResearch.WordTrace tailWord_728066 prefixEnd_728066 55384860177252395870621 := by
  unfold tailWord_728066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638687145087175154599013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17703165720232467078930701 6638687145087175154599013)
  ·
    refine ⟨1244753839703845341487315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6638687145087175154599013 1244753839703845341487315)
    ·
      refine ⟨1867130759555768012230973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244753839703845341487315 1867130759555768012230973)
      ·
        refine ⟨700174034833413004586615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1867130759555768012230973 700174034833413004586615)
        ·
          refine ⟨1050261052250119506879923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700174034833413004586615 1050261052250119506879923)
          ·
            refine ⟨1575391578375179260319885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050261052250119506879923 1575391578375179260319885)
            ·
              refine ⟨590771841890692222619957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1575391578375179260319885 590771841890692222619957)
              ·
                refine ⟨55384860177252395870621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 590771841890692222619957 55384860177252395870621)
                ·
                  rfl

theorem cell21_728066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_728066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728066 prefixEnd_728066 := by exact prefixLift 728066
  have htrace : WordTrace (prefixWord ++ tailWord_728066) baseStart_728066 baseEnd_728066 := by
    simpa [prefixWord, tailWord_728066, baseEnd_728066] using wordTrace_append hprefix tailTrace_728066
  have hstable : (prefixWord ++ tailWord_728066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728066).length < 2 ^ (prefixWord ++ tailWord_728066).sum := by decide
  have hdescent : baseEnd_728066 < baseStart_728066 := by decide
  rcases family_descends (prefixWord ++ tailWord_728066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728156 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_728156 : Nat := 118140960795 + 728156 * 2 ^ 59
def prefixEnd_728156 : Nat := 4983230072969 + 3 ^ 40 * 728156 * 2
def baseEnd_728156 : Nat := 166175119757937031111679

theorem tailTrace_728156 : CollatzResearch.WordTrace tailWord_728156 prefixEnd_728156 166175119757937031111679 := by
  unfold tailWord_728156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13279015575011322994586161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17705354100015097326114881 13279015575011322994586161)
  ·
    refine ⟨9959261681258492245939621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13279015575011322994586161 9959261681258492245939621)
    ·
      refine ⟨1867361565235967296113679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9959261681258492245939621 1867361565235967296113679)
      ·
        refine ⟨2801042347853950944170519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867361565235967296113679 2801042347853950944170519)
        ·
          refine ⟨4201563521780926416255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801042347853950944170519 4201563521780926416255779)
          ·
            refine ⟨6302345282671389624383669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201563521780926416255779 6302345282671389624383669)
            ·
              refine ⟨590844870250442777285969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6302345282671389624383669 590844870250442777285969)
              ·
                refine ⟨443133652687832082964477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590844870250442777285969 443133652687832082964477)
                ·
                  refine ⟨166175119757937031111679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443133652687832082964477 166175119757937031111679)
                  ·
                    rfl

theorem cell21_728156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_728156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728156 prefixEnd_728156 := by exact prefixLift 728156
  have htrace : WordTrace (prefixWord ++ tailWord_728156) baseStart_728156 baseEnd_728156 := by
    simpa [prefixWord, tailWord_728156, baseEnd_728156] using wordTrace_append hprefix tailTrace_728156
  have hstable : (prefixWord ++ tailWord_728156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728156).length < 2 ^ (prefixWord ++ tailWord_728156).sum := by decide
  have hdescent : baseEnd_728156 < baseStart_728156 := by decide
  rcases family_descends (prefixWord ++ tailWord_728156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728167 : List Nat := [1, 1, 5, 1, 1, 4, 2, 6]
def baseStart_728167 : Nat := 118140960795 + 728167 * 2 ^ 59
def prefixEnd_728167 : Nat := 4983230072969 + 3 ^ 40 * 728167 * 2
def baseEnd_728167 : Nat := 55392543369267818809441

theorem tailTrace_728167 : CollatzResearch.WordTrace tailWord_728167 prefixEnd_728167 55392543369267818809441 := by
  unfold tailWord_728167
  simp only [CollatzResearch.WordTrace]
  refine ⟨26558432352982794867822755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17705621568655196578548503 26558432352982794867822755)
  ·
    refine ⟨39837648529474192301734133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26558432352982794867822755 39837648529474192301734133)
    ·
      refine ⟨3734779549638205528287575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39837648529474192301734133 3734779549638205528287575)
      ·
        refine ⟨5602169324457308292431363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734779549638205528287575 5602169324457308292431363)
        ·
          refine ⟨8403253986685962438647045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5602169324457308292431363 8403253986685962438647045)
          ·
            refine ⟨1575610122503617957246321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8403253986685962438647045 1575610122503617957246321)
            ·
              refine ⟨1181707591877713467934741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575610122503617957246321 1181707591877713467934741)
              ·
                refine ⟨55392543369267818809441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1181707591877713467934741 55392543369267818809441)
                ·
                  rfl

theorem cell21_728167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_728167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728167 prefixEnd_728167 := by exact prefixLift 728167
  have htrace : WordTrace (prefixWord ++ tailWord_728167) baseStart_728167 baseEnd_728167 := by
    simpa [prefixWord, tailWord_728167, baseEnd_728167] using wordTrace_append hprefix tailTrace_728167
  have hstable : (prefixWord ++ tailWord_728167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728167).length < 2 ^ (prefixWord ++ tailWord_728167).sum := by decide
  have hdescent : baseEnd_728167 < baseStart_728167 := by decide
  rcases family_descends (prefixWord ++ tailWord_728167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728170 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_728170 : Nat := 118140960795 + 728170 * 2 ^ 59
def prefixEnd_728170 : Nat := 4983230072969 + 3 ^ 40 * 728170 * 2
def baseEnd_728170 : Nat := 166178314748676117878317

theorem tailTrace_728170 : CollatzResearch.WordTrace tailWord_728170 prefixEnd_728170 166178314748676117878317 := by
  unfold tailWord_728170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639635442992981595045491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17705694514647950920121309 6639635442992981595045491)
  ·
    refine ⟨9959453164489472392568237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639635442992981595045491 9959453164489472392568237)
    ·
      refine ⟨3734794936683552147213089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9959453164489472392568237 3734794936683552147213089)
      ·
        refine ⟨2801096202512664110409817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3734794936683552147213089 2801096202512664110409817)
        ·
          refine ⟨2100822151884498082807363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2801096202512664110409817 2100822151884498082807363)
          ·
            refine ⟨3151233227826747124211045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100822151884498082807363 3151233227826747124211045)
            ·
              refine ⟨590856230217515085789571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3151233227826747124211045 590856230217515085789571)
              ·
                refine ⟨886284345326272628684357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590856230217515085789571 886284345326272628684357)
                ·
                  refine ⟨166178314748676117878317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886284345326272628684357 166178314748676117878317)
                  ·
                    rfl

theorem cell21_728170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_728170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728170 prefixEnd_728170 := by exact prefixLift 728170
  have htrace : WordTrace (prefixWord ++ tailWord_728170) baseStart_728170 baseEnd_728170 := by
    simpa [prefixWord, tailWord_728170, baseEnd_728170] using wordTrace_append hprefix tailTrace_728170
  have hstable : (prefixWord ++ tailWord_728170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728170).length < 2 ^ (prefixWord ++ tailWord_728170).sum := by decide
  have hdescent : baseEnd_728170 < baseStart_728170 := by decide
  rcases family_descends (prefixWord ++ tailWord_728170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728215 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 3]
def baseStart_728215 : Nat := 118140960795 + 728215 * 2 ^ 59
def prefixEnd_728215 : Nat := 4983230072969 + 3 ^ 40 * 728215 * 2
def baseEnd_728215 : Nat := 166188584361766039628225

theorem tailTrace_728215 : CollatzResearch.WordTrace tailWord_728215 prefixEnd_728215 166188584361766039628225 := by
  unfold tailWord_728215
  simp only [CollatzResearch.WordTrace]
  refine ⟨26560183056808899065570099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17706788704539266043713399 26560183056808899065570099)
  ·
    refine ⟨39840274585213348598355149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26560183056808899065570099 39840274585213348598355149)
    ·
      refine ⟨14940102969455005724383181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39840274585213348598355149 14940102969455005724383181)
      ·
        refine ⟨5602538613545627146643693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14940102969455005724383181 5602538613545627146643693)
        ·
          refine ⟨2100951980079610179991385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5602538613545627146643693 2100951980079610179991385)
          ·
            refine ⟨1575713985059707634993539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100951980079610179991385 1575713985059707634993539)
            ·
              refine ⟨2363570977589561452490309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575713985059707634993539 2363570977589561452490309)
              ·
                refine ⟨443169558298042772341933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2363570977589561452490309 443169558298042772341933)
                ·
                  refine ⟨166188584361766039628225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443169558298042772341933 166188584361766039628225)
                  ·
                    rfl

theorem cell21_728215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3].length) (baseStart_728215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728215 prefixEnd_728215 := by exact prefixLift 728215
  have htrace : WordTrace (prefixWord ++ tailWord_728215) baseStart_728215 baseEnd_728215 := by
    simpa [prefixWord, tailWord_728215, baseEnd_728215] using wordTrace_append hprefix tailTrace_728215
  have hstable : (prefixWord ++ tailWord_728215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728215).length < 2 ^ (prefixWord ++ tailWord_728215).sum := by decide
  have hdescent : baseEnd_728215 < baseStart_728215 := by decide
  rcases family_descends (prefixWord ++ tailWord_728215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728274 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_728274 : Nat := 118140960795 + 728274 * 2 ^ 59
def prefixEnd_728274 : Nat := 4983230072969 + 3 ^ 40 * 728274 * 2
def baseEnd_728274 : Nat := 166202048965595048144771

theorem tailTrace_728274 : CollatzResearch.WordTrace tailWord_728274 prefixEnd_728274 166202048965595048144771 := by
  unfold tailWord_728274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640583740898788035491969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17708223309063434761311917 6640583740898788035491969)
  ·
    refine ⟨4980437805674091026618977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640583740898788035491969 4980437805674091026618977)
    ·
      refine ⟨3735328354255568269964233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4980437805674091026618977 3735328354255568269964233)
      ·
        refine ⟨2801496265691676202473175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3735328354255568269964233 2801496265691676202473175)
        ·
          refine ⟨4202244398537514303709763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801496265691676202473175 4202244398537514303709763)
          ·
            refine ⟨6303366597806271455564645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202244398537514303709763 6303366597806271455564645)
            ·
              refine ⟨1181881237088675897918371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6303366597806271455564645 1181881237088675897918371)
              ·
                refine ⟨1772821855633013846877557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181881237088675897918371 1772821855633013846877557)
                ·
                  refine ⟨166202048965595048144771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1772821855633013846877557 166202048965595048144771)
                  ·
                    rfl

theorem cell21_728274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_728274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728274 prefixEnd_728274 := by exact prefixLift 728274
  have htrace : WordTrace (prefixWord ++ tailWord_728274) baseStart_728274 baseEnd_728274 := by
    simpa [prefixWord, tailWord_728274, baseEnd_728274] using wordTrace_append hprefix tailTrace_728274
  have hstable : (prefixWord ++ tailWord_728274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728274).length < 2 ^ (prefixWord ++ tailWord_728274).sum := by decide
  have hdescent : baseEnd_728274 < baseStart_728274 := by decide
  rcases family_descends (prefixWord ++ tailWord_728274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728488 : List Nat := [2, 1, 6, 1, 2, 2, 7]
def baseStart_728488 : Nat := 118140960795 + 728488 * 2 ^ 59
def prefixEnd_728488 : Nat := 4983230072969 + 3 ^ 40 * 728488 * 2
def baseEnd_728488 : Nat := 18472320742353136841963

theorem tailTrace_728488 : CollatzResearch.WordTrace tailWord_728488 prefixEnd_728488 18472320742353136841963 := by
  unfold tailWord_728488
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285070092409933345129059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17713426789879911126838745 13285070092409933345129059)
  ·
    refine ⟨19927605138614900017693589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285070092409933345129059 19927605138614900017693589)
    ·
      refine ⟨934106490872573438329387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19927605138614900017693589 934106490872573438329387)
      ·
        refine ⟨1401159736308860157494081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934106490872573438329387 1401159736308860157494081)
        ·
          refine ⟨1050869802231645118120561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401159736308860157494081 1050869802231645118120561)
          ·
            refine ⟨788152351673733838590421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050869802231645118120561 788152351673733838590421)
            ·
              refine ⟨18472320742353136841963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 788152351673733838590421 18472320742353136841963)
              ·
                rfl

theorem cell21_728488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 7].length) (baseStart_728488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728488 prefixEnd_728488 := by exact prefixLift 728488
  have htrace : WordTrace (prefixWord ++ tailWord_728488) baseStart_728488 baseEnd_728488 := by
    simpa [prefixWord, tailWord_728488, baseEnd_728488] using wordTrace_append hprefix tailTrace_728488
  have hstable : (prefixWord ++ tailWord_728488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728488).length < 2 ^ (prefixWord ++ tailWord_728488).sum := by decide
  have hdescent : baseEnd_728488 < baseStart_728488 := by decide
  rcases family_descends (prefixWord ++ tailWord_728488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728544 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_728544 : Nat := 118140960795 + 728544 * 2 ^ 59
def prefixEnd_728544 : Nat := 4983230072969 + 3 ^ 40 * 728544 * 2
def baseEnd_728544 : Nat := 166263666644134578644219

theorem tailTrace_728544 : CollatzResearch.WordTrace tailWord_728544 prefixEnd_728544 166263666644134578644219 := by
  unfold tailWord_728544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286091336308494127148343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17714788448411325502864457 13286091336308494127148343)
  ·
    refine ⟨19929137004462741190722515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13286091336308494127148343 19929137004462741190722515)
    ·
      refine ⟨29893705506694111786083773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19929137004462741190722515 29893705506694111786083773)
      ·
        refine ⟨11210139565010291919781415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29893705506694111786083773 11210139565010291919781415)
        ·
          refine ⟨16815209347515437879672123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210139565010291919781415 16815209347515437879672123)
          ·
            refine ⟨25222814021273156819508185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16815209347515437879672123 25222814021273156819508185)
            ·
              refine ⟨18917110515954867614631139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25222814021273156819508185 18917110515954867614631139)
              ·
                refine ⟨28375665773932301421946709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18917110515954867614631139 28375665773932301421946709)
                ·
                  refine ⟨166263666644134578644219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28375665773932301421946709 166263666644134578644219)
                  ·
                    rfl

theorem cell21_728544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_728544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728544 prefixEnd_728544 := by exact prefixLift 728544
  have htrace : WordTrace (prefixWord ++ tailWord_728544) baseStart_728544 baseEnd_728544 := by
    simpa [prefixWord, tailWord_728544, baseEnd_728544] using wordTrace_append hprefix tailTrace_728544
  have hstable : (prefixWord ++ tailWord_728544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728544).length < 2 ^ (prefixWord ++ tailWord_728544).sum := by decide
  have hdescent : baseEnd_728544 < baseStart_728544 := by decide
  rcases family_descends (prefixWord ++ tailWord_728544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728578 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_728578 : Nat := 118140960795 + 728578 * 2 ^ 59
def prefixEnd_728578 : Nat := 4983230072969 + 3 ^ 40 * 728578 * 2
def baseEnd_728578 : Nat := 166271425907358075077483

theorem tailTrace_728578 : CollatzResearch.WordTrace tailWord_728578 prefixEnd_728578 166271425907358075077483 := by
  unfold tailWord_728578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643355688623453015258597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17715615169662541374022925 6643355688623453015258597)
  ·
    refine ⟨1245629191616897440360987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6643355688623453015258597 1245629191616897440360987)
    ·
      refine ⟨1868443787425346160541481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245629191616897440360987 1868443787425346160541481)
      ·
        refine ⟨1401332840569009620406111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1868443787425346160541481 1401332840569009620406111)
        ·
          refine ⟨2101999260853514430609167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401332840569009620406111 2101999260853514430609167)
          ·
            refine ⟨3152998891280271645913751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101999260853514430609167 3152998891280271645913751)
            ·
              refine ⟨4729498336920407468870627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152998891280271645913751 4729498336920407468870627)
              ·
                refine ⟨7094247505380611203305941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729498336920407468870627 7094247505380611203305941)
                ·
                  refine ⟨166271425907358075077483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7094247505380611203305941 166271425907358075077483)
                  ·
                    rfl

theorem cell21_728578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_728578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728578 prefixEnd_728578 := by exact prefixLift 728578
  have htrace : WordTrace (prefixWord ++ tailWord_728578) baseStart_728578 baseEnd_728578 := by
    simpa [prefixWord, tailWord_728578, baseEnd_728578] using wordTrace_append hprefix tailTrace_728578
  have hstable : (prefixWord ++ tailWord_728578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728578).length < 2 ^ (prefixWord ++ tailWord_728578).sum := by decide
  have hdescent : baseEnd_728578 < baseStart_728578 := by decide
  rcases family_descends (prefixWord ++ tailWord_728578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728609 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 4]
def baseStart_728609 : Nat := 118140960795 + 728609 * 2 ^ 59
def prefixEnd_728609 : Nat := 4983230072969 + 3 ^ 40 * 728609 * 2
def baseEnd_728609 : Nat := 166278500529708910060753

theorem tailTrace_728609 : CollatzResearch.WordTrace tailWord_728609 prefixEnd_728609 166278500529708910060753 := by
  unfold tailWord_728609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574553417381504355412881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17716368944921002903608587 26574553417381504355412881)
  ·
    refine ⟨19930915063036128266559661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26574553417381504355412881 19930915063036128266559661)
    ·
      refine ⟨7474093148638548099959873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19930915063036128266559661 7474093148638548099959873)
      ·
        refine ⟨5605569861478911074969905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7474093148638548099959873 5605569861478911074969905)
        ·
          refine ⟨4204177396109183306227429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605569861478911074969905 4204177396109183306227429)
          ·
            refine ⟨788283261770471869917643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4204177396109183306227429 788283261770471869917643)
            ·
              refine ⟨1182424892655707804876465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788283261770471869917643 1182424892655707804876465)
              ·
                refine ⟨886818669491780853657349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182424892655707804876465 886818669491780853657349)
                ·
                  refine ⟨166278500529708910060753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886818669491780853657349 166278500529708910060753)
                  ·
                    rfl

theorem cell21_728609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_728609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728609 prefixEnd_728609 := by exact prefixLift 728609
  have htrace : WordTrace (prefixWord ++ tailWord_728609) baseStart_728609 baseEnd_728609 := by
    simpa [prefixWord, tailWord_728609, baseEnd_728609] using wordTrace_append hprefix tailTrace_728609
  have hstable : (prefixWord ++ tailWord_728609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728609).length < 2 ^ (prefixWord ++ tailWord_728609).sum := by decide
  have hdescent : baseEnd_728609 < baseStart_728609 := by decide
  rcases family_descends (prefixWord ++ tailWord_728609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728646 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_728646 : Nat := 118140960795 + 728646 * 2 ^ 59
def prefixEnd_728646 : Nat := 4983230072969 + 3 ^ 40 * 728646 * 2
def baseEnd_728646 : Nat := 166286944433805067944011

theorem tailTrace_728646 : CollatzResearch.WordTrace tailWord_728646 prefixEnd_728646 166286944433805067944011 := by
  unfold tailWord_728646
  simp only [CollatzResearch.WordTrace]
  refine ⟨830496966195233114828431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17717268612164973116339861 830496966195233114828431)
  ·
    refine ⟨1245745449292849672242647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830496966195233114828431 1245745449292849672242647)
    ·
      refine ⟨1868618173939274508363971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245745449292849672242647 1868618173939274508363971)
      ·
        refine ⟨2802927260908911762545957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868618173939274508363971 2802927260908911762545957)
        ·
          refine ⟨525548861420420955477367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2802927260908911762545957 525548861420420955477367)
          ·
            refine ⟨788323292130631433216051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525548861420420955477367 788323292130631433216051)
            ·
              refine ⟨1182484938195947149824077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788323292130631433216051 1182484938195947149824077)
              ·
                refine ⟨443431851823480181184029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182484938195947149824077 443431851823480181184029)
                ·
                  refine ⟨166286944433805067944011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443431851823480181184029 166286944433805067944011)
                  ·
                    rfl

theorem cell21_728646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_728646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728646 prefixEnd_728646 := by exact prefixLift 728646
  have htrace : WordTrace (prefixWord ++ tailWord_728646) baseStart_728646 baseEnd_728646 := by
    simpa [prefixWord, tailWord_728646, baseEnd_728646] using wordTrace_append hprefix tailTrace_728646
  have hstable : (prefixWord ++ tailWord_728646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728646).length < 2 ^ (prefixWord ++ tailWord_728646).sum := by decide
  have hdescent : baseEnd_728646 < baseStart_728646 := by decide
  rcases family_descends (prefixWord ++ tailWord_728646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728668 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_728668 : Nat := 118140960795 + 728668 * 2 ^ 59
def prefixEnd_728668 : Nat := 4983230072969 + 3 ^ 40 * 728668 * 2
def baseEnd_728668 : Nat := 166291965133537918577299

theorem tailTrace_728668 : CollatzResearch.WordTrace tailWord_728668 prefixEnd_728668 166291965133537918577299 := by
  unfold tailWord_728668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13288352662083878715905329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17717803549445171621207105 13288352662083878715905329)
  ·
    refine ⟨9966264496562909036928997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13288352662083878715905329 9966264496562909036928997)
    ·
      refine ⟨1868674593105545444424187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9966264496562909036928997 1868674593105545444424187)
      ·
        refine ⟨2803011889658318166636281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868674593105545444424187 2803011889658318166636281)
        ·
          refine ⟨2102258917243738624977211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803011889658318166636281 2102258917243738624977211)
          ·
            refine ⟨3153388375865607937465817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102258917243738624977211 3153388375865607937465817)
            ·
              refine ⟨2365041281899205953099363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153388375865607937465817 2365041281899205953099363)
              ·
                refine ⟨3547561922848808929649045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365041281899205953099363 3547561922848808929649045)
                ·
                  refine ⟨166291965133537918577299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3547561922848808929649045 166291965133537918577299)
                  ·
                    rfl

theorem cell21_728668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_728668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728668 prefixEnd_728668 := by exact prefixLift 728668
  have htrace : WordTrace (prefixWord ++ tailWord_728668) baseStart_728668 baseEnd_728668 := by
    simpa [prefixWord, tailWord_728668, baseEnd_728668] using wordTrace_append hprefix tailTrace_728668
  have hstable : (prefixWord ++ tailWord_728668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728668).length < 2 ^ (prefixWord ++ tailWord_728668).sum := by decide
  have hdescent : baseEnd_728668 < baseStart_728668 := by decide
  rcases family_descends (prefixWord ++ tailWord_728668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728682 : List Nat := [3, 1, 3, 2, 1, 2, 1, 8]
def baseStart_728682 : Nat := 118140960795 + 728682 * 2 ^ 59
def prefixEnd_728682 : Nat := 4983230072969 + 3 ^ 40 * 728682 * 2
def baseEnd_728682 : Nat := 55431720041425668447979

theorem tailTrace_728682 : CollatzResearch.WordTrace tailWord_728682 prefixEnd_728682 55431720041425668447979 := by
  unfold tailWord_728682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644303986529259455705075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17718143964078025215213533 6644303986529259455705075)
  ·
    refine ⟨9966455979793889183557613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644303986529259455705075 9966455979793889183557613)
    ·
      refine ⟨3737420992422708443834105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9966455979793889183557613 3737420992422708443834105)
      ·
        refine ⟨2803065744317031332875579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737420992422708443834105 2803065744317031332875579)
        ·
          refine ⟨4204598616475546999313369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803065744317031332875579 4204598616475546999313369)
          ·
            refine ⟨3153448962356660249485027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204598616475546999313369 3153448962356660249485027)
            ·
              refine ⟨4730173443534990374227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153448962356660249485027 4730173443534990374227541)
              ·
                refine ⟨55431720041425668447979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4730173443534990374227541 55431720041425668447979)
                ·
                  rfl

theorem cell21_728682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_728682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728682 prefixEnd_728682 := by exact prefixLift 728682
  have htrace : WordTrace (prefixWord ++ tailWord_728682) baseStart_728682 baseEnd_728682 := by
    simpa [prefixWord, tailWord_728682, baseEnd_728682] using wordTrace_append hprefix tailTrace_728682
  have hstable : (prefixWord ++ tailWord_728682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728682).length < 2 ^ (prefixWord ++ tailWord_728682).sum := by decide
  have hdescent : baseEnd_728682 < baseStart_728682 := by decide
  rcases family_descends (prefixWord ++ tailWord_728682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728685 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_728685 : Nat := 118140960795 + 728685 * 2 ^ 59
def prefixEnd_728685 : Nat := 4983230072969 + 3 ^ 40 * 728685 * 2
def baseEnd_728685 : Nat := 166295844765149666793931

theorem tailTrace_728685 : CollatzResearch.WordTrace tailWord_728685 prefixEnd_728685 166295844765149666793931 := by
  unfold tailWord_728685
  simp only [CollatzResearch.WordTrace]
  refine ⟨26577325365106169335179509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17718216910070779556786339 26577325365106169335179509)
  ·
    refine ⟨2491624252978703375173079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26577325365106169335179509 2491624252978703375173079)
    ·
      refine ⟨3737436379468055062759619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491624252978703375173079 3737436379468055062759619)
      ·
        refine ⟨5606154569202082594139429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737436379468055062759619 5606154569202082594139429)
        ·
          refine ⟨1051153981725390486401143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5606154569202082594139429 1051153981725390486401143)
          ·
            refine ⟨1576730972588085729601715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051153981725390486401143 1576730972588085729601715)
            ·
              refine ⟨2365096458882128594402573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576730972588085729601715 2365096458882128594402573)
              ·
                refine ⟨886911172080798222900965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365096458882128594402573 886911172080798222900965)
                ·
                  refine ⟨166295844765149666793931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886911172080798222900965 166295844765149666793931)
                  ·
                    rfl

theorem cell21_728685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_728685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728685 prefixEnd_728685 := by exact prefixLift 728685
  have htrace : WordTrace (prefixWord ++ tailWord_728685) baseStart_728685 baseEnd_728685 := by
    simpa [prefixWord, tailWord_728685, baseEnd_728685] using wordTrace_append hprefix tailTrace_728685
  have hstable : (prefixWord ++ tailWord_728685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728685).length < 2 ^ (prefixWord ++ tailWord_728685).sum := by decide
  have hdescent : baseEnd_728685 < baseStart_728685 := by decide
  rcases family_descends (prefixWord ++ tailWord_728685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728778 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_728778 : Nat := 118140960795 + 728778 * 2 ^ 59
def prefixEnd_728778 : Nat := 4983230072969 + 3 ^ 40 * 728778 * 2
def baseEnd_728778 : Nat := 166317068632202171743741

theorem tailTrace_728778 : CollatzResearch.WordTrace tailWord_728778 prefixEnd_728778 166317068632202171743741 := by
  unfold tailWord_728778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645179338442311554578747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17720478235846164145543325 6645179338442311554578747)
  ·
    refine ⟨9967769007663467331868121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6645179338442311554578747 9967769007663467331868121)
    ·
      refine ⟨7475826755747600498901091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9967769007663467331868121 7475826755747600498901091)
      ·
        refine ⟨11213740133621400748351637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475826755747600498901091 11213740133621400748351637)
        ·
          refine ⟨525644068763503160078983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11213740133621400748351637 525644068763503160078983)
          ·
            refine ⟨788466103145254740118475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525644068763503160078983 788466103145254740118475)
            ·
              refine ⟨1182699154717882110177713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788466103145254740118475 1182699154717882110177713)
              ·
                refine ⟨887024366038411582633285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182699154717882110177713 887024366038411582633285)
                ·
                  refine ⟨166317068632202171743741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887024366038411582633285 166317068632202171743741)
                  ·
                    rfl

theorem cell21_728778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_728778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728778 prefixEnd_728778 := by exact prefixLift 728778
  have htrace : WordTrace (prefixWord ++ tailWord_728778) baseStart_728778 baseEnd_728778 := by
    simpa [prefixWord, tailWord_728778, baseEnd_728778] using wordTrace_append hprefix tailTrace_728778
  have hstable : (prefixWord ++ tailWord_728778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728778).length < 2 ^ (prefixWord ++ tailWord_728778).sum := by decide
  have hdescent : baseEnd_728778 < baseStart_728778 := by decide
  rcases family_descends (prefixWord ++ tailWord_728778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728899 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 3]
def baseStart_728899 : Nat := 118140960795 + 728899 * 2 ^ 59
def prefixEnd_728899 : Nat := 4983230072969 + 3 ^ 40 * 728899 * 2
def baseEnd_728899 : Nat := 166344682480732850226827

theorem tailTrace_728899 : CollatzResearch.WordTrace tailWord_728899 prefixEnd_728899 166344682480732850226827 := by
  unfold tailWord_728899
  simp only [CollatzResearch.WordTrace]
  refine ⟨26585130586330883883469751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17723420390887255922313167 26585130586330883883469751)
  ·
    refine ⟨39877695879496325825204627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26585130586330883883469751 39877695879496325825204627)
    ·
      refine ⟨59816543819244488737806941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39877695879496325825204627 59816543819244488737806941)
      ·
        refine ⟨22431203932216683276677603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59816543819244488737806941 22431203932216683276677603)
        ·
          refine ⟨33646805898325024915016405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22431203932216683276677603 33646805898325024915016405)
          ·
            refine ⟨788597013241992771445697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33646805898325024915016405 788597013241992771445697)
            ·
              refine ⟨591447759931494578584273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788597013241992771445697 591447759931494578584273)
              ·
                refine ⟨443585819948620933938205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591447759931494578584273 443585819948620933938205)
                ·
                  refine ⟨166344682480732850226827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443585819948620933938205 166344682480732850226827)
                  ·
                    rfl

theorem cell21_728899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3].length) (baseStart_728899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728899 prefixEnd_728899 := by exact prefixLift 728899
  have htrace : WordTrace (prefixWord ++ tailWord_728899) baseStart_728899 baseEnd_728899 := by
    simpa [prefixWord, tailWord_728899, baseEnd_728899] using wordTrace_append hprefix tailTrace_728899
  have hstable : (prefixWord ++ tailWord_728899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728899).length < 2 ^ (prefixWord ++ tailWord_728899).sum := by decide
  have hdescent : baseEnd_728899 < baseStart_728899 := by decide
  rcases family_descends (prefixWord ++ tailWord_728899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728958 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_728958 : Nat := 118140960795 + 728958 * 2 ^ 59
def prefixEnd_728958 : Nat := 4983230072969 + 3 ^ 40 * 728958 * 2
def baseEnd_728958 : Nat := 166358147084561858743373

theorem tailTrace_728958 : CollatzResearch.WordTrace tailWord_728958 prefixEnd_728958 166358147084561858743373 := by
  unfold tailWord_728958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323410311639642119983441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17724854995411424639911685 3323410311639642119983441)
  ·
    refine ⟨2492557733729731589987581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3323410311639642119983441 2492557733729731589987581)
    ·
      refine ⟨934709150148649346245343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2492557733729731589987581 934709150148649346245343)
      ·
        refine ⟨1402063725222974019368015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934709150148649346245343 1402063725222974019368015)
        ·
          refine ⟨2103095587834461029052023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402063725222974019368015 2103095587834461029052023)
          ·
            refine ⟨3154643381751691543578035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103095587834461029052023 3154643381751691543578035)
            ·
              refine ⟨4731965072627537315367053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154643381751691543578035 4731965072627537315367053)
              ·
                refine ⟨1774486902235326493262645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731965072627537315367053 1774486902235326493262645)
                ·
                  refine ⟨166358147084561858743373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1774486902235326493262645 166358147084561858743373)
                  ·
                    rfl

theorem cell21_728958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_728958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728958 prefixEnd_728958 := by exact prefixLift 728958
  have htrace : WordTrace (prefixWord ++ tailWord_728958) baseStart_728958 baseEnd_728958 := by
    simpa [prefixWord, tailWord_728958, baseEnd_728958] using wordTrace_append hprefix tailTrace_728958
  have hstable : (prefixWord ++ tailWord_728958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728958).length < 2 ^ (prefixWord ++ tailWord_728958).sum := by decide
  have hdescent : baseEnd_728958 < baseStart_728958 := by decide
  rcases family_descends (prefixWord ++ tailWord_728958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728969 : List Nat := [1, 2, 1, 1, 5, 1, 2, 8]
def baseStart_728969 : Nat := 118140960795 + 728969 * 2 ^ 59
def prefixEnd_728969 : Nat := 4983230072969 + 3 ^ 40 * 728969 * 2
def baseEnd_728969 : Nat := 55453552478142761353339

theorem tailTrace_728969 : CollatzResearch.WordTrace tailWord_728969 prefixEnd_728969 55453552478142761353339 := by
  unfold tailWord_728969
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587683696077285838517961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17725122464051523892345307 26587683696077285838517961)
  ·
    refine ⟨19940762772057964378888471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26587683696077285838517961 19940762772057964378888471)
    ·
      refine ⟨29911144158086946568332707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19940762772057964378888471 29911144158086946568332707)
      ·
        refine ⟨44866716237130419852499061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29911144158086946568332707 44866716237130419852499061)
        ·
          refine ⟨4206254647230976861171787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44866716237130419852499061 4206254647230976861171787)
          ·
            refine ⟨6309381970846465291757681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206254647230976861171787 6309381970846465291757681)
            ·
              refine ⟨4732036478134848968818261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309381970846465291757681 4732036478134848968818261)
              ·
                refine ⟨55453552478142761353339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4732036478134848968818261 55453552478142761353339)
                ·
                  rfl

theorem cell21_728969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_728969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728969 prefixEnd_728969 := by exact prefixLift 728969
  have htrace : WordTrace (prefixWord ++ tailWord_728969) baseStart_728969 baseEnd_728969 := by
    simpa [prefixWord, tailWord_728969, baseEnd_728969] using wordTrace_append hprefix tailTrace_728969
  have hstable : (prefixWord ++ tailWord_728969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728969).length < 2 ^ (prefixWord ++ tailWord_728969).sum := by decide
  have hdescent : baseEnd_728969 < baseStart_728969 := by decide
  rcases family_descends (prefixWord ++ tailWord_728969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728986 : List Nat := [3, 1, 1, 4, 2, 2, 1, 7]
def baseStart_728986 : Nat := 118140960795 + 728986 * 2 ^ 59
def prefixEnd_728986 : Nat := 4983230072969 + 3 ^ 40 * 728986 * 2
def baseEnd_728986 : Nat := 55454845688680010758883

theorem tailTrace_728986 : CollatzResearch.WordTrace tailWord_728986 prefixEnd_728986 55454845688680010758883 := by
  unfold tailWord_728986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647075934253924435471703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17725535824677131827924541 6647075934253924435471703)
  ·
    refine ⟨9970613901380886653207555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6647075934253924435471703 9970613901380886653207555)
    ·
      refine ⟨14955920852071329979811333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9970613901380886653207555 14955920852071329979811333)
      ·
        refine ⟨2804235159763374371214625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14955920852071329979811333 2804235159763374371214625)
        ·
          refine ⟨2103176369822530778410969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2804235159763374371214625 2103176369822530778410969)
          ·
            refine ⟨1577382277366898083808227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2103176369822530778410969 1577382277366898083808227)
            ·
              refine ⟨2366073416050347125712341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577382277366898083808227 2366073416050347125712341)
              ·
                refine ⟨55454845688680010758883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2366073416050347125712341 55454845688680010758883)
                ·
                  rfl

theorem cell21_728986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_728986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_728986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_728986 prefixEnd_728986 := by exact prefixLift 728986
  have htrace : WordTrace (prefixWord ++ tailWord_728986) baseStart_728986 baseEnd_728986 := by
    simpa [prefixWord, tailWord_728986, baseEnd_728986] using wordTrace_append hprefix tailTrace_728986
  have hstable : (prefixWord ++ tailWord_728986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728986).length < 2 ^ (prefixWord ++ tailWord_728986).sum := by decide
  have hdescent : baseEnd_728986 < baseStart_728986 := by decide
  rcases family_descends (prefixWord ++ tailWord_728986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729124 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_729124 : Nat := 118140960795 + 729124 * 2 ^ 59
def prefixEnd_729124 : Nat := 4983230072969 + 3 ^ 40 * 729124 * 2
def baseEnd_729124 : Nat := 166396030546182458976367

theorem tailTrace_729124 : CollatzResearch.WordTrace tailWord_729124 prefixEnd_729124 166396030546182458976367 := by
  unfold tailWord_729124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296668505257873655205213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17728891340343831540273617 13296668505257873655205213)
  ·
    refine ⟨4986250689471702620701955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13296668505257873655205213 4986250689471702620701955)
    ·
      refine ⟨7479376034207553931052933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986250689471702620701955 7479376034207553931052933)
      ·
        refine ⟨1402383006413916362072425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7479376034207553931052933 1402383006413916362072425)
        ·
          refine ⟨1051787254810437271554319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402383006413916362072425 1051787254810437271554319)
          ·
            refine ⟨1577680882215655907331479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051787254810437271554319 1577680882215655907331479)
            ·
              refine ⟨2366521323323483860997219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577680882215655907331479 2366521323323483860997219)
              ·
                refine ⟨3549781984985225791495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366521323323483860997219 3549781984985225791495829)
                ·
                  refine ⟨166396030546182458976367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3549781984985225791495829 166396030546182458976367)
                  ·
                    rfl

theorem cell21_729124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_729124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729124 prefixEnd_729124 := by exact prefixLift 729124
  have htrace : WordTrace (prefixWord ++ tailWord_729124) baseStart_729124 baseEnd_729124 := by
    simpa [prefixWord, tailWord_729124, baseEnd_729124] using wordTrace_append hprefix tailTrace_729124
  have hstable : (prefixWord ++ tailWord_729124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729124).length < 2 ^ (prefixWord ++ tailWord_729124).sum := by decide
  have hdescent : baseEnd_729124 < baseStart_729124 := by decide
  rcases family_descends (prefixWord ++ tailWord_729124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729152 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_729152 : Nat := 118140960795 + 729152 * 2 ^ 59
def prefixEnd_729152 : Nat := 4983230072969 + 3 ^ 40 * 729152 * 2
def baseEnd_729152 : Nat := 166402420527660632509643

theorem tailTrace_729152 : CollatzResearch.WordTrace tailWord_729152 prefixEnd_729152 166402420527660632509643 := by
  unfold tailWord_729152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13297179127207154046214855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17729572169609538728286473 13297179127207154046214855)
  ·
    refine ⟨19945768690810731069322283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13297179127207154046214855 19945768690810731069322283)
    ·
      refine ⟨29918653036216096603983425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19945768690810731069322283 29918653036216096603983425)
      ·
        refine ⟨22438989777162072452987569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29918653036216096603983425 22438989777162072452987569)
        ·
          refine ⟨16829242332871554339740677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22438989777162072452987569 16829242332871554339740677)
          ·
            refine ⟨3155482937413416438701377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16829242332871554339740677 3155482937413416438701377)
            ·
              refine ⟨2366612203060062329026033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155482937413416438701377 2366612203060062329026033)
              ·
                refine ⟨1774959152295046746769525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366612203060062329026033 1774959152295046746769525)
                ·
                  refine ⟨166402420527660632509643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1774959152295046746769525 166402420527660632509643)
                  ·
                    rfl

theorem cell21_729152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_729152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729152 prefixEnd_729152 := by exact prefixLift 729152
  have htrace : WordTrace (prefixWord ++ tailWord_729152) baseStart_729152 baseEnd_729152 := by
    simpa [prefixWord, tailWord_729152, baseEnd_729152] using wordTrace_append hprefix tailTrace_729152
  have hstable : (prefixWord ++ tailWord_729152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729152).length < 2 ^ (prefixWord ++ tailWord_729152).sum := by decide
  have hdescent : baseEnd_729152 < baseStart_729152 := by decide
  rcases family_descends (prefixWord ++ tailWord_729152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729200 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_729200 : Nat := 118140960795 + 729200 * 2 ^ 59
def prefixEnd_729200 : Nat := 4983230072969 + 3 ^ 40 * 729200 * 2
def baseEnd_729200 : Nat := 166413374781623215709545

theorem tailTrace_729200 : CollatzResearch.WordTrace tailWord_729200 prefixEnd_729200 166413374781623215709545 := by
  unfold tailWord_729200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298054479120206145088527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17730739305493608193451369 13298054479120206145088527)
  ·
    refine ⟨19947081718680309217632791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13298054479120206145088527 19947081718680309217632791)
    ·
      refine ⟨29920622578020463826449187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19947081718680309217632791 29920622578020463826449187)
      ·
        refine ⟨44880933867030695739673781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29920622578020463826449187 44880933867030695739673781)
        ·
          refine ⟨4207587550034127725594417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44880933867030695739673781 4207587550034127725594417)
          ·
            refine ⟨3155690662525595794195813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207587550034127725594417 3155690662525595794195813)
            ·
              refine ⟨591691999223549211411715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3155690662525595794195813 591691999223549211411715)
              ·
                refine ⟨887537998835323817117573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591691999223549211411715 887537998835323817117573)
                ·
                  refine ⟨166413374781623215709545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887537998835323817117573 166413374781623215709545)
                  ·
                    rfl

theorem cell21_729200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_729200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729200 prefixEnd_729200 := by exact prefixLift 729200
  have htrace : WordTrace (prefixWord ++ tailWord_729200) baseStart_729200 baseEnd_729200 := by
    simpa [prefixWord, tailWord_729200, baseEnd_729200] using wordTrace_append hprefix tailTrace_729200
  have hstable : (prefixWord ++ tailWord_729200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729200).length < 2 ^ (prefixWord ++ tailWord_729200).sum := by decide
  have hdescent : baseEnd_729200 < baseStart_729200 := by decide
  rcases family_descends (prefixWord ++ tailWord_729200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729304 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_729304 : Nat := 118140960795 + 729304 * 2 ^ 59
def prefixEnd_729304 : Nat := 4983230072969 + 3 ^ 40 * 729304 * 2
def baseEnd_729304 : Nat := 166437108998542145975999

theorem tailTrace_729304 : CollatzResearch.WordTrace tailWord_729304 prefixEnd_729304 166437108998542145975999 := by
  unfold tailWord_729304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13299951074931819025981483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17733268099909092034641977 13299951074931819025981483)
  ·
    refine ⟨19949926612397728538972225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13299951074931819025981483 19949926612397728538972225)
    ·
      refine ⟨14962444959298296404229169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19949926612397728538972225 14962444959298296404229169)
      ·
        refine ⟨11221833719473722303171877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14962444959298296404229169 11221833719473722303171877)
        ·
          refine ⟨2104093822401322931844727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11221833719473722303171877 2104093822401322931844727)
          ·
            refine ⟨3156140733601984397767091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104093822401322931844727 3156140733601984397767091)
            ·
              refine ⟨4734211100402976596650637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156140733601984397767091 4734211100402976596650637)
              ·
                refine ⟨1775329162651116223743989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4734211100402976596650637 1775329162651116223743989)
                ·
                  refine ⟨166437108998542145975999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775329162651116223743989 166437108998542145975999)
                  ·
                    rfl

theorem cell21_729304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_729304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729304 prefixEnd_729304 := by exact prefixLift 729304
  have htrace : WordTrace (prefixWord ++ tailWord_729304) baseStart_729304 baseEnd_729304 := by
    simpa [prefixWord, tailWord_729304, baseEnd_729304] using wordTrace_append hprefix tailTrace_729304
  have hstable : (prefixWord ++ tailWord_729304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729304).length < 2 ^ (prefixWord ++ tailWord_729304).sum := by decide
  have hdescent : baseEnd_729304 < baseStart_729304 := by decide
  rcases family_descends (prefixWord ++ tailWord_729304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729338 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_729338 : Nat := 118140960795 + 729338 * 2 ^ 59
def prefixEnd_729338 : Nat := 4983230072969 + 3 ^ 40 * 729338 * 2
def baseEnd_729338 : Nat := 166444868261765642409263

theorem tailTrace_729338 : CollatzResearch.WordTrace tailWord_729338 prefixEnd_729338 166444868261765642409263 := by
  unfold tailWord_729338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650285557935115464675167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17734094821160307905800445 6650285557935115464675167)
  ·
    refine ⟨9975428336902673197012751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650285557935115464675167 9975428336902673197012751)
    ·
      refine ⟨14963142505354009795519127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975428336902673197012751 14963142505354009795519127)
      ·
        refine ⟨22444713758031014693278691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963142505354009795519127 22444713758031014693278691)
        ·
          refine ⟨33667070637046522039918037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22444713758031014693278691 33667070637046522039918037)
          ·
            refine ⟨789071968055777860310579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33667070637046522039918037 789071968055777860310579)
            ·
              refine ⟨1183607952083666790465869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789071968055777860310579 1183607952083666790465869)
              ·
                refine ⟨443852982031375046424701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183607952083666790465869 443852982031375046424701)
                ·
                  refine ⟨166444868261765642409263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443852982031375046424701 166444868261765642409263)
                  ·
                    rfl

theorem cell21_729338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_729338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729338 prefixEnd_729338 := by exact prefixLift 729338
  have htrace : WordTrace (prefixWord ++ tailWord_729338) baseStart_729338 baseEnd_729338 := by
    simpa [prefixWord, tailWord_729338, baseEnd_729338] using wordTrace_append hprefix tailTrace_729338
  have hstable : (prefixWord ++ tailWord_729338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729338).length < 2 ^ (prefixWord ++ tailWord_729338).sum := by decide
  have hdescent : baseEnd_729338 < baseStart_729338 := by decide
  rcases family_descends (prefixWord ++ tailWord_729338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729397 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 3]
def baseStart_729397 : Nat := 118140960795 + 729397 * 2 ^ 59
def prefixEnd_729397 : Nat := 4983230072969 + 3 ^ 40 * 729397 * 2
def baseEnd_729397 : Nat := 166458332865594650925809

theorem tailTrace_729397 : CollatzResearch.WordTrace tailWord_729397 prefixEnd_729397 166458332865594650925809 := by
  unfold tailWord_729397
  simp only [CollatzResearch.WordTrace]
  refine ⟨26603294138526714935098445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17735529425684476623398963 26603294138526714935098445)
  ·
    refine ⟨9976235301947518100661917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26603294138526714935098445 9976235301947518100661917)
    ·
      refine ⟨3741088238230319287748219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9976235301947518100661917 3741088238230319287748219)
      ·
        refine ⟨5611632357345478931622329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741088238230319287748219 5611632357345478931622329)
        ·
          refine ⟨4208724268009109198716747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5611632357345478931622329 4208724268009109198716747)
          ·
            refine ⟨6313086402013663798075121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208724268009109198716747 6313086402013663798075121)
            ·
              refine ⟨4734814801510247848556341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6313086402013663798075121 4734814801510247848556341)
              ·
                refine ⟨443888887641585735802157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4734814801510247848556341 443888887641585735802157)
                ·
                  refine ⟨166458332865594650925809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443888887641585735802157 166458332865594650925809)
                  ·
                    rfl

theorem cell21_729397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_729397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729397 prefixEnd_729397 := by exact prefixLift 729397
  have htrace : WordTrace (prefixWord ++ tailWord_729397) baseStart_729397 baseEnd_729397 := by
    simpa [prefixWord, tailWord_729397, baseEnd_729397] using wordTrace_append hprefix tailTrace_729397
  have hstable : (prefixWord ++ tailWord_729397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729397).length < 2 ^ (prefixWord ++ tailWord_729397).sum := by decide
  have hdescent : baseEnd_729397 < baseStart_729397 := by decide
  rcases family_descends (prefixWord ++ tailWord_729397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729425 : List Nat := [1, 2, 2, 1, 4, 2, 3, 6]
def baseStart_729425 : Nat := 118140960795 + 729425 * 2 ^ 59
def prefixEnd_729425 : Nat := 4983230072969 + 3 ^ 40 * 729425 * 2
def baseEnd_729425 : Nat := 55488240949024274819695

theorem tailTrace_729425 : CollatzResearch.WordTrace tailWord_729425 prefixEnd_729425 55488240949024274819695 := by
  unfold tailWord_729425
  simp only [CollatzResearch.WordTrace]
  refine ⟨26604315382425275717117729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17736210254950183811411819 26604315382425275717117729)
  ·
    refine ⟨19953236536818956787838297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26604315382425275717117729 19953236536818956787838297)
    ·
      refine ⟨14964927402614217590878723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19953236536818956787838297 14964927402614217590878723)
      ·
        refine ⟨22447391103921326386318085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964927402614217590878723 22447391103921326386318085)
        ·
          refine ⟨4208885831985248697434641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22447391103921326386318085 4208885831985248697434641)
          ·
            refine ⟨3156664373988936523075981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4208885831985248697434641 3156664373988936523075981)
            ·
              refine ⟨1183749140245851196153493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3156664373988936523075981 1183749140245851196153493)
              ·
                refine ⟨55488240949024274819695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1183749140245851196153493 55488240949024274819695)
                ·
                  rfl

theorem cell21_729425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_729425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729425 prefixEnd_729425 := by exact prefixLift 729425
  have htrace : WordTrace (prefixWord ++ tailWord_729425) baseStart_729425 baseEnd_729425 := by
    simpa [prefixWord, tailWord_729425, baseEnd_729425] using wordTrace_append hprefix tailTrace_729425
  have hstable : (prefixWord ++ tailWord_729425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729425).length < 2 ^ (prefixWord ++ tailWord_729425).sum := by decide
  have hdescent : baseEnd_729425 < baseStart_729425 := by decide
  rcases family_descends (prefixWord ++ tailWord_729425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729439 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_729439 : Nat := 118140960795 + 729439 * 2 ^ 59
def prefixEnd_729439 : Nat := 4983230072969 + 3 ^ 40 * 729439 * 2
def baseEnd_729439 : Nat := 166467917837811911225723

theorem tailTrace_729439 : CollatzResearch.WordTrace tailWord_729439 prefixEnd_729439 166467917837811911225723 := by
  unfold tailWord_729439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26604826004374556108127371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17736550669583037405418247 26604826004374556108127371)
  ·
    refine ⟨39907239006561834162191057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26604826004374556108127371 39907239006561834162191057)
    ·
      refine ⟨29930429254921375621643293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39907239006561834162191057 29930429254921375621643293)
      ·
        refine ⟨11223910970595515858116235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29930429254921375621643293 11223910970595515858116235)
        ·
          refine ⟨16835866455893273787174353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11223910970595515858116235 16835866455893273787174353)
          ·
            refine ⟨12626899841919955340380765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16835866455893273787174353 12626899841919955340380765)
            ·
              refine ⟨4735087440719983252642787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12626899841919955340380765 4735087440719983252642787)
              ·
                refine ⟨7102631161079974878964181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735087440719983252642787 7102631161079974878964181)
                ·
                  refine ⟨166467917837811911225723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7102631161079974878964181 166467917837811911225723)
                  ·
                    rfl

theorem cell21_729439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_729439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729439 prefixEnd_729439 := by exact prefixLift 729439
  have htrace : WordTrace (prefixWord ++ tailWord_729439) baseStart_729439 baseEnd_729439 := by
    simpa [prefixWord, tailWord_729439, baseEnd_729439] using wordTrace_append hprefix tailTrace_729439
  have hstable : (prefixWord ++ tailWord_729439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729439).length < 2 ^ (prefixWord ++ tailWord_729439).sum := by decide
  have hdescent : baseEnd_729439 < baseStart_729439 := by decide
  rcases family_descends (prefixWord ++ tailWord_729439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729462 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_729462 : Nat := 118140960795 + 729462 * 2 ^ 59
def prefixEnd_729462 : Nat := 4983230072969 + 3 ^ 40 * 729462 * 2
def baseEnd_729462 : Nat := 166473166751168982342343

theorem tailTrace_729462 : CollatzResearch.WordTrace tailWord_729462 prefixEnd_729462 166473166751168982342343 := by
  unfold tailWord_729462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662854055205701939763415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17737109922194154024143093 1662854055205701939763415)
  ·
    refine ⟨2494281082808552909645123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662854055205701939763415 2494281082808552909645123)
    ·
      refine ⟨3741421624212829364467685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494281082808552909645123 3741421624212829364467685)
      ·
        refine ⟨701516554539905505837691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3741421624212829364467685 701516554539905505837691)
        ·
          refine ⟨1052274831809858258756537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701516554539905505837691 1052274831809858258756537)
          ·
            refine ⟨789206123857393694067403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052274831809858258756537 789206123857393694067403)
            ·
              refine ⟨1183809185786090541101105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789206123857393694067403 1183809185786090541101105)
              ·
                refine ⟨887856889339567905825829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183809185786090541101105 887856889339567905825829)
                ·
                  refine ⟨166473166751168982342343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887856889339567905825829 166473166751168982342343)
                  ·
                    rfl

theorem cell21_729462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_729462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729462 prefixEnd_729462 := by exact prefixLift 729462
  have htrace : WordTrace (prefixWord ++ tailWord_729462) baseStart_729462 baseEnd_729462 := by
    simpa [prefixWord, tailWord_729462, baseEnd_729462] using wordTrace_append hprefix tailTrace_729462
  have hstable : (prefixWord ++ tailWord_729462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729462).length < 2 ^ (prefixWord ++ tailWord_729462).sum := by decide
  have hdescent : baseEnd_729462 < baseStart_729462 := by decide
  rcases family_descends (prefixWord ++ tailWord_729462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729473 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_729473 : Nat := 118140960795 + 729473 * 2 ^ 59
def prefixEnd_729473 : Nat := 4983230072969 + 3 ^ 40 * 729473 * 2
def baseEnd_729473 : Nat := 166475677101035407658987

theorem tailTrace_729473 : CollatzResearch.WordTrace tailWord_729473 prefixEnd_729473 166475677101035407658987 := by
  unfold tailWord_729473
  simp only [CollatzResearch.WordTrace]
  refine ⟨26606066086251379914865073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17737377390834253276576715 26606066086251379914865073)
  ·
    refine ⟨19954549564688534936148805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26606066086251379914865073 19954549564688534936148805)
    ·
      refine ⟨3741478043379100300527901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19954549564688534936148805 3741478043379100300527901)
      ·
        refine ⟨1403054266267162612697963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3741478043379100300527901 1403054266267162612697963)
        ·
          refine ⟨2104581399400743919046945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403054266267162612697963 2104581399400743919046945)
          ·
            refine ⟨1578436049550557939285209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104581399400743919046945 1578436049550557939285209)
            ·
              refine ⟨1183827037162918454463907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1578436049550557939285209 1183827037162918454463907)
              ·
                refine ⟨1775740555744377681695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183827037162918454463907 1775740555744377681695861)
                ·
                  refine ⟨166475677101035407658987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775740555744377681695861 166475677101035407658987)
                  ·
                    rfl

theorem cell21_729473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_729473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729473 prefixEnd_729473 := by exact prefixLift 729473
  have htrace : WordTrace (prefixWord ++ tailWord_729473) baseStart_729473 baseEnd_729473 := by
    simpa [prefixWord, tailWord_729473, baseEnd_729473] using wordTrace_append hprefix tailTrace_729473
  have hstable : (prefixWord ++ tailWord_729473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729473).length < 2 ^ (prefixWord ++ tailWord_729473).sum := by decide
  have hdescent : baseEnd_729473 < baseStart_729473 := by decide
  rcases family_descends (prefixWord ++ tailWord_729473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729524 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_729524 : Nat := 118140960795 + 729524 * 2 ^ 59
def prefixEnd_729524 : Nat := 4983230072969 + 3 ^ 40 * 729524 * 2
def baseEnd_729524 : Nat := 166487315995870652308883

theorem tailTrace_729524 : CollatzResearch.WordTrace tailWord_729524 prefixEnd_729524 166487315995870652308883 := by
  unfold tailWord_729524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303963104533307812485813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17738617472711077083314417 13303963104533307812485813)
  ·
    refine ⟨1247246541049997607420545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13303963104533307812485813 1247246541049997607420545)
    ·
      refine ⟨935434905787498205565409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247246541049997607420545 935434905787498205565409)
      ·
        refine ⟨701576179340623654174057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 935434905787498205565409 701576179340623654174057)
        ·
          refine ⟨526182134505467740630543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701576179340623654174057 526182134505467740630543)
          ·
            refine ⟨789273201758201610945815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526182134505467740630543 789273201758201610945815)
            ·
              refine ⟨1183909802637302416418723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789273201758201610945815 1183909802637302416418723)
              ·
                refine ⟨1775864703955953624628085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183909802637302416418723 1775864703955953624628085)
                ·
                  refine ⟨166487315995870652308883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775864703955953624628085 166487315995870652308883)
                  ·
                    rfl

theorem cell21_729524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_729524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729524 prefixEnd_729524 := by exact prefixLift 729524
  have htrace : WordTrace (prefixWord ++ tailWord_729524) baseStart_729524 baseEnd_729524 := by
    simpa [prefixWord, tailWord_729524, baseEnd_729524] using wordTrace_append hprefix tailTrace_729524
  have hstable : (prefixWord ++ tailWord_729524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729524).length < 2 ^ (prefixWord ++ tailWord_729524).sum := by decide
  have hdescent : baseEnd_729524 < baseStart_729524 := by decide
  rcases family_descends (prefixWord ++ tailWord_729524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729701 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 5]
def baseStart_729701 : Nat := 118140960795 + 729701 * 2 ^ 59
def prefixEnd_729701 : Nat := 4983230072969 + 3 ^ 40 * 729701 * 2
def baseEnd_729701 : Nat := 166527709807357677858521

theorem tailTrace_729701 : CollatzResearch.WordTrace tailWord_729701 prefixEnd_729701 166527709807357677858521 := by
  unfold tailWord_729701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26614381929425374854164957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17742921286283583236109971 26614381929425374854164957)
  ·
    refine ⟨9980393223534515570311859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26614381929425374854164957 9980393223534515570311859)
    ·
      refine ⟨14970589835301773355467789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980393223534515570311859 14970589835301773355467789)
      ·
        refine ⟨5613971188238165008300421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14970589835301773355467789 5613971188238165008300421)
        ·
          refine ⟨1052619597794655939056329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5613971188238165008300421 1052619597794655939056329)
          ·
            refine ⟨789464698345991954292247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052619597794655939056329 789464698345991954292247)
            ·
              refine ⟨1184197047518987931438371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789464698345991954292247 1184197047518987931438371)
              ·
                refine ⟨1776295571278481897157557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184197047518987931438371 1776295571278481897157557)
                ·
                  refine ⟨166527709807357677858521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776295571278481897157557 166527709807357677858521)
                  ·
                    rfl

theorem cell21_729701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_729701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729701 prefixEnd_729701 := by exact prefixLift 729701
  have htrace : WordTrace (prefixWord ++ tailWord_729701) baseStart_729701 baseEnd_729701 := by
    simpa [prefixWord, tailWord_729701, baseEnd_729701] using wordTrace_append hprefix tailTrace_729701
  have hstable : (prefixWord ++ tailWord_729701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729701).length < 2 ^ (prefixWord ++ tailWord_729701).sum := by decide
  have hdescent : baseEnd_729701 < baseStart_729701 := by decide
  rcases family_descends (prefixWord ++ tailWord_729701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729777 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 5]
def baseStart_729777 : Nat := 118140960795 + 729777 * 2 ^ 59
def prefixEnd_729777 : Nat := 4983230072969 + 3 ^ 40 * 729777 * 2
def baseEnd_729777 : Nat := 166545054042798434591699

theorem tailTrace_729777 : CollatzResearch.WordTrace tailWord_729777 prefixEnd_729777 166545054042798434591699 := by
  unfold tailWord_729777
  simp only [CollatzResearch.WordTrace]
  refine ⟨26617153877150039833931585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17744769251433359889287723 26617153877150039833931585)
  ·
    refine ⟨19962865407862529875448689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26617153877150039833931585 19962865407862529875448689)
    ·
      refine ⟨14972149055896897406586517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19962865407862529875448689 14972149055896897406586517)
      ·
        refine ⟨701819486995167065933743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14972149055896897406586517 701819486995167065933743)
        ·
          refine ⟨1052729230492750598900615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701819486995167065933743 1052729230492750598900615)
          ·
            refine ⟨1579093845739125898350923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052729230492750598900615 1579093845739125898350923)
            ·
              refine ⟨2368640768608688847526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579093845739125898350923 2368640768608688847526385)
              ·
                refine ⟨1776480576456516635644789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368640768608688847526385 1776480576456516635644789)
                ·
                  refine ⟨166545054042798434591699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776480576456516635644789 166545054042798434591699)
                  ·
                    rfl

theorem cell21_729777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_729777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729777 prefixEnd_729777 := by exact prefixLift 729777
  have htrace : WordTrace (prefixWord ++ tailWord_729777) baseStart_729777 baseEnd_729777 := by
    simpa [prefixWord, tailWord_729777, baseEnd_729777] using wordTrace_append hprefix tailTrace_729777
  have hstable : (prefixWord ++ tailWord_729777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729777).length < 2 ^ (prefixWord ++ tailWord_729777).sum := by decide
  have hdescent : baseEnd_729777 < baseStart_729777 := by decide
  rcases family_descends (prefixWord ++ tailWord_729777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729845 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 3]
def baseStart_729845 : Nat := 118140960795 + 729845 * 2 ^ 59
def prefixEnd_729845 : Nat := 4983230072969 + 3 ^ 40 * 729845 * 2
def baseEnd_729845 : Nat := 166560572569245427458227

theorem tailTrace_729845 : CollatzResearch.WordTrace tailWord_729845 prefixEnd_729845 166560572569245427458227 := by
  unfold tailWord_729845
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619634040903687447406989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17746422693935791631604659 26619634040903687447406989)
  ·
    refine ⟨9982362765338882792777621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26619634040903687447406989 9982362765338882792777621)
    ·
      refine ⟨467923254625260130911451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9982362765338882792777621 467923254625260130911451)
      ·
        refine ⟨701884881937890196367177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467923254625260130911451 701884881937890196367177)
        ·
          refine ⟨526413661453417647275383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701884881937890196367177 526413661453417647275383)
          ·
            refine ⟨789620492180126470913075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526413661453417647275383 789620492180126470913075)
            ·
              refine ⟨1184430738270189706369613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789620492180126470913075 1184430738270189706369613)
              ·
                refine ⟨444161526851321139888605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1184430738270189706369613 444161526851321139888605)
                ·
                  refine ⟨166560572569245427458227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444161526851321139888605 166560572569245427458227)
                  ·
                    rfl

theorem cell21_729845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_729845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729845 prefixEnd_729845 := by exact prefixLift 729845
  have htrace : WordTrace (prefixWord ++ tailWord_729845) baseStart_729845 baseEnd_729845 := by
    simpa [prefixWord, tailWord_729845, baseEnd_729845] using wordTrace_append hprefix tailTrace_729845
  have hstable : (prefixWord ++ tailWord_729845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729845).length < 2 ^ (prefixWord ++ tailWord_729845).sum := by decide
  have hdescent : baseEnd_729845 < baseStart_729845 := by decide
  rcases family_descends (prefixWord ++ tailWord_729845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729864 : List Nat := [2, 1, 3, 2, 2, 2, 9]
def baseStart_729864 : Nat := 118140960795 + 729864 * 2 ^ 59
def prefixEnd_729864 : Nat := 4983230072969 + 3 ^ 40 * 729864 * 2
def baseEnd_729864 : Nat := 18507212069789512960169

theorem tailTrace_729864 : CollatzResearch.WordTrace tailWord_729864 prefixEnd_729864 18507212069789512960169 := by
  unfold tailWord_729864
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310163513917426846174323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17746884685223235794899097 13310163513917426846174323)
  ·
    refine ⟨19965245270876140269261485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13310163513917426846174323 19965245270876140269261485)
    ·
      refine ⟨7486966976578552600973057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19965245270876140269261485 7486966976578552600973057)
      ·
        refine ⟨5615225232433914450729793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7486966976578552600973057 5615225232433914450729793)
        ·
          refine ⟨4211418924325435838047345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615225232433914450729793 4211418924325435838047345)
          ·
            refine ⟨3158564193244076878535509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211418924325435838047345 3158564193244076878535509)
            ·
              refine ⟨18507212069789512960169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3158564193244076878535509 18507212069789512960169)
              ·
                rfl

theorem cell21_729864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 9].length) (baseStart_729864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729864 prefixEnd_729864 := by exact prefixLift 729864
  have htrace : WordTrace (prefixWord ++ tailWord_729864) baseStart_729864 baseEnd_729864 := by
    simpa [prefixWord, tailWord_729864, baseEnd_729864] using wordTrace_append hprefix tailTrace_729864
  have hstable : (prefixWord ++ tailWord_729864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729864).length < 2 ^ (prefixWord ++ tailWord_729864).sum := by decide
  have hdescent : baseEnd_729864 < baseStart_729864 := by decide
  rcases family_descends (prefixWord ++ tailWord_729864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729884 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_729884 : Nat := 118140960795 + 729884 * 2 ^ 59
def prefixEnd_729884 : Nat := 4983230072969 + 3 ^ 40 * 729884 * 2
def baseEnd_729884 : Nat := 166569472900590026308147

theorem tailTrace_729884 : CollatzResearch.WordTrace tailWord_729884 prefixEnd_729884 166569472900590026308147 := by
  unfold tailWord_729884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310528243881198554038353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17747370991841598072051137 13310528243881198554038353)
  ·
    refine ⟨9982896182910898915528765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13310528243881198554038353 9982896182910898915528765)
    ·
      refine ⟨3743586068591587093323287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9982896182910898915528765 3743586068591587093323287)
      ·
        refine ⟨5615379102887380639984931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743586068591587093323287 5615379102887380639984931)
        ·
          refine ⟨8423068654331070959977397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615379102887380639984931 8423068654331070959977397)
          ·
            refine ⟨789662686343537902497881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8423068654331070959977397 789662686343537902497881)
            ·
              refine ⟨592247014757653426873411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789662686343537902497881 592247014757653426873411)
              ·
                refine ⟨888370522136480140310117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592247014757653426873411 888370522136480140310117)
                ·
                  refine ⟨166569472900590026308147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888370522136480140310117 166569472900590026308147)
                  ·
                    rfl

theorem cell21_729884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_729884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729884 prefixEnd_729884 := by exact prefixLift 729884
  have htrace : WordTrace (prefixWord ++ tailWord_729884) baseStart_729884 baseEnd_729884 := by
    simpa [prefixWord, tailWord_729884, baseEnd_729884] using wordTrace_append hprefix tailTrace_729884
  have hstable : (prefixWord ++ tailWord_729884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729884).length < 2 ^ (prefixWord ++ tailWord_729884).sum := by decide
  have hdescent : baseEnd_729884 < baseStart_729884 := by decide
  rcases family_descends (prefixWord ++ tailWord_729884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729912 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_729912 : Nat := 118140960795 + 729912 * 2 ^ 59
def prefixEnd_729912 : Nat := 4983230072969 + 3 ^ 40 * 729912 * 2
def baseEnd_729912 : Nat := 166575862882068199841423

theorem tailTrace_729912 : CollatzResearch.WordTrace tailWord_729912 prefixEnd_729912 166575862882068199841423 := by
  unfold tailWord_729912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311038865830478945047995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17748051821107305260063993 13311038865830478945047995)
  ·
    refine ⟨19966558298745718417571993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13311038865830478945047995 19966558298745718417571993)
    ·
      refine ⟨14974918724059288813178995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19966558298745718417571993 14974918724059288813178995)
      ·
        refine ⟨22462378086088933219768493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14974918724059288813178995 22462378086088933219768493)
        ·
          refine ⟨8423391782283349957413185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22462378086088933219768493 8423391782283349957413185)
          ·
            refine ⟨6317543836712512468059889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423391782283349957413185 6317543836712512468059889)
            ·
              refine ⟨4738157877534384351044917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6317543836712512468059889 4738157877534384351044917)
              ·
                refine ⟨444202301018848532910461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4738157877534384351044917 444202301018848532910461)
                ·
                  refine ⟨166575862882068199841423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444202301018848532910461 166575862882068199841423)
                  ·
                    rfl

theorem cell21_729912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_729912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729912 prefixEnd_729912 := by exact prefixLift 729912
  have htrace : WordTrace (prefixWord ++ tailWord_729912) baseStart_729912 baseEnd_729912 := by
    simpa [prefixWord, tailWord_729912, baseEnd_729912] using wordTrace_append hprefix tailTrace_729912
  have hstable : (prefixWord ++ tailWord_729912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729912).length < 2 ^ (prefixWord ++ tailWord_729912).sum := by decide
  have hdescent : baseEnd_729912 < baseStart_729912 := by decide
  rcases family_descends (prefixWord ++ tailWord_729912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729929 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 3]
def baseStart_729929 : Nat := 118140960795 + 729929 * 2 ^ 59
def prefixEnd_729929 : Nat := 4983230072969 + 3 ^ 40 * 729929 * 2
def baseEnd_729929 : Nat := 166579742513679948058055

theorem tailTrace_729929 : CollatzResearch.WordTrace tailWord_729929 prefixEnd_729929 166579742513679948058055 := by
  unfold tailWord_729929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622697772599369793464841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17748465181732913195643227 26622697772599369793464841)
  ·
    refine ⟨19967023329449527345098631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26622697772599369793464841 19967023329449527345098631)
    ·
      refine ⟨29950534994174291017647947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19967023329449527345098631 29950534994174291017647947)
      ·
        refine ⟨44925802491261436526471921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29950534994174291017647947 44925802491261436526471921)
        ·
          refine ⟨33694351868446077394853941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44925802491261436526471921 33694351868446077394853941)
          ·
            refine ⟨3158845487666819755767557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33694351868446077394853941 3158845487666819755767557)
            ·
              refine ⟨592283528937528704206417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3158845487666819755767557 592283528937528704206417)
              ·
                refine ⟨444212646703146528154813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592283528937528704206417 444212646703146528154813)
                ·
                  refine ⟨166579742513679948058055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444212646703146528154813 166579742513679948058055)
                  ·
                    rfl

theorem cell21_729929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_729929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_729929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_729929 prefixEnd_729929 := by exact prefixLift 729929
  have htrace : WordTrace (prefixWord ++ tailWord_729929) baseStart_729929 baseEnd_729929 := by
    simpa [prefixWord, tailWord_729929, baseEnd_729929] using wordTrace_append hprefix tailTrace_729929
  have hstable : (prefixWord ++ tailWord_729929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729929).length < 2 ^ (prefixWord ++ tailWord_729929).sum := by decide
  have hdescent : baseEnd_729929 < baseStart_729929 := by decide
  rcases family_descends (prefixWord ++ tailWord_729929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730033 : List Nat := [1, 2, 2, 4, 3, 2, 7]
def baseStart_730033 : Nat := 118140960795 + 730033 * 2 ^ 59
def prefixEnd_730033 : Nat := 4983230072969 + 3 ^ 40 * 730033 * 2
def baseEnd_730033 : Nat := 18511497414510986480501

theorem tailTrace_730033 : CollatzResearch.WordTrace tailWord_730033 prefixEnd_730033 18511497414510986480501 := by
  unfold tailWord_730033
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626490964222595555250753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17750993976148397036833835 26626490964222595555250753)
  ·
    refine ⟨19969868223166946666438065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26626490964222595555250753 19969868223166946666438065)
    ·
      refine ⟨14977401167375209999828549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19969868223166946666438065 14977401167375209999828549)
      ·
        refine ⟨2808262718882851874967853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14977401167375209999828549 2808262718882851874967853)
        ·
          refine ⟨1053098519581069453112945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2808262718882851874967853 1053098519581069453112945)
          ·
            refine ⟨789823889685802089834709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053098519581069453112945 789823889685802089834709)
            ·
              refine ⟨18511497414510986480501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 789823889685802089834709 18511497414510986480501)
              ·
                rfl

theorem cell21_730033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 7].length) (baseStart_730033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730033 prefixEnd_730033 := by exact prefixLift 730033
  have htrace : WordTrace (prefixWord ++ tailWord_730033) baseStart_730033 baseEnd_730033 := by
    simpa [prefixWord, tailWord_730033, baseEnd_730033] using wordTrace_append hprefix tailTrace_730033
  have hstable : (prefixWord ++ tailWord_730033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730033).length < 2 ^ (prefixWord ++ tailWord_730033).sum := by decide
  have hdescent : baseEnd_730033 < baseStart_730033 := by decide
  rcases family_descends (prefixWord ++ tailWord_730033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730098 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_730098 : Nat := 118140960795 + 730098 * 2 ^ 59
def prefixEnd_730098 : Nat := 4983230072969 + 3 ^ 40 * 730098 * 2
def baseEnd_730098 : Nat := 166618310616173209741043

theorem tailTrace_730098 : CollatzResearch.WordTrace tailWord_730098 prefixEnd_730098 166618310616173209741043 := by
  unfold tailWord_730098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657215427246777914091737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17752574472658074437577965 6657215427246777914091737)
  ·
    refine ⟨4992911570435083435568803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6657215427246777914091737 4992911570435083435568803)
    ·
      refine ⟨7489367355652625153353205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992911570435083435568803 7489367355652625153353205)
      ·
        refine ⟨702128189592433608126863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7489367355652625153353205 702128189592433608126863)
        ·
          refine ⟨1053192284388650412190295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702128189592433608126863 1053192284388650412190295)
          ·
            refine ⟨1579788426582975618285443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053192284388650412190295 1579788426582975618285443)
            ·
              refine ⟨2369682639874463427428165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579788426582975618285443 2369682639874463427428165)
              ·
                refine ⟨444315494976461892642781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2369682639874463427428165 444315494976461892642781)
                ·
                  refine ⟨166618310616173209741043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444315494976461892642781 166618310616173209741043)
                  ·
                    rfl

theorem cell21_730098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_730098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730098 prefixEnd_730098 := by exact prefixLift 730098
  have htrace : WordTrace (prefixWord ++ tailWord_730098) baseStart_730098 baseEnd_730098 := by
    simpa [prefixWord, tailWord_730098, baseEnd_730098] using wordTrace_append hprefix tailTrace_730098
  have hstable : (prefixWord ++ tailWord_730098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730098).length < 2 ^ (prefixWord ++ tailWord_730098).sum := by decide
  have hdescent : baseEnd_730098 < baseStart_730098 := by decide
  rcases family_descends (prefixWord ++ tailWord_730098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730106 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_730106 : Nat := 118140960795 + 730106 * 2 ^ 59
def prefixEnd_730106 : Nat := 4983230072969 + 3 ^ 40 * 730106 * 2
def baseEnd_730106 : Nat := 166620136325166973607693

theorem tailTrace_730106 : CollatzResearch.WordTrace tailWord_730106 prefixEnd_730106 166620136325166973607693 := by
  unfold tailWord_730106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657288373239532255664543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17752768995305419348438781 6657288373239532255664543)
  ·
    refine ⟨9985932559859298383496815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6657288373239532255664543 9985932559859298383496815)
    ·
      refine ⟨14978898839788947575245223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9985932559859298383496815 14978898839788947575245223)
      ·
        refine ⟨22468348259683421362867835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14978898839788947575245223 22468348259683421362867835)
        ·
          refine ⟨33702522389525132044301753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22468348259683421362867835 33702522389525132044301753)
          ·
            refine ⟨25276891792143849033226315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33702522389525132044301753 25276891792143849033226315)
            ·
              refine ⟨37915337688215773549839473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25276891792143849033226315 37915337688215773549839473)
              ·
                refine ⟨28436503266161830162379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37915337688215773549839473 28436503266161830162379605)
                ·
                  refine ⟨166620136325166973607693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28436503266161830162379605 166620136325166973607693)
                  ·
                    rfl

theorem cell21_730106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_730106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730106 prefixEnd_730106 := by exact prefixLift 730106
  have htrace : WordTrace (prefixWord ++ tailWord_730106) baseStart_730106 baseEnd_730106 := by
    simpa [prefixWord, tailWord_730106, baseEnd_730106] using wordTrace_append hprefix tailTrace_730106
  have hstable : (prefixWord ++ tailWord_730106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730106).length < 2 ^ (prefixWord ++ tailWord_730106).sum := by decide
  have hdescent : baseEnd_730106 < baseStart_730106 := by decide
  rcases family_descends (prefixWord ++ tailWord_730106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730123 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_730123 : Nat := 118140960795 + 730123 * 2 ^ 59
def prefixEnd_730123 : Nat := 4983230072969 + 3 ^ 40 * 730123 * 2
def baseEnd_730123 : Nat := 166624015956778721824325

theorem tailTrace_730123 : CollatzResearch.WordTrace tailWord_730123 prefixEnd_730123 166624015956778721824325 := by
  unfold tailWord_730123
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629773533896540926027023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17753182355931027284018015 26629773533896540926027023)
  ·
    refine ⟨39944660300844811389040535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26629773533896540926027023 39944660300844811389040535)
    ·
      refine ⟨59916990451267217083560803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39944660300844811389040535 59916990451267217083560803)
      ·
        refine ⟨89875485676900825625341205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59916990451267217083560803 89875485676900825625341205)
        ·
          refine ⟨4212913391104726201187869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89875485676900825625341205 4212913391104726201187869)
          ·
            refine ⟨1579842521664272325445451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4212913391104726201187869 1579842521664272325445451)
            ·
              refine ⟨2369763782496408488168177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579842521664272325445451 2369763782496408488168177)
              ·
                refine ⟨1777322836872306366126133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369763782496408488168177 1777322836872306366126133)
                ·
                  refine ⟨166624015956778721824325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777322836872306366126133 166624015956778721824325)
                  ·
                    rfl

theorem cell21_730123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_730123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730123 prefixEnd_730123 := by exact prefixLift 730123
  have htrace : WordTrace (prefixWord ++ tailWord_730123) baseStart_730123 baseEnd_730123 := by
    simpa [prefixWord, tailWord_730123, baseEnd_730123] using wordTrace_append hprefix tailTrace_730123
  have hstable : (prefixWord ++ tailWord_730123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730123).length < 2 ^ (prefixWord ++ tailWord_730123).sum := by decide
  have hdescent : baseEnd_730123 < baseStart_730123 := by decide
  rcases family_descends (prefixWord ++ tailWord_730123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730213 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_730213 : Nat := 118140960795 + 730213 * 2 ^ 59
def prefixEnd_730213 : Nat := 4983230072969 + 3 ^ 40 * 730213 * 2
def baseEnd_730213 : Nat := 166644555182958565324141

theorem tailTrace_730213 : CollatzResearch.WordTrace tailWord_730213 prefixEnd_730213 166644555182958565324141 := by
  unfold tailWord_730213
  simp only [CollatzResearch.WordTrace]
  refine ⟨26633056103570486296803293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17755370735713657531202195 26633056103570486296803293)
  ·
    refine ⟨9987396038838932361301235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26633056103570486296803293 9987396038838932361301235)
    ·
      refine ⟨14981094058258398541951853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9987396038838932361301235 14981094058258398541951853)
      ·
        refine ⟨5617910271846899453231945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14981094058258398541951853 5617910271846899453231945)
        ·
          refine ⟨4213432703885174589923959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5617910271846899453231945 4213432703885174589923959)
          ·
            refine ⟨6320149055827761884885939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213432703885174589923959 6320149055827761884885939)
            ·
              refine ⟨9480223583741642827328909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320149055827761884885939 9480223583741642827328909)
              ·
                refine ⟨3555083843903116060248341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9480223583741642827328909 3555083843903116060248341)
                ·
                  refine ⟨166644555182958565324141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3555083843903116060248341 166644555182958565324141)
                  ·
                    rfl

theorem cell21_730213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_730213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730213 prefixEnd_730213 := by exact prefixLift 730213
  have htrace : WordTrace (prefixWord ++ tailWord_730213) baseStart_730213 baseEnd_730213 := by
    simpa [prefixWord, tailWord_730213, baseEnd_730213] using wordTrace_append hprefix tailTrace_730213
  have hstable : (prefixWord ++ tailWord_730213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730213).length < 2 ^ (prefixWord ++ tailWord_730213).sum := by decide
  have hdescent : baseEnd_730213 < baseStart_730213 := by decide
  rcases family_descends (prefixWord ++ tailWord_730213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730244 : List Nat := [2, 3, 2, 1, 2, 2, 2, 7]
def baseStart_730244 : Nat := 118140960795 + 730244 * 2 ^ 59
def prefixEnd_730244 : Nat := 4983230072969 + 3 ^ 40 * 730244 * 2
def baseEnd_730244 : Nat := 55550543268436466769137

theorem tailTrace_730244 : CollatzResearch.WordTrace tailWord_730244 prefixEnd_730244 55550543268436466769137 := by
  unfold tailWord_730244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317093383229089295590893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17756124510972119060787857 13317093383229089295590893)
  ·
    refine ⟨4993910018710908485846585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13317093383229089295590893 4993910018710908485846585)
    ·
      refine ⟨3745432514033181364384939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4993910018710908485846585 3745432514033181364384939)
      ·
        refine ⟨5618148771049772046577409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745432514033181364384939 5618148771049772046577409)
        ·
          refine ⟨4213611578287329034933057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618148771049772046577409 4213611578287329034933057)
          ·
            refine ⟨3160208683715496776199793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213611578287329034933057 3160208683715496776199793)
            ·
              refine ⟨2370156512786622582149845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160208683715496776199793 2370156512786622582149845)
              ·
                refine ⟨55550543268436466769137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2370156512786622582149845 55550543268436466769137)
                ·
                  rfl

theorem cell21_730244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_730244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730244 prefixEnd_730244 := by exact prefixLift 730244
  have htrace : WordTrace (prefixWord ++ tailWord_730244) baseStart_730244 baseEnd_730244 := by
    simpa [prefixWord, tailWord_730244, baseEnd_730244] using wordTrace_append hprefix tailTrace_730244
  have hstable : (prefixWord ++ tailWord_730244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730244).length < 2 ^ (prefixWord ++ tailWord_730244).sum := by decide
  have hdescent : baseEnd_730244 < baseStart_730244 := by decide
  rcases family_descends (prefixWord ++ tailWord_730244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730303 : List Nat := [1, 1, 2, 2, 2, 2, 2, 9]
def baseStart_730303 : Nat := 118140960795 + 730303 * 2 ^ 59
def prefixEnd_730303 : Nat := 4983230072969 + 3 ^ 40 * 730303 * 2
def baseEnd_730303 : Nat := 55555031469712802941319

theorem tailTrace_730303 : CollatzResearch.WordTrace tailWord_730303 prefixEnd_730303 55555031469712802941319 := by
  unfold tailWord_730303
  simp only [CollatzResearch.WordTrace]
  refine ⟨26636338673244431667579563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17757559115496287778386375 26636338673244431667579563)
  ·
    refine ⟨39954508009866647501369345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26636338673244431667579563 39954508009866647501369345)
    ·
      refine ⟨29965881007399985626027009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39954508009866647501369345 29965881007399985626027009)
      ·
        refine ⟨22474410755549989219520257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29965881007399985626027009 22474410755549989219520257)
        ·
          refine ⟨16855808066662491914640193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22474410755549989219520257 16855808066662491914640193)
          ·
            refine ⟨12641856049996868935980145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16855808066662491914640193 12641856049996868935980145)
            ·
              refine ⟨9481392037497651701985109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12641856049996868935980145 9481392037497651701985109)
              ·
                refine ⟨55555031469712802941319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9481392037497651701985109 55555031469712802941319)
                ·
                  rfl

theorem cell21_730303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_730303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730303 prefixEnd_730303 := by exact prefixLift 730303
  have htrace : WordTrace (prefixWord ++ tailWord_730303) baseStart_730303 baseEnd_730303 := by
    simpa [prefixWord, tailWord_730303, baseEnd_730303] using wordTrace_append hprefix tailTrace_730303
  have hstable : (prefixWord ++ tailWord_730303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730303).length < 2 ^ (prefixWord ++ tailWord_730303).sum := by decide
  have hdescent : baseEnd_730303 < baseStart_730303 := by decide
  rcases family_descends (prefixWord ++ tailWord_730303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730354 : List Nat := [3, 2, 1, 3, 3, 2, 2, 5]
def baseStart_730354 : Nat := 118140960795 + 730354 * 2 ^ 59
def prefixEnd_730354 : Nat := 4983230072969 + 3 ^ 40 * 730354 * 2
def baseEnd_730354 : Nat := 55558911101324551157951

theorem tailTrace_730354 : CollatzResearch.WordTrace tailWord_730354 prefixEnd_730354 55558911101324551157951 := by
  unfold tailWord_730354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659549699014916844421529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17758799197373111585124077 6659549699014916844421529)
  ·
    refine ⟨4994662274261187633316147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6659549699014916844421529 4994662274261187633316147)
    ·
      refine ⟨7491993411391781449974221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994662274261187633316147 7491993411391781449974221)
      ·
        refine ⟨2809497529271918043740333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7491993411391781449974221 2809497529271918043740333)
        ·
          refine ⟨1053561573476969266402625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2809497529271918043740333 1053561573476969266402625)
          ·
            refine ⟨790171180107726949801969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053561573476969266402625 790171180107726949801969)
            ·
              refine ⟨592628385080795212351477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790171180107726949801969 592628385080795212351477)
              ·
                refine ⟨55558911101324551157951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 592628385080795212351477 55558911101324551157951)
                ·
                  rfl

theorem cell21_730354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_730354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730354 prefixEnd_730354 := by exact prefixLift 730354
  have htrace : WordTrace (prefixWord ++ tailWord_730354) baseStart_730354 baseEnd_730354 := by
    simpa [prefixWord, tailWord_730354, baseEnd_730354] using wordTrace_append hprefix tailTrace_730354
  have hstable : (prefixWord ++ tailWord_730354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730354).length < 2 ^ (prefixWord ++ tailWord_730354).sum := by decide
  have hdescent : baseEnd_730354 < baseStart_730354 := by decide
  rcases family_descends (prefixWord ++ tailWord_730354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730379 : List Nat := [1, 1, 1, 1, 5, 3, 9]
def baseStart_730379 : Nat := 118140960795 + 730379 * 2 ^ 59
def prefixEnd_730379 : Nat := 4983230072969 + 3 ^ 40 * 730379 * 2
def baseEnd_730379 : Nat := 18520270960508796173015

theorem tailTrace_730379 : CollatzResearch.WordTrace tailWord_730379 prefixEnd_730379 18520270960508796173015 := by
  unfold tailWord_730379
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639110620969096647346191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17759407080646064431564127 26639110620969096647346191)
  ·
    refine ⟨39958665931453644971019287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26639110620969096647346191 39958665931453644971019287)
    ·
      refine ⟨59937998897180467456528931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39958665931453644971019287 59937998897180467456528931)
      ·
        refine ⟨89906998345770701184793397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59937998897180467456528931 89906998345770701184793397)
        ·
          refine ⟨8428781094916003236074381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89906998345770701184793397 8428781094916003236074381)
          ·
            refine ⟨3160792910593501213527893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8428781094916003236074381 3160792910593501213527893)
            ·
              refine ⟨18520270960508796173015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3160792910593501213527893 18520270960508796173015)
              ·
                rfl

theorem cell21_730379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 9].length) (baseStart_730379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730379 prefixEnd_730379 := by exact prefixLift 730379
  have htrace : WordTrace (prefixWord ++ tailWord_730379) baseStart_730379 baseEnd_730379 := by
    simpa [prefixWord, tailWord_730379, baseEnd_730379] using wordTrace_append hprefix tailTrace_730379
  have hstable : (prefixWord ++ tailWord_730379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730379).length < 2 ^ (prefixWord ++ tailWord_730379).sum := by decide
  have hdescent : baseEnd_730379 < baseStart_730379 := by decide
  rcases family_descends (prefixWord ++ tailWord_730379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730413 : List Nat := [1, 5, 3, 1, 1, 1, 2, 7]
def baseStart_730413 : Nat := 118140960795 + 730413 * 2 ^ 59
def prefixEnd_730413 : Nat := 4983230072969 + 3 ^ 40 * 730413 * 2
def baseEnd_730413 : Nat := 55563399302600887330133

theorem tailTrace_730413 : CollatzResearch.WordTrace tailWord_730413 prefixEnd_730413 55563399302600887330133 := by
  unfold tailWord_730413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26640350702845920454083893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17760233801897280302722595 26640350702845920454083893)
  ·
    refine ⟨2497532878391805042570365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26640350702845920454083893 2497532878391805042570365)
    ·
      refine ⟨936574829396926890963887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2497532878391805042570365 936574829396926890963887)
      ·
        refine ⟨1404862244095390336445831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936574829396926890963887 1404862244095390336445831)
        ·
          refine ⟨2107293366143085504668747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404862244095390336445831 2107293366143085504668747)
          ·
            refine ⟨3160940049214628257003121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107293366143085504668747 3160940049214628257003121)
            ·
              refine ⟨2370705036910971192752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160940049214628257003121 2370705036910971192752341)
              ·
                refine ⟨55563399302600887330133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2370705036910971192752341 55563399302600887330133)
                ·
                  rfl

theorem cell21_730413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_730413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730413 prefixEnd_730413 := by exact prefixLift 730413
  have htrace : WordTrace (prefixWord ++ tailWord_730413) baseStart_730413 baseEnd_730413 := by
    simpa [prefixWord, tailWord_730413, baseEnd_730413] using wordTrace_append hprefix tailTrace_730413
  have hstable : (prefixWord ++ tailWord_730413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730413).length < 2 ^ (prefixWord ++ tailWord_730413).sum := by decide
  have hdescent : baseEnd_730413 < baseStart_730413 := by decide
  rcases family_descends (prefixWord ++ tailWord_730413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730441 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_730441 : Nat := 118140960795 + 730441 * 2 ^ 59
def prefixEnd_730441 : Nat := 4983230072969 + 3 ^ 40 * 730441 * 2
def baseEnd_730441 : Nat := 166696587889280835523675

theorem tailTrace_730441 : CollatzResearch.WordTrace tailWord_730441 prefixEnd_730441 166696587889280835523675 := by
  unfold tailWord_730441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641371946744481236103177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17760914631162987490735451 26641371946744481236103177)
  ·
    refine ⟨19981028960058360927077383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26641371946744481236103177 19981028960058360927077383)
    ·
      refine ⟨29971543440087541390616075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981028960058360927077383 29971543440087541390616075)
      ·
        refine ⟨44957315160131312085924113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29971543440087541390616075 44957315160131312085924113)
        ·
          refine ⟨33717986370098484064443085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44957315160131312085924113 33717986370098484064443085)
          ·
            refine ⟨12644244888786931524166157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33717986370098484064443085 12644244888786931524166157)
            ·
              refine ⟨4741591833295099321562309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12644244888786931524166157 4741591833295099321562309)
              ·
                refine ⟨889048468742831122792933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4741591833295099321562309 889048468742831122792933)
                ·
                  refine ⟨166696587889280835523675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889048468742831122792933 166696587889280835523675)
                  ·
                    rfl

theorem cell21_730441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_730441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730441 prefixEnd_730441 := by exact prefixLift 730441
  have htrace : WordTrace (prefixWord ++ tailWord_730441) baseStart_730441 baseEnd_730441 := by
    simpa [prefixWord, tailWord_730441, baseEnd_730441] using wordTrace_append hprefix tailTrace_730441
  have hstable : (prefixWord ++ tailWord_730441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730441).length < 2 ^ (prefixWord ++ tailWord_730441).sum := by decide
  have hdescent : baseEnd_730441 < baseStart_730441 := by decide
  rcases family_descends (prefixWord ++ tailWord_730441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730444 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_730444 : Nat := 118140960795 + 730444 * 2 ^ 59
def prefixEnd_730444 : Nat := 4983230072969 + 3 ^ 40 * 730444 * 2
def baseEnd_730444 : Nat := 166697272530153496973669

theorem tailTrace_730444 : CollatzResearch.WordTrace tailWord_730444 prefixEnd_730444 166697272530153496973669 := by
  unfold tailWord_730444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320740682866806374231193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17760987577155741832308257 13320740682866806374231193)
  ·
    refine ⟨9990555512150104780673395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13320740682866806374231193 9990555512150104780673395)
    ·
      refine ⟨14985833268225157171010093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9990555512150104780673395 14985833268225157171010093)
      ·
        refine ⟨5619687475584433939128785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14985833268225157171010093 5619687475584433939128785)
        ·
          refine ⟨4214765606688325454346589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5619687475584433939128785 4214765606688325454346589)
          ·
            refine ⟨1580537102508122045379971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4214765606688325454346589 1580537102508122045379971)
            ·
              refine ⟨2370805653762183068069957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580537102508122045379971 2370805653762183068069957)
              ·
                refine ⟨444526060080409325263117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2370805653762183068069957 444526060080409325263117)
                ·
                  refine ⟨166697272530153496973669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444526060080409325263117 166697272530153496973669)
                  ·
                    rfl

theorem cell21_730444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_730444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730444 prefixEnd_730444 := by exact prefixLift 730444
  have htrace : WordTrace (prefixWord ++ tailWord_730444) baseStart_730444 baseEnd_730444 := by
    simpa [prefixWord, tailWord_730444, baseEnd_730444] using wordTrace_append hprefix tailTrace_730444
  have hstable : (prefixWord ++ tailWord_730444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730444).length < 2 ^ (prefixWord ++ tailWord_730444).sum := by decide
  have hdescent : baseEnd_730444 < baseStart_730444 := by decide
  rcases family_descends (prefixWord ++ tailWord_730444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730478 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_730478 : Nat := 118140960795 + 730478 * 2 ^ 59
def prefixEnd_730478 : Nat := 4983230072969 + 3 ^ 40 * 730478 * 2
def baseEnd_730478 : Nat := 166705031793376993406933

theorem tailTrace_730478 : CollatzResearch.WordTrace tailWord_730478 prefixEnd_730478 166705031793376993406933 := by
  unfold tailWord_730478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330340180951304569400011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17761814298406957703466725 3330340180951304569400011)
  ·
    refine ⟨4995510271426956854100017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330340180951304569400011 4995510271426956854100017)
    ·
      refine ⟨3746632703570217640575013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4995510271426956854100017 3746632703570217640575013)
      ·
        refine ⟨702493631919415807607815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3746632703570217640575013 702493631919415807607815)
        ·
          refine ⟨1053740447879123711411723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702493631919415807607815 1053740447879123711411723)
          ·
            refine ⟨1580610671818685567117585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053740447879123711411723 1580610671818685567117585)
            ·
              refine ⟨1185458003864014175338189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580610671818685567117585 1185458003864014175338189)
              ·
                refine ⟨444546751449005315751821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185458003864014175338189 444546751449005315751821)
                ·
                  refine ⟨166705031793376993406933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444546751449005315751821 166705031793376993406933)
                  ·
                    rfl

theorem cell21_730478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_730478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730478 prefixEnd_730478 := by exact prefixLift 730478
  have htrace : WordTrace (prefixWord ++ tailWord_730478) baseStart_730478 baseEnd_730478 := by
    simpa [prefixWord, tailWord_730478, baseEnd_730478] using wordTrace_append hprefix tailTrace_730478
  have hstable : (prefixWord ++ tailWord_730478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730478).length < 2 ^ (prefixWord ++ tailWord_730478).sum := by decide
  have hdescent : baseEnd_730478 < baseStart_730478 := by decide
  rcases family_descends (prefixWord ++ tailWord_730478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730503 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_730503 : Nat := 118140960795 + 730503 * 2 ^ 59
def prefixEnd_730503 : Nat := 4983230072969 + 3 ^ 40 * 730503 * 2
def baseEnd_730503 : Nat := 166710737133982505490215

theorem tailTrace_730503 : CollatzResearch.WordTrace tailWord_730503 prefixEnd_730503 166710737133982505490215 := by
  unfold tailWord_730503
  simp only [CollatzResearch.WordTrace]
  refine ⟨26643633272519865824860163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17762422181679910549906775 26643633272519865824860163)
  ·
    refine ⟨39965449908779798737290245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26643633272519865824860163 39965449908779798737290245)
    ·
      refine ⟨7493521857896212263241921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39965449908779798737290245 7493521857896212263241921)
      ·
        refine ⟨5620141393422159197431441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7493521857896212263241921 5620141393422159197431441)
        ·
          refine ⟨4215106045066619398073581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620141393422159197431441 4215106045066619398073581)
          ·
            refine ⟨1580664766899982274277593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4215106045066619398073581 1580664766899982274277593)
            ·
              refine ⟨1185498575174986705708195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580664766899982274277593 1185498575174986705708195)
              ·
                refine ⟨1778247862762480058562293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185498575174986705708195 1778247862762480058562293)
                ·
                  refine ⟨166710737133982505490215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778247862762480058562293 166710737133982505490215)
                  ·
                    rfl

theorem cell21_730503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_730503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730503 prefixEnd_730503 := by exact prefixLift 730503
  have htrace : WordTrace (prefixWord ++ tailWord_730503) baseStart_730503 baseEnd_730503 := by
    simpa [prefixWord, tailWord_730503, baseEnd_730503] using wordTrace_append hprefix tailTrace_730503
  have hstable : (prefixWord ++ tailWord_730503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730503).length < 2 ^ (prefixWord ++ tailWord_730503).sum := by decide
  have hdescent : baseEnd_730503 < baseStart_730503 := by decide
  rcases family_descends (prefixWord ++ tailWord_730503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730517 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_730517 : Nat := 118140960795 + 730517 * 2 ^ 59
def prefixEnd_730517 : Nat := 4983230072969 + 3 ^ 40 * 730517 * 2
def baseEnd_730517 : Nat := 166713932124721592256853

theorem tailTrace_730517 : CollatzResearch.WordTrace tailWord_730517 prefixEnd_730517 166713932124721592256853 := by
  unfold tailWord_730517
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644143894469146215869805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17762762596312764143913203 26644143894469146215869805)
  ·
    refine ⟨9991553960425929830951177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26644143894469146215869805 9991553960425929830951177)
    ·
      refine ⟨7493665470319447373213383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9991553960425929830951177 7493665470319447373213383)
      ·
        refine ⟨11240498205479171059820075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7493665470319447373213383 11240498205479171059820075)
        ·
          refine ⟨16860747308218756589730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11240498205479171059820075 16860747308218756589730113)
          ·
            refine ⟨12645560481164067442297585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16860747308218756589730113 12645560481164067442297585)
            ·
              refine ⟨9484170360873050581723189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12645560481164067442297585 9484170360873050581723189)
              ·
                refine ⟨889140971331848492036549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9484170360873050581723189 889140971331848492036549)
                ·
                  refine ⟨166713932124721592256853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889140971331848492036549 166713932124721592256853)
                  ·
                    rfl

theorem cell21_730517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_730517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730517 prefixEnd_730517 := by exact prefixLift 730517
  have htrace : WordTrace (prefixWord ++ tailWord_730517) baseStart_730517 baseEnd_730517 := by
    simpa [prefixWord, tailWord_730517, baseEnd_730517] using wordTrace_append hprefix tailTrace_730517
  have hstable : (prefixWord ++ tailWord_730517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730517).length < 2 ^ (prefixWord ++ tailWord_730517).sum := by decide
  have hdescent : baseEnd_730517 < baseStart_730517 := by decide
  rcases family_descends (prefixWord ++ tailWord_730517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730531 : List Nat := [1, 1, 1, 4, 1, 3, 3, 7]
def baseStart_730531 : Nat := 118140960795 + 730531 * 2 ^ 59
def prefixEnd_730531 : Nat := 4983230072969 + 3 ^ 40 * 730531 * 2
def baseEnd_730531 : Nat := 55572375705153559674497

theorem tailTrace_730531 : CollatzResearch.WordTrace tailWord_730531 prefixEnd_730531 55572375705153559674497 := by
  unfold tailWord_730531
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644654516418426606879447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17763103010945617737919631 26644654516418426606879447)
  ·
    refine ⟨39966981774627639910319171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26644654516418426606879447 39966981774627639910319171)
    ·
      refine ⟨59950472661941459865478757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39966981774627639910319171 59950472661941459865478757)
      ·
        refine ⟨11240713624114023724777267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59950472661941459865478757 11240713624114023724777267)
        ·
          refine ⟨16861070436171035587165901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11240713624114023724777267 16861070436171035587165901)
          ·
            refine ⟨6322901413564138345187213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16861070436171035587165901 6322901413564138345187213)
            ·
              refine ⟨2371088030086551879445205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6322901413564138345187213 2371088030086551879445205)
              ·
                refine ⟨55572375705153559674497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2371088030086551879445205 55572375705153559674497)
                ·
                  rfl

theorem cell21_730531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_730531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730531 prefixEnd_730531 := by exact prefixLift 730531
  have htrace : WordTrace (prefixWord ++ tailWord_730531) baseStart_730531 baseEnd_730531 := by
    simpa [prefixWord, tailWord_730531, baseEnd_730531] using wordTrace_append hprefix tailTrace_730531
  have hstable : (prefixWord ++ tailWord_730531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730531).length < 2 ^ (prefixWord ++ tailWord_730531).sum := by decide
  have hdescent : baseEnd_730531 < baseStart_730531 := by decide
  rcases family_descends (prefixWord ++ tailWord_730531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730610 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_730610 : Nat := 118140960795 + 730610 * 2 ^ 59
def prefixEnd_730610 : Nat := 4983230072969 + 3 ^ 40 * 730610 * 2
def baseEnd_730610 : Nat := 166735155991774097206663

theorem tailTrace_730610 : CollatzResearch.WordTrace tailWord_730610 prefixEnd_730610 166735155991774097206663 := by
  unfold tailWord_730610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661883970783055774751321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17765023922088148732670189 6661883970783055774751321)
  ·
    refine ⟨4996412978087291831063491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6661883970783055774751321 4996412978087291831063491)
    ·
      refine ⟨7494619467130937746595237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996412978087291831063491 7494619467130937746595237)
      ·
        refine ⟨1405241150087050827486607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7494619467130937746595237 1405241150087050827486607)
        ·
          refine ⟨2107861725130576241229911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405241150087050827486607 2107861725130576241229911)
          ·
            refine ⟨3161792587695864361844867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107861725130576241229911 3161792587695864361844867)
            ·
              refine ⟨4742688881543796542767301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161792587695864361844867 4742688881543796542767301)
              ·
                refine ⟨889254165289461851768869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4742688881543796542767301 889254165289461851768869)
                ·
                  refine ⟨166735155991774097206663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889254165289461851768869 166735155991774097206663)
                  ·
                    rfl

theorem cell21_730610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_730610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730610 prefixEnd_730610 := by exact prefixLift 730610
  have htrace : WordTrace (prefixWord ++ tailWord_730610) baseStart_730610 baseEnd_730610 := by
    simpa [prefixWord, tailWord_730610, baseEnd_730610] using wordTrace_append hprefix tailTrace_730610
  have hstable : (prefixWord ++ tailWord_730610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730610).length < 2 ^ (prefixWord ++ tailWord_730610).sum := by decide
  have hdescent : baseEnd_730610 < baseStart_730610 := by decide
  rcases family_descends (prefixWord ++ tailWord_730610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730613 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 3]
def baseStart_730613 : Nat := 118140960795 + 730613 * 2 ^ 59
def prefixEnd_730613 : Nat := 4983230072969 + 3 ^ 40 * 730613 * 2
def baseEnd_730613 : Nat := 166735840632646758656657

theorem tailTrace_730613 : CollatzResearch.WordTrace tailWord_730613 prefixEnd_730613 166735840632646758656657 := by
  unfold tailWord_730613
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647645302121354611364493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17765096868080903074242995 26647645302121354611364493)
  ·
    refine ⟨9992866988295507979261685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26647645302121354611364493 9992866988295507979261685)
    ·
      refine ⟨936831280152703873055783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9992866988295507979261685 936831280152703873055783)
      ·
        refine ⟨1405246920229055809583675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936831280152703873055783 1405246920229055809583675)
        ·
          refine ⟨2107870380343583714375513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405246920229055809583675 2107870380343583714375513)
          ·
            refine ⟨1580902785257687785781635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107870380343583714375513 1580902785257687785781635)
            ·
              refine ⟨2371354177886531678672453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580902785257687785781635 2371354177886531678672453)
              ·
                refine ⟨444628908353724689751085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2371354177886531678672453 444628908353724689751085)
                ·
                  refine ⟨166735840632646758656657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444628908353724689751085 166735840632646758656657)
                  ·
                    rfl

theorem cell21_730613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_730613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730613 prefixEnd_730613 := by exact prefixLift 730613
  have htrace : WordTrace (prefixWord ++ tailWord_730613) baseStart_730613 baseEnd_730613 := by
    simpa [prefixWord, tailWord_730613, baseEnd_730613] using wordTrace_append hprefix tailTrace_730613
  have hstable : (prefixWord ++ tailWord_730613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730613).length < 2 ^ (prefixWord ++ tailWord_730613).sum := by decide
  have hdescent : baseEnd_730613 < baseStart_730613 := by decide
  rcases family_descends (prefixWord ++ tailWord_730613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730630 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_730630 : Nat := 118140960795 + 730630 * 2 ^ 59
def prefixEnd_730630 : Nat := 4983230072969 + 3 ^ 40 * 730630 * 2
def baseEnd_730630 : Nat := 166739720264258506873289

theorem tailTrace_730630 : CollatzResearch.WordTrace tailWord_730630 prefixEnd_730630 166739720264258506873289 := by
  unfold tailWord_730630
  simp only [CollatzResearch.WordTrace]
  refine ⟨832758291970617703585417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17765510228706511009822229 832758291970617703585417)
  ·
    refine ⟨624568718977963277689063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 832758291970617703585417 624568718977963277689063)
    ·
      refine ⟨936853078466944916533595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624568718977963277689063 936853078466944916533595)
      ·
        refine ⟨1405279617700417374800393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936853078466944916533595 1405279617700417374800393)
        ·
          refine ⟨1053959713275313031100295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1405279617700417374800393 1053959713275313031100295)
          ·
            refine ⟨1580939569912969546650443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053959713275313031100295 1580939569912969546650443)
            ·
              refine ⟨2371409354869454319975665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580939569912969546650443 2371409354869454319975665)
              ·
                refine ⟨1778557016152090739981749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371409354869454319975665 1778557016152090739981749)
                ·
                  refine ⟨166739720264258506873289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778557016152090739981749 166739720264258506873289)
                  ·
                    rfl

theorem cell21_730630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_730630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730630 prefixEnd_730630 := by exact prefixLift 730630
  have htrace : WordTrace (prefixWord ++ tailWord_730630) baseStart_730630 baseEnd_730630 := by
    simpa [prefixWord, tailWord_730630, baseEnd_730630] using wordTrace_append hprefix tailTrace_730630
  have hstable : (prefixWord ++ tailWord_730630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730630).length < 2 ^ (prefixWord ++ tailWord_730630).sum := by decide
  have hdescent : baseEnd_730630 < baseStart_730630 := by decide
  rcases family_descends (prefixWord ++ tailWord_730630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730655 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 3]
def baseStart_730655 : Nat := 118140960795 + 730655 * 2 ^ 59
def prefixEnd_730655 : Nat := 4983230072969 + 3 ^ 40 * 730655 * 2
def baseEnd_730655 : Nat := 166745425604864018956571

theorem tailTrace_730655 : CollatzResearch.WordTrace tailWord_730655 prefixEnd_730655 166745425604864018956571 := by
  unfold tailWord_730655
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649177167969195784393419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17766118111979463856262279 26649177167969195784393419)
  ·
    refine ⟨39973765751953793676590129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26649177167969195784393419 39973765751953793676590129)
    ·
      refine ⟨29980324313965345257442597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39973765751953793676590129 29980324313965345257442597)
      ·
        refine ⟨5621310808868502235770487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29980324313965345257442597 5621310808868502235770487)
        ·
          refine ⟨8431966213302753353655731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621310808868502235770487 8431966213302753353655731)
          ·
            refine ⟨12647949319954130030483597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431966213302753353655731 12647949319954130030483597)
            ·
              refine ⟨4742980994982798761431349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12647949319954130030483597 4742980994982798761431349)
              ·
                refine ⟨444654468279637383884189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4742980994982798761431349 444654468279637383884189)
                ·
                  refine ⟨166745425604864018956571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444654468279637383884189 166745425604864018956571)
                  ·
                    rfl

theorem cell21_730655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3].length) (baseStart_730655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730655 prefixEnd_730655 := by exact prefixLift 730655
  have htrace : WordTrace (prefixWord ++ tailWord_730655) baseStart_730655 baseEnd_730655 := by
    simpa [prefixWord, tailWord_730655, baseEnd_730655] using wordTrace_append hprefix tailTrace_730655
  have hstable : (prefixWord ++ tailWord_730655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730655).length < 2 ^ (prefixWord ++ tailWord_730655).sum := by decide
  have hdescent : baseEnd_730655 < baseStart_730655 := by decide
  rcases family_descends (prefixWord ++ tailWord_730655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730700 : List Nat := [2, 2, 1, 3, 1, 3, 4, 5]
def baseStart_730700 : Nat := 118140960795 + 730700 * 2 ^ 59
def prefixEnd_730700 : Nat := 4983230072969 + 3 ^ 40 * 730700 * 2
def baseEnd_730700 : Nat := 55585231739317980235493

theorem tailTrace_730700 : CollatzResearch.WordTrace tailWord_730700 prefixEnd_730700 55585231739317980235493 := by
  unfold tailWord_730700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325409226403084234890777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17767212301870778979854369 13325409226403084234890777)
  ·
    refine ⟨9994056919802313176168083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13325409226403084234890777 9994056919802313176168083)
    ·
      refine ⟨14991085379703469764252125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9994056919802313176168083 14991085379703469764252125)
      ·
        refine ⟨5621657017388801161594547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14991085379703469764252125 5621657017388801161594547)
        ·
          refine ⟨8432485526083201742391821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621657017388801161594547 8432485526083201742391821)
          ·
            refine ⟨3162182072281200653396933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8432485526083201742391821 3162182072281200653396933)
            ·
              refine ⟨592909138552725122511925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3162182072281200653396933 592909138552725122511925)
              ·
                refine ⟨55585231739317980235493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 592909138552725122511925 55585231739317980235493)
                ·
                  rfl

theorem cell21_730700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_730700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730700 prefixEnd_730700 := by exact prefixLift 730700
  have htrace : WordTrace (prefixWord ++ tailWord_730700) baseStart_730700 baseEnd_730700 := by
    simpa [prefixWord, tailWord_730700, baseEnd_730700] using wordTrace_append hprefix tailTrace_730700
  have hstable : (prefixWord ++ tailWord_730700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730700).length < 2 ^ (prefixWord ++ tailWord_730700).sum := by decide
  have hdescent : baseEnd_730700 < baseStart_730700 := by decide
  rcases family_descends (prefixWord ++ tailWord_730700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730745 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_730745 : Nat := 118140960795 + 730745 * 2 ^ 59
def prefixEnd_730745 : Nat := 4983230072969 + 3 ^ 40 * 730745 * 2
def baseEnd_730745 : Nat := 166765964831043862456387

theorem tailTrace_730745 : CollatzResearch.WordTrace tailWord_730745 prefixEnd_730745 166765964831043862456387 := by
  unfold tailWord_730745
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652459737643141155169689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17768306491762094103446459 26652459737643141155169689)
  ·
    refine ⟨19989344803232355866377267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26652459737643141155169689 19989344803232355866377267)
    ·
      refine ⟨29984017204848533799565901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19989344803232355866377267 29984017204848533799565901)
      ·
        refine ⟨11244006451818200174837213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29984017204848533799565901 11244006451818200174837213)
        ·
          refine ⟨4216502419431825065563955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11244006451818200174837213 4216502419431825065563955)
          ·
            refine ⟨6324753629147737598345933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216502419431825065563955 6324753629147737598345933)
            ·
              refine ⟨2371782610930401599379725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6324753629147737598345933 2371782610930401599379725)
              ·
                refine ⟨889418479098900599767397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371782610930401599379725 889418479098900599767397)
                ·
                  refine ⟨166765964831043862456387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889418479098900599767397 166765964831043862456387)
                  ·
                    rfl

theorem cell21_730745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_730745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730745 prefixEnd_730745 := by exact prefixLift 730745
  have htrace : WordTrace (prefixWord ++ tailWord_730745) baseStart_730745 baseEnd_730745 := by
    simpa [prefixWord, tailWord_730745, baseEnd_730745] using wordTrace_append hprefix tailTrace_730745
  have hstable : (prefixWord ++ tailWord_730745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730745).length < 2 ^ (prefixWord ++ tailWord_730745).sum := by decide
  have hdescent : baseEnd_730745 < baseStart_730745 := by decide
  rcases family_descends (prefixWord ++ tailWord_730745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730759 : List Nat := [1, 1, 4, 2, 1, 3, 2, 7]
def baseStart_730759 : Nat := 118140960795 + 730759 * 2 ^ 59
def prefixEnd_730759 : Nat := 4983230072969 + 3 ^ 40 * 730759 * 2
def baseEnd_730759 : Nat := 55589719940594316407675

theorem tailTrace_730759 : CollatzResearch.WordTrace tailWord_730759 prefixEnd_730759 55589719940594316407675 := by
  unfold tailWord_730759
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652970359592421546179331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17768646906394947697452887 26652970359592421546179331)
  ·
    refine ⟨39979455539388632319268997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26652970359592421546179331 39979455539388632319268997)
    ·
      refine ⟨7496147913635368559862937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39979455539388632319268997 7496147913635368559862937)
      ·
        refine ⟨5622110935226526419897203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496147913635368559862937 5622110935226526419897203)
        ·
          refine ⟨8433166402839789629845805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622110935226526419897203 8433166402839789629845805)
          ·
            refine ⟨3162437401064921111192177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8433166402839789629845805 3162437401064921111192177)
            ·
              refine ⟨2371828050798690833394133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3162437401064921111192177 2371828050798690833394133)
              ·
                refine ⟨55589719940594316407675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2371828050798690833394133 55589719940594316407675)
                ·
                  rfl

theorem cell21_730759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_730759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730759 prefixEnd_730759 := by exact prefixLift 730759
  have htrace : WordTrace (prefixWord ++ tailWord_730759) baseStart_730759 baseEnd_730759 := by
    simpa [prefixWord, tailWord_730759, baseEnd_730759] using wordTrace_append hprefix tailTrace_730759
  have hstable : (prefixWord ++ tailWord_730759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730759).length < 2 ^ (prefixWord ++ tailWord_730759).sum := by decide
  have hdescent : baseEnd_730759 < baseStart_730759 := by decide
  rcases family_descends (prefixWord ++ tailWord_730759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730782 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_730782 : Nat := 118140960795 + 730782 * 2 ^ 59
def prefixEnd_730782 : Nat := 4983230072969 + 3 ^ 40 * 730782 * 2
def baseEnd_730782 : Nat := 166774408735140020339645

theorem tailTrace_730782 : CollatzResearch.WordTrace tailWord_730782 prefixEnd_730782 166774408735140020339645 := by
  unfold tailWord_730782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3331726154813637059283325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17769206159006064316177733 3331726154813637059283325)
  ·
    refine ⟨1249397308055113897231247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3331726154813637059283325 1249397308055113897231247)
    ·
      refine ⟨1874095962082670845846871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249397308055113897231247 1874095962082670845846871)
      ·
        refine ⟨2811143943124006268770307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874095962082670845846871 2811143943124006268770307)
        ·
          refine ⟨4216715914686009403155461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811143943124006268770307 4216715914686009403155461)
          ·
            refine ⟨790634234003626763091649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4216715914686009403155461 790634234003626763091649)
            ·
              refine ⟨592975675502720072318737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790634234003626763091649 592975675502720072318737)
              ·
                refine ⟨444731756627040054239053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592975675502720072318737 444731756627040054239053)
                ·
                  refine ⟨166774408735140020339645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444731756627040054239053 166774408735140020339645)
                  ·
                    rfl

theorem cell21_730782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_730782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730782 prefixEnd_730782 := by exact prefixLift 730782
  have htrace : WordTrace (prefixWord ++ tailWord_730782) baseStart_730782 baseEnd_730782 := by
    simpa [prefixWord, tailWord_730782, baseEnd_730782] using wordTrace_append hprefix tailTrace_730782
  have hstable : (prefixWord ++ tailWord_730782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730782).length < 2 ^ (prefixWord ++ tailWord_730782).sum := by decide
  have hdescent : baseEnd_730782 < baseStart_730782 := by decide
  rcases family_descends (prefixWord ++ tailWord_730782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730866 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_730866 : Nat := 118140960795 + 730866 * 2 ^ 59
def prefixEnd_730866 : Nat := 4983230072969 + 3 ^ 40 * 730866 * 2
def baseEnd_730866 : Nat := 166793578679574540939473

theorem tailTrace_730866 : CollatzResearch.WordTrace tailWord_730866 prefixEnd_730866 166793578679574540939473 := by
  unfold tailWord_730866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6664218242551194705081113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17771248646803185880216301 6664218242551194705081113)
  ·
    refine ⟨4998163681913396028810835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6664218242551194705081113 4998163681913396028810835)
    ·
      refine ⟨7497245522870094043216253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4998163681913396028810835 7497245522870094043216253)
      ·
        refine ⟨2811467071076285266206095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7497245522870094043216253 2811467071076285266206095)
        ·
          refine ⟨4217200606614427899309143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811467071076285266206095 4217200606614427899309143)
          ·
            refine ⟨6325800909921641848963715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217200606614427899309143 6325800909921641848963715)
            ·
              refine ⟨9488701364882462773445573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325800909921641848963715 9488701364882462773445573)
              ·
                refine ⟨1779131505915461770021045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9488701364882462773445573 1779131505915461770021045)
                ·
                  refine ⟨166793578679574540939473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779131505915461770021045 166793578679574540939473)
                  ·
                    rfl

theorem cell21_730866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_730866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730866 prefixEnd_730866 := by exact prefixLift 730866
  have htrace : WordTrace (prefixWord ++ tailWord_730866) baseStart_730866 baseEnd_730866 := by
    simpa [prefixWord, tailWord_730866, baseEnd_730866] using wordTrace_append hprefix tailTrace_730866
  have hstable : (prefixWord ++ tailWord_730866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730866).length < 2 ^ (prefixWord ++ tailWord_730866).sum := by decide
  have hdescent : baseEnd_730866 < baseStart_730866 := by decide
  rcases family_descends (prefixWord ++ tailWord_730866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730883 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 3]
def baseStart_730883 : Nat := 118140960795 + 730883 * 2 ^ 59
def prefixEnd_730883 : Nat := 4983230072969 + 3 ^ 40 * 730883 * 2
def baseEnd_730883 : Nat := 166797458311186289156105

theorem tailTrace_730883 : CollatzResearch.WordTrace tailWord_730883 prefixEnd_730883 166797458311186289156105 := by
  unfold tailWord_730883
  simp only [CollatzResearch.WordTrace]
  refine ⟨26657493011143190723693303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17771662007428793815795535 26657493011143190723693303)
  ·
    refine ⟨39986239516714786085539955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26657493011143190723693303 39986239516714786085539955)
    ·
      refine ⟨59979359275072179128309933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39986239516714786085539955 59979359275072179128309933)
      ·
        refine ⟨22492259728152067173116225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59979359275072179128309933 22492259728152067173116225)
        ·
          refine ⟨16869194796114050379837169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22492259728152067173116225 16869194796114050379837169)
          ·
            refine ⟨12651896097085537784877877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16869194796114050379837169 12651896097085537784877877)
            ·
              refine ⟨1186115259101769167332301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12651896097085537784877877 1186115259101769167332301)
              ·
                refine ⟨444793222163163437749613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1186115259101769167332301 444793222163163437749613)
                ·
                  refine ⟨166797458311186289156105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444793222163163437749613 166797458311186289156105)
                  ·
                    rfl

theorem cell21_730883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 3].length) (baseStart_730883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730883 prefixEnd_730883 := by exact prefixLift 730883
  have htrace : WordTrace (prefixWord ++ tailWord_730883) baseStart_730883 baseEnd_730883 := by
    simpa [prefixWord, tailWord_730883, baseEnd_730883] using wordTrace_append hprefix tailTrace_730883
  have hstable : (prefixWord ++ tailWord_730883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730883).length < 2 ^ (prefixWord ++ tailWord_730883).sum := by decide
  have hdescent : baseEnd_730883 < baseStart_730883 := by decide
  rcases family_descends (prefixWord ++ tailWord_730883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730911 : List Nat := [1, 1, 2, 4, 2, 1, 4, 6]
def baseStart_730911 : Nat := 118140960795 + 730911 * 2 ^ 59
def prefixEnd_730911 : Nat := 4983230072969 + 3 ^ 40 * 730911 * 2
def baseEnd_730911 : Nat := 55601282764221487563127

theorem tailTrace_730911 : CollatzResearch.WordTrace tailWord_730911 prefixEnd_730911 55601282764221487563127 := by
  unfold tailWord_730911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658514255041751505712587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17772342836694501003808391 26658514255041751505712587)
  ·
    refine ⟨39987771382562627258568881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26658514255041751505712587 39987771382562627258568881)
    ·
      refine ⟨29990828536921970443926661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39987771382562627258568881 29990828536921970443926661)
      ·
        refine ⟨5623280350672869458236249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29990828536921970443926661 5623280350672869458236249)
        ·
          refine ⟨4217460263004652093677187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5623280350672869458236249 4217460263004652093677187)
          ·
            refine ⟨6326190394506978140515781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217460263004652093677187 6326190394506978140515781)
            ·
              refine ⟨1186160698970058401346709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6326190394506978140515781 1186160698970058401346709)
              ·
                refine ⟨55601282764221487563127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1186160698970058401346709 55601282764221487563127)
                ·
                  rfl

theorem cell21_730911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_730911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_730911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_730911 prefixEnd_730911 := by exact prefixLift 730911
  have htrace : WordTrace (prefixWord ++ tailWord_730911) baseStart_730911 baseEnd_730911 := by
    simpa [prefixWord, tailWord_730911, baseEnd_730911] using wordTrace_append hprefix tailTrace_730911
  have hstable : (prefixWord ++ tailWord_730911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730911).length < 2 ^ (prefixWord ++ tailWord_730911).sum := by decide
  have hdescent : baseEnd_730911 < baseStart_730911 := by decide
  rcases family_descends (prefixWord ++ tailWord_730911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731001 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_731001 : Nat := 118140960795 + 731001 * 2 ^ 59
def prefixEnd_731001 : Nat := 4983230072969 + 3 ^ 40 * 731001 * 2
def baseEnd_731001 : Nat := 166824387518844306189197

theorem tailTrace_731001 : CollatzResearch.WordTrace tailWord_731001 prefixEnd_731001 166824387518844306189197 := by
  unfold tailWord_731001
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661796824715696876488857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774531216477131250992571 26661796824715696876488857)
  ·
    refine ⟨19996347618536772657366643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26661796824715696876488857 19996347618536772657366643)
    ·
      refine ⟨29994521427805158986049965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19996347618536772657366643 29994521427805158986049965)
      ·
        refine ⟨11247945535426934619768737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29994521427805158986049965 11247945535426934619768737)
        ·
          refine ⟨8435959151570200964826553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247945535426934619768737 8435959151570200964826553)
          ·
            refine ⟨6326969363677650723619915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8435959151570200964826553 6326969363677650723619915)
            ·
              refine ⟨9490454045516476085429873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326969363677650723619915 9490454045516476085429873)
              ·
                refine ⟨7117840534137357064072405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9490454045516476085429873 7117840534137357064072405)
                ·
                  refine ⟨166824387518844306189197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7117840534137357064072405 166824387518844306189197)
                  ·
                    rfl

theorem cell21_731001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_731001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731001 prefixEnd_731001 := by exact prefixLift 731001
  have htrace : WordTrace (prefixWord ++ tailWord_731001) baseStart_731001 baseEnd_731001 := by
    simpa [prefixWord, tailWord_731001, baseEnd_731001] using wordTrace_append hprefix tailTrace_731001
  have hstable : (prefixWord ++ tailWord_731001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731001).length < 2 ^ (prefixWord ++ tailWord_731001).sum := by decide
  have hdescent : baseEnd_731001 < baseStart_731001 := by decide
  rcases family_descends (prefixWord ++ tailWord_731001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731077 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_731077 : Nat := 118140960795 + 731077 * 2 ^ 59
def prefixEnd_731077 : Nat := 4983230072969 + 3 ^ 40 * 731077 * 2
def baseEnd_731077 : Nat := 166841731754285062922375

theorem tailTrace_731077 : CollatzResearch.WordTrace tailWord_731077 prefixEnd_731077 166841731754285062922375 := by
  unfold tailWord_731077
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664568772440361856255485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17776379181626907904170323 26664568772440361856255485)
  ·
    refine ⟨9999213289665135696095807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26664568772440361856255485 9999213289665135696095807)
    ·
      refine ⟨14998819934497703544143711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9999213289665135696095807 14998819934497703544143711)
      ·
        refine ⟨22498229901746555316215567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14998819934497703544143711 22498229901746555316215567)
        ·
          refine ⟨33747344852619832974323351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22498229901746555316215567 33747344852619832974323351)
          ·
            refine ⟨50621017278929749461485027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33747344852619832974323351 50621017278929749461485027)
            ·
              refine ⟨75931525918394624192227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50621017278929749461485027 75931525918394624192227541)
              ·
                refine ⟨1779645138712374004505333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75931525918394624192227541 1779645138712374004505333)
                ·
                  refine ⟨166841731754285062922375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779645138712374004505333 166841731754285062922375)
                  ·
                    rfl

theorem cell21_731077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_731077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731077 prefixEnd_731077 := by exact prefixLift 731077
  have htrace : WordTrace (prefixWord ++ tailWord_731077) baseStart_731077 baseEnd_731077 := by
    simpa [prefixWord, tailWord_731077, baseEnd_731077] using wordTrace_append hprefix tailTrace_731077
  have hstable : (prefixWord ++ tailWord_731077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731077).length < 2 ^ (prefixWord ++ tailWord_731077).sum := by decide
  have hdescent : baseEnd_731077 < baseStart_731077 := by decide
  rcases family_descends (prefixWord ++ tailWord_731077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731122 : List Nat := [3, 2, 1, 15]
def baseStart_731122 : Nat := 118140960795 + 731122 * 2 ^ 59
def prefixEnd_731122 : Nat := 4983230072969 + 3 ^ 40 * 731122 * 2
def baseEnd_731122 : Nat := 686633750483024628281

theorem tailTrace_731122 : CollatzResearch.WordTrace tailWord_731122 prefixEnd_731122 686633750483024628281 := by
  unfold tailWord_731122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666552514319333635410905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17777473371518223027762413 6666552514319333635410905)
  ·
    refine ⟨4999914385739500226558179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6666552514319333635410905 4999914385739500226558179)
    ·
      refine ⟨7499871578609250339837269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999914385739500226558179 7499871578609250339837269)
      ·
        refine ⟨686633750483024628281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 7499871578609250339837269 686633750483024628281)
        ·
          rfl

theorem cell21_731122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 15].length) (baseStart_731122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731122 prefixEnd_731122 := by exact prefixLift 731122
  have htrace : WordTrace (prefixWord ++ tailWord_731122) baseStart_731122 baseEnd_731122 := by
    simpa [prefixWord, tailWord_731122, baseEnd_731122] using wordTrace_append hprefix tailTrace_731122
  have hstable : (prefixWord ++ tailWord_731122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731122).length < 2 ^ (prefixWord ++ tailWord_731122).sum := by decide
  have hdescent : baseEnd_731122 < baseStart_731122 := by decide
  rcases family_descends (prefixWord ++ tailWord_731122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731176 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_731176 : Nat := 118140960795 + 731176 * 2 ^ 59
def prefixEnd_731176 : Nat := 4983230072969 + 3 ^ 40 * 731176 * 2
def baseEnd_731176 : Nat := 166864324903082890772173

theorem tailTrace_731176 : CollatzResearch.WordTrace tailWord_731176 prefixEnd_731176 166864324903082890772173 := by
  unfold tailWord_731176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334089799540850882054691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17778786399387801176072921 13334089799540850882054691)
  ·
    refine ⟨20001134699311276323082037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13334089799540850882054691 20001134699311276323082037)
    ·
      refine ⟨1875106378060432155288941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20001134699311276323082037 1875106378060432155288941)
      ·
        refine ⟨703164891772662058233353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1875106378060432155288941 703164891772662058233353)
        ·
          refine ⟨527373668829496543675015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 703164891772662058233353 527373668829496543675015)
          ·
            refine ⟨791060503244244815512523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527373668829496543675015 791060503244244815512523)
            ·
              refine ⟨1186590754866367223268785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791060503244244815512523 1186590754866367223268785)
              ·
                refine ⟨889943066149775417451589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186590754866367223268785 889943066149775417451589)
                ·
                  refine ⟨166864324903082890772173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889943066149775417451589 166864324903082890772173)
                  ·
                    rfl

theorem cell21_731176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_731176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731176 prefixEnd_731176 := by exact prefixLift 731176
  have htrace : WordTrace (prefixWord ++ tailWord_731176) baseStart_731176 baseEnd_731176 := by
    simpa [prefixWord, tailWord_731176, baseEnd_731176] using wordTrace_append hprefix tailTrace_731176
  have hstable : (prefixWord ++ tailWord_731176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731176).length < 2 ^ (prefixWord ++ tailWord_731176).sum := by decide
  have hdescent : baseEnd_731176 < baseStart_731176 := by decide
  rcases family_descends (prefixWord ++ tailWord_731176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731184 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_731184 : Nat := 118140960795 + 731184 * 2 ^ 59
def prefixEnd_731184 : Nat := 4983230072969 + 3 ^ 40 * 731184 * 2
def baseEnd_731184 : Nat := 166866150612076654638823

theorem tailTrace_731184 : CollatzResearch.WordTrace tailWord_731184 prefixEnd_731184 166866150612076654638823 := by
  unfold tailWord_731184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334235691526359565200303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17778980922035146086933737 13334235691526359565200303)
  ·
    refine ⟨20001353537289539347800455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13334235691526359565200303 20001353537289539347800455)
    ·
      refine ⟨30002030305934309021700683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20001353537289539347800455 30002030305934309021700683)
      ·
        refine ⟨45003045458901463532551025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30002030305934309021700683 45003045458901463532551025)
        ·
          refine ⟨33752284094176097649413269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45003045458901463532551025 33752284094176097649413269)
          ·
            refine ⟨1582138316914504577316247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33752284094176097649413269 1582138316914504577316247)
            ·
              refine ⟨2373207475371756865974371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582138316914504577316247 2373207475371756865974371)
              ·
                refine ⟨3559811213057635298961557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373207475371756865974371 3559811213057635298961557)
                ·
                  refine ⟨166866150612076654638823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3559811213057635298961557 166866150612076654638823)
                  ·
                    rfl

theorem cell21_731184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_731184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731184 prefixEnd_731184 := by exact prefixLift 731184
  have htrace : WordTrace (prefixWord ++ tailWord_731184) baseStart_731184 baseEnd_731184 := by
    simpa [prefixWord, tailWord_731184, baseEnd_731184] using wordTrace_append hprefix tailTrace_731184
  have hstable : (prefixWord ++ tailWord_731184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731184).length < 2 ^ (prefixWord ++ tailWord_731184).sum := by decide
  have hdescent : baseEnd_731184 < baseStart_731184 := by decide
  rcases family_descends (prefixWord ++ tailWord_731184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731356 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_731356 : Nat := 118140960795 + 731356 * 2 ^ 59
def prefixEnd_731356 : Nat := 4983230072969 + 3 ^ 40 * 731356 * 2
def baseEnd_731356 : Nat := 166905403355442577771805

theorem tailTrace_731356 : CollatzResearch.WordTrace tailWord_731356 prefixEnd_731356 166905403355442577771805 := by
  unfold tailWord_731356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337372369214796252830961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17783163158953061670441281 13337372369214796252830961)
  ·
    refine ⟨10003029276911097189623221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13337372369214796252830961 10003029276911097189623221)
    ·
      refine ⟨937783994710415361527177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10003029276911097189623221 937783994710415361527177)
      ·
        refine ⟨703337996032811521145383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 937783994710415361527177 703337996032811521145383)
        ·
          refine ⟨1055006994049217281718075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703337996032811521145383 1055006994049217281718075)
          ·
            refine ⟨1582510491073825922577113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055006994049217281718075 1582510491073825922577113)
            ·
              refine ⟨1186882868305369441932835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582510491073825922577113 1186882868305369441932835)
              ·
                refine ⟨1780324302458054162899253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186882868305369441932835 1780324302458054162899253)
                ·
                  refine ⟨166905403355442577771805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1780324302458054162899253 166905403355442577771805)
                  ·
                    rfl

theorem cell21_731356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_731356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731356 prefixEnd_731356 := by exact prefixLift 731356
  have htrace : WordTrace (prefixWord ++ tailWord_731356) baseStart_731356 baseEnd_731356 := by
    simpa [prefixWord, tailWord_731356, baseEnd_731356] using wordTrace_append hprefix tailTrace_731356
  have hstable : (prefixWord ++ tailWord_731356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731356).length < 2 ^ (prefixWord ++ tailWord_731356).sum := by decide
  have hdescent : baseEnd_731356 < baseStart_731356 := by decide
  rcases family_descends (prefixWord ++ tailWord_731356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731395 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_731395 : Nat := 118140960795 + 731395 * 2 ^ 59
def prefixEnd_731395 : Nat := 4983230072969 + 3 ^ 40 * 731395 * 2
def baseEnd_731395 : Nat := 166914303686787176621725

theorem tailTrace_731395 : CollatzResearch.WordTrace tailWord_731395 prefixEnd_731395 166914303686787176621725 := by
  unfold tailWord_731395
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676167185288302166331639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17784111456858868110887759 26676167185288302166331639)
  ·
    refine ⟨40014250777932453249497459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26676167185288302166331639 40014250777932453249497459)
    ·
      refine ⟨60021376166898679874246189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40014250777932453249497459 60021376166898679874246189)
      ·
        refine ⟨22508016062587004952842321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60021376166898679874246189 22508016062587004952842321)
        ·
          refine ⟨16881012046940253714631741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22508016062587004952842321 16881012046940253714631741)
          ·
            refine ⟨6330379517602595142986903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16881012046940253714631741 6330379517602595142986903)
            ·
              refine ⟨9495569276403892714480355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330379517602595142986903 9495569276403892714480355)
              ·
                refine ⟨14243353914605839071720533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495569276403892714480355 14243353914605839071720533)
                ·
                  refine ⟨166914303686787176621725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14243353914605839071720533 166914303686787176621725)
                  ·
                    rfl

theorem cell21_731395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_731395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731395 prefixEnd_731395 := by exact prefixLift 731395
  have htrace : WordTrace (prefixWord ++ tailWord_731395) baseStart_731395 baseEnd_731395 := by
    simpa [prefixWord, tailWord_731395, baseEnd_731395] using wordTrace_append hprefix tailTrace_731395
  have hstable : (prefixWord ++ tailWord_731395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731395).length < 2 ^ (prefixWord ++ tailWord_731395).sum := by decide
  have hdescent : baseEnd_731395 < baseStart_731395 := by decide
  rcases family_descends (prefixWord ++ tailWord_731395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731429 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_731429 : Nat := 118140960795 + 731429 * 2 ^ 59
def prefixEnd_731429 : Nat := 4983230072969 + 3 ^ 40 * 731429 * 2
def baseEnd_731429 : Nat := 166922062950010673054989

theorem tailTrace_731429 : CollatzResearch.WordTrace tailWord_731429 prefixEnd_731429 166922062950010673054989 := by
  unfold tailWord_731429
  simp only [CollatzResearch.WordTrace]
  refine ⟨26677407267165125973069341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17784938178110083982046227 26677407267165125973069341)
  ·
    refine ⟨10004027725186922239901003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26677407267165125973069341 10004027725186922239901003)
    ·
      refine ⟨15006041587780383359851505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10004027725186922239901003 15006041587780383359851505)
      ·
        refine ⟨11254531190835287519888629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15006041587780383359851505 11254531190835287519888629)
        ·
          refine ⟨1055112299140808204989559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11254531190835287519888629 1055112299140808204989559)
          ·
            refine ⟨1582668448711212307484339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055112299140808204989559 1582668448711212307484339)
            ·
              refine ⟨2374002673066818461226509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582668448711212307484339 2374002673066818461226509)
              ·
                refine ⟨890251002400056922959941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2374002673066818461226509 890251002400056922959941)
                ·
                  refine ⟨166922062950010673054989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890251002400056922959941 166922062950010673054989)
                  ·
                    rfl

theorem cell21_731429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_731429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731429 prefixEnd_731429 := by exact prefixLift 731429
  have htrace : WordTrace (prefixWord ++ tailWord_731429) baseStart_731429 baseEnd_731429 := by
    simpa [prefixWord, tailWord_731429, baseEnd_731429] using wordTrace_append hprefix tailTrace_731429
  have hstable : (prefixWord ++ tailWord_731429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731429).length < 2 ^ (prefixWord ++ tailWord_731429).sum := by decide
  have hdescent : baseEnd_731429 < baseStart_731429 := by decide
  rcases family_descends (prefixWord ++ tailWord_731429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731460 : List Nat := [2, 3, 4, 1, 3, 8]
def baseStart_731460 : Nat := 118140960795 + 731460 * 2 ^ 59
def prefixEnd_731460 : Nat := 4983230072969 + 3 ^ 40 * 731460 * 2
def baseEnd_731460 : Nat := 6182560650828204001417

theorem tailTrace_731460 : CollatzResearch.WordTrace tailWord_731460 prefixEnd_731460 6182560650828204001417 := by
  unfold tailWord_731460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339268965026409133723917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17785691953368545511631889 13339268965026409133723917)
  ·
    refine ⟨5002225861884903425146469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13339268965026409133723917 5002225861884903425146469)
    ·
      refine ⟨937917349103419392214963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5002225861884903425146469 937917349103419392214963)
      ·
        refine ⟨1406876023655129088322445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937917349103419392214963 1406876023655129088322445)
        ·
          refine ⟨527578508870673408120917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1406876023655129088322445 527578508870673408120917)
          ·
            refine ⟨6182560650828204001417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 527578508870673408120917 6182560650828204001417)
            ·
              rfl

theorem cell21_731460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 8].length) (baseStart_731460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731460 prefixEnd_731460 := by exact prefixLift 731460
  have htrace : WordTrace (prefixWord ++ tailWord_731460) baseStart_731460 baseEnd_731460 := by
    simpa [prefixWord, tailWord_731460, baseEnd_731460] using wordTrace_append hprefix tailTrace_731460
  have hstable : (prefixWord ++ tailWord_731460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731460).length < 2 ^ (prefixWord ++ tailWord_731460).sum := by decide
  have hdescent : baseEnd_731460 < baseStart_731460 := by decide
  rcases family_descends (prefixWord ++ tailWord_731460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731522 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_731522 : Nat := 118140960795 + 731522 * 2 ^ 59
def prefixEnd_731522 : Nat := 4983230072969 + 3 ^ 40 * 731522 * 2
def baseEnd_731522 : Nat := 166943286817063178004799

theorem tailTrace_731522 : CollatzResearch.WordTrace tailWord_731522 prefixEnd_731522 166943286817063178004799 := by
  unfold tailWord_731522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6670199813957050714051205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17787199503885468570803213 6670199813957050714051205)
  ·
    refine ⟨1250662465116947008884601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6670199813957050714051205 1250662465116947008884601)
    ·
      refine ⟨937996848837710256663451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250662465116947008884601 937996848837710256663451)
      ·
        refine ⟨1406995273256565384995177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937996848837710256663451 1406995273256565384995177)
        ·
          refine ⟨1055246454942424038746383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406995273256565384995177 1055246454942424038746383)
          ·
            refine ⟨1582869682413636058119575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055246454942424038746383 1582869682413636058119575)
            ·
              refine ⟨2374304523620454087179363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582869682413636058119575 2374304523620454087179363)
              ·
                refine ⟨3561456785430681130769045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374304523620454087179363 3561456785430681130769045)
                ·
                  refine ⟨166943286817063178004799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3561456785430681130769045 166943286817063178004799)
                  ·
                    rfl

theorem cell21_731522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_731522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731522 prefixEnd_731522 := by exact prefixLift 731522
  have htrace : WordTrace (prefixWord ++ tailWord_731522) baseStart_731522 baseEnd_731522 := by
    simpa [prefixWord, tailWord_731522, baseEnd_731522] using wordTrace_append hprefix tailTrace_731522
  have hstable : (prefixWord ++ tailWord_731522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731522).length < 2 ^ (prefixWord ++ tailWord_731522).sum := by decide
  have hdescent : baseEnd_731522 < baseStart_731522 := by decide
  rcases family_descends (prefixWord ++ tailWord_731522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731553 : List Nat := [1, 2, 3, 5, 1, 2, 2, 5]
def baseStart_731553 : Nat := 118140960795 + 731553 * 2 ^ 59
def prefixEnd_731553 : Nat := 4983230072969 + 3 ^ 40 * 731553 * 2
def baseEnd_731553 : Nat := 55650120479804670996023

theorem tailTrace_731553 : CollatzResearch.WordTrace tailWord_731553 prefixEnd_731553 55650120479804670996023 := by
  unfold tailWord_731553
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681929918715895150583313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17787953279143930100388875 26681929918715895150583313)
  ·
    refine ⟨20011447439036921362937485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26681929918715895150583313 20011447439036921362937485)
    ·
      refine ⟨7504292789638845511101557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20011447439036921362937485 7504292789638845511101557)
      ·
        refine ⟨703527449028641766665771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7504292789638845511101557 703527449028641766665771)
        ·
          refine ⟨1055291173542962649998657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703527449028641766665771 1055291173542962649998657)
          ·
            refine ⟨791468380157221987498993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055291173542962649998657 791468380157221987498993)
            ·
              refine ⟨593601285117916490624245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791468380157221987498993 593601285117916490624245)
              ·
                refine ⟨55650120479804670996023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 593601285117916490624245 55650120479804670996023)
                ·
                  rfl

theorem cell21_731553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 5].length) (baseStart_731553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731553 prefixEnd_731553 := by exact prefixLift 731553
  have htrace : WordTrace (prefixWord ++ tailWord_731553) baseStart_731553 baseEnd_731553 := by
    simpa [prefixWord, tailWord_731553, baseEnd_731553] using wordTrace_append hprefix tailTrace_731553
  have hstable : (prefixWord ++ tailWord_731553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731553).length < 2 ^ (prefixWord ++ tailWord_731553).sum := by decide
  have hdescent : baseEnd_731553 < baseStart_731553 := by decide
  rcases family_descends (prefixWord ++ tailWord_731553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731640 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_731640 : Nat := 118140960795 + 731640 * 2 ^ 59
def prefixEnd_731640 : Nat := 4983230072969 + 3 ^ 40 * 731640 * 2
def baseEnd_731640 : Nat := 166970216024721195037891

theorem tailTrace_731640 : CollatzResearch.WordTrace tailWord_731640 prefixEnd_731640 166970216024721195037891 := by
  unfold tailWord_731640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342551534700354504500187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17790068712933806006000249 13342551534700354504500187)
  ·
    refine ⟨20013827302050531756750281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13342551534700354504500187 20013827302050531756750281)
    ·
      refine ⟨15010370476537898817562711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20013827302050531756750281 15010370476537898817562711)
      ·
        refine ⟨22515555714806848226344067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15010370476537898817562711 22515555714806848226344067)
        ·
          refine ⟨33773333572210272339516101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22515555714806848226344067 33773333572210272339516101)
          ·
            refine ⟨6332500044789426063659269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33773333572210272339516101 6332500044789426063659269)
            ·
              refine ⟨1187343758398017386936113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6332500044789426063659269 1187343758398017386936113)
              ·
                refine ⟨890507818798513040202085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187343758398017386936113 890507818798513040202085)
                ·
                  refine ⟨166970216024721195037891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890507818798513040202085 166970216024721195037891)
                  ·
                    rfl

theorem cell21_731640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_731640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731640 prefixEnd_731640 := by exact prefixLift 731640
  have htrace : WordTrace (prefixWord ++ tailWord_731640) baseStart_731640 baseEnd_731640 := by
    simpa [prefixWord, tailWord_731640, baseEnd_731640] using wordTrace_append hprefix tailTrace_731640
  have hstable : (prefixWord ++ tailWord_731640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731640).length < 2 ^ (prefixWord ++ tailWord_731640).sum := by decide
  have hdescent : baseEnd_731640 < baseStart_731640 := by decide
  rcases family_descends (prefixWord ++ tailWord_731640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731699 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_731699 : Nat := 118140960795 + 731699 * 2 ^ 59
def prefixEnd_731699 : Nat := 4983230072969 + 3 ^ 40 * 731699 * 2
def baseEnd_731699 : Nat := 166983680628550203554437

theorem tailTrace_731699 : CollatzResearch.WordTrace tailWord_731699 prefixEnd_731699 166983680628550203554437 := by
  unfold tailWord_731699
  simp only [CollatzResearch.WordTrace]
  refine ⟨26687254976186962085398151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17791503317457974723598767 26687254976186962085398151)
  ·
    refine ⟨40030882464280443128097227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26687254976186962085398151 40030882464280443128097227)
    ·
      refine ⟨60046323696420664692145841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40030882464280443128097227 60046323696420664692145841)
      ·
        refine ⟨45034742772315498519109381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60046323696420664692145841 45034742772315498519109381)
        ·
          refine ⟨8444014269809155972333009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45034742772315498519109381 8444014269809155972333009)
          ·
            refine ⟨6333010702356866979249757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8444014269809155972333009 6333010702356866979249757)
            ·
              refine ⟨2374879013383825117218659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6333010702356866979249757 2374879013383825117218659)
              ·
                refine ⟨3562318520075737675827989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374879013383825117218659 3562318520075737675827989)
                ·
                  refine ⟨166983680628550203554437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3562318520075737675827989 166983680628550203554437)
                  ·
                    rfl

theorem cell21_731699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_731699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731699 prefixEnd_731699 := by exact prefixLift 731699
  have htrace : WordTrace (prefixWord ++ tailWord_731699) baseStart_731699 baseEnd_731699 := by
    simpa [prefixWord, tailWord_731699, baseEnd_731699] using wordTrace_append hprefix tailTrace_731699
  have hstable : (prefixWord ++ tailWord_731699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731699).length < 2 ^ (prefixWord ++ tailWord_731699).sum := by decide
  have hdescent : baseEnd_731699 < baseStart_731699 := by decide
  rcases family_descends (prefixWord ++ tailWord_731699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731702 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_731702 : Nat := 118140960795 + 731702 * 2 ^ 59
def prefixEnd_731702 : Nat := 4983230072969 + 3 ^ 40 * 731702 * 2
def baseEnd_731702 : Nat := 166984365269422865004431

theorem tailTrace_731702 : CollatzResearch.WordTrace tailWord_731702 prefixEnd_731702 166984365269422865004431 := by
  unfold tailWord_731702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667960274698505849859835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17791576263450729065171573 1667960274698505849859835)
  ·
    refine ⟨2501940412047758774789753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1667960274698505849859835 2501940412047758774789753)
    ·
      refine ⟨1876455309035819081092315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2501940412047758774789753 1876455309035819081092315)
      ·
        refine ⟨2814682963553728621638473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876455309035819081092315 2814682963553728621638473)
        ·
          refine ⟨2111012222665296466228855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2814682963553728621638473 2111012222665296466228855)
          ·
            refine ⟨3166518333997944699343283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111012222665296466228855 3166518333997944699343283)
            ·
              refine ⟨4749777500996917049014925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166518333997944699343283 4749777500996917049014925)
              ·
                refine ⟨1781166562873843893380597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4749777500996917049014925 1781166562873843893380597)
                ·
                  refine ⟨166984365269422865004431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1781166562873843893380597 166984365269422865004431)
                  ·
                    rfl

theorem cell21_731702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_731702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731702 prefixEnd_731702 := by exact prefixLift 731702
  have htrace : WordTrace (prefixWord ++ tailWord_731702) baseStart_731702 baseEnd_731702 := by
    simpa [prefixWord, tailWord_731702, baseEnd_731702] using wordTrace_append hprefix tailTrace_731702
  have hstable : (prefixWord ++ tailWord_731702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731702).length < 2 ^ (prefixWord ++ tailWord_731702).sum := by decide
  have hdescent : baseEnd_731702 < baseStart_731702 := by decide
  rcases family_descends (prefixWord ++ tailWord_731702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731730 : List Nat := [3, 2, 2, 1, 2, 1, 3, 7]
def baseStart_731730 : Nat := 118140960795 + 731730 * 2 ^ 59
def prefixEnd_731730 : Nat := 4983230072969 + 3 ^ 40 * 731730 * 2
def baseEnd_731730 : Nat := 55663585083633679512569

theorem tailTrace_731730 : CollatzResearch.WordTrace tailWord_731730 prefixEnd_731730 55663585083633679512569 := by
  unfold tailWord_731730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6672096409768663594944161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17792257092716436253184429 6672096409768663594944161)
  ·
    refine ⟨5004072307326497696208121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6672096409768663594944161 5004072307326497696208121)
    ·
      refine ⟨3753054230494873272156091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5004072307326497696208121 3753054230494873272156091)
      ·
        refine ⟨5629581345742309908234137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753054230494873272156091 5629581345742309908234137)
        ·
          refine ⟨4222186009306732431175603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5629581345742309908234137 4222186009306732431175603)
          ·
            refine ⟨6333279013960098646763405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222186009306732431175603 6333279013960098646763405)
            ·
              refine ⟨2374979630235036992536277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6333279013960098646763405 2374979630235036992536277)
              ·
                refine ⟨55663585083633679512569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2374979630235036992536277 55663585083633679512569)
                ·
                  rfl

theorem cell21_731730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_731730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731730 prefixEnd_731730 := by exact prefixLift 731730
  have htrace : WordTrace (prefixWord ++ tailWord_731730) baseStart_731730 baseEnd_731730 := by
    simpa [prefixWord, tailWord_731730, baseEnd_731730] using wordTrace_append hprefix tailTrace_731730
  have hstable : (prefixWord ++ tailWord_731730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731730).length < 2 ^ (prefixWord ++ tailWord_731730).sum := by decide
  have hdescent : baseEnd_731730 < baseStart_731730 := by decide
  rcases family_descends (prefixWord ++ tailWord_731730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731744 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_731744 : Nat := 118140960795 + 731744 * 2 ^ 59
def prefixEnd_731744 : Nat := 4983230072969 + 3 ^ 40 * 731744 * 2
def baseEnd_731744 : Nat := 166993950241640125304345

theorem tailTrace_731744 : CollatzResearch.WordTrace tailWord_731744 prefixEnd_731744 166993950241640125304345 := by
  unfold tailWord_731744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344448130511967385393143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17792597507349289847190857 13344448130511967385393143)
  ·
    refine ⟨20016672195767951078089715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13344448130511967385393143 20016672195767951078089715)
    ·
      refine ⟨30025008293651926617134573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20016672195767951078089715 30025008293651926617134573)
      ·
        refine ⟨11259378110119472481425465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30025008293651926617134573 11259378110119472481425465)
        ·
          refine ⟨8444533582589604361069099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11259378110119472481425465 8444533582589604361069099)
          ·
            refine ⟨12666800373884406541603649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8444533582589604361069099 12666800373884406541603649)
            ·
              refine ⟨9500100280413304906202737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12666800373884406541603649 9500100280413304906202737)
              ·
                refine ⟨7125075210309978679652053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9500100280413304906202737 7125075210309978679652053)
                ·
                  refine ⟨166993950241640125304345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7125075210309978679652053 166993950241640125304345)
                  ·
                    rfl

theorem cell21_731744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_731744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731744 prefixEnd_731744 := by exact prefixLift 731744
  have htrace : WordTrace (prefixWord ++ tailWord_731744) baseStart_731744 baseEnd_731744 := by
    simpa [prefixWord, tailWord_731744, baseEnd_731744] using wordTrace_append hprefix tailTrace_731744
  have hstable : (prefixWord ++ tailWord_731744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731744).length < 2 ^ (prefixWord ++ tailWord_731744).sum := by decide
  have hdescent : baseEnd_731744 < baseStart_731744 := by decide
  rcases family_descends (prefixWord ++ tailWord_731744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731809 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_731809 : Nat := 118140960795 + 731809 * 2 ^ 59
def prefixEnd_731809 : Nat := 4983230072969 + 3 ^ 40 * 731809 * 2
def baseEnd_731809 : Nat := 167008784127214456720879

theorem tailTrace_731809 : CollatzResearch.WordTrace tailWord_731809 prefixEnd_731809 167008784127214456720879 := by
  unfold tailWord_731809
  simp only [CollatzResearch.WordTrace]
  refine ⟨26691267005788450871902481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17794178003858967247934987 26691267005788450871902481)
  ·
    refine ⟨20018450254341338153926861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26691267005788450871902481 20018450254341338153926861)
    ·
      refine ⟨7506918845378001807722573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20018450254341338153926861 7506918845378001807722573)
      ·
        refine ⟨2815094567016750677895965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7506918845378001807722573 2815094567016750677895965)
        ·
          refine ⟨1055660462631281504210987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2815094567016750677895965 1055660462631281504210987)
          ·
            refine ⟨1583490693946922256316481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055660462631281504210987 1583490693946922256316481)
            ·
              refine ⟨1187618020460191692237361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583490693946922256316481 1187618020460191692237361)
              ·
                refine ⟨890713515345143769178021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187618020460191692237361 890713515345143769178021)
                ·
                  refine ⟨167008784127214456720879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890713515345143769178021 167008784127214456720879)
                  ·
                    rfl

theorem cell21_731809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_731809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731809 prefixEnd_731809 := by exact prefixLift 731809
  have htrace : WordTrace (prefixWord ++ tailWord_731809) baseStart_731809 baseEnd_731809 := by
    simpa [prefixWord, tailWord_731809, baseEnd_731809] using wordTrace_append hprefix tailTrace_731809
  have hstable : (prefixWord ++ tailWord_731809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731809).length < 2 ^ (prefixWord ++ tailWord_731809).sum := by decide
  have hdescent : baseEnd_731809 < baseStart_731809 := by decide
  rcases family_descends (prefixWord ++ tailWord_731809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731837 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_731837 : Nat := 118140960795 + 731837 * 2 ^ 59
def prefixEnd_731837 : Nat := 4983230072969 + 3 ^ 40 * 731837 * 2
def baseEnd_731837 : Nat := 167015174108692630254155

theorem tailTrace_731837 : CollatzResearch.WordTrace tailWord_731837 prefixEnd_731837 167015174108692630254155 := by
  unfold tailWord_731837
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692288249687011653921765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17794858833124674435947843 26692288249687011653921765)
  ·
    refine ⟨5004804046816314685110331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26692288249687011653921765 5004804046816314685110331)
    ·
      refine ⟨7507206070224472027665497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5004804046816314685110331 7507206070224472027665497)
      ·
        refine ⟨5630404552668354020749123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7507206070224472027665497 5630404552668354020749123)
        ·
          refine ⟨8445606829002531031123685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5630404552668354020749123 8445606829002531031123685)
          ·
            refine ⟨1583551280437974568335691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8445606829002531031123685 1583551280437974568335691)
            ·
              refine ⟨2375326920656961852503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583551280437974568335691 2375326920656961852503537)
              ·
                refine ⟨1781495190492721389377653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375326920656961852503537 1781495190492721389377653)
                ·
                  refine ⟨167015174108692630254155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1781495190492721389377653 167015174108692630254155)
                  ·
                    rfl

theorem cell21_731837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_731837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731837 prefixEnd_731837 := by exact prefixLift 731837
  have htrace : WordTrace (prefixWord ++ tailWord_731837) baseStart_731837 baseEnd_731837 := by
    simpa [prefixWord, tailWord_731837, baseEnd_731837] using wordTrace_append hprefix tailTrace_731837
  have hstable : (prefixWord ++ tailWord_731837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731837).length < 2 ^ (prefixWord ++ tailWord_731837).sum := by decide
  have hdescent : baseEnd_731837 < baseStart_731837 := by decide
  rcases family_descends (prefixWord ++ tailWord_731837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731854 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_731854 : Nat := 118140960795 + 731854 * 2 ^ 59
def prefixEnd_731854 : Nat := 4983230072969 + 3 ^ 40 * 731854 * 2
def baseEnd_731854 : Nat := 167019053740304378470787

theorem tailTrace_731854 : CollatzResearch.WordTrace tailWord_731854 prefixEnd_731854 167019053740304378470787 := by
  unfold tailWord_731854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336613536328177944661327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17795272193750282371527077 3336613536328177944661327)
  ·
    refine ⟨5004920304492266916991991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3336613536328177944661327 5004920304492266916991991)
    ·
      refine ⟨7507380456738400375487987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5004920304492266916991991 7507380456738400375487987)
      ·
        refine ⟨11261070685107600563231981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7507380456738400375487987 11261070685107600563231981)
        ·
          refine ⟨4222901506915350211211993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11261070685107600563231981 4222901506915350211211993)
          ·
            refine ⟨3167176130186512658408995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4222901506915350211211993 3167176130186512658408995)
            ·
              refine ⟨4750764195279768987613493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167176130186512658408995 4750764195279768987613493)
              ·
                refine ⟨445384143307478342588765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4750764195279768987613493 445384143307478342588765)
                ·
                  refine ⟨167019053740304378470787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445384143307478342588765 167019053740304378470787)
                  ·
                    rfl

theorem cell21_731854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_731854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731854 prefixEnd_731854 := by exact prefixLift 731854
  have htrace : WordTrace (prefixWord ++ tailWord_731854) baseStart_731854 baseEnd_731854 := by
    simpa [prefixWord, tailWord_731854, baseEnd_731854] using wordTrace_append hprefix tailTrace_731854
  have hstable : (prefixWord ++ tailWord_731854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731854).length < 2 ^ (prefixWord ++ tailWord_731854).sum := by decide
  have hdescent : baseEnd_731854 < baseStart_731854 := by decide
  rcases family_descends (prefixWord ++ tailWord_731854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731865 : List Nat := [1, 2, 1, 2, 3, 2, 10]
def baseStart_731865 : Nat := 118140960795 + 731865 * 2 ^ 59
def prefixEnd_731865 : Nat := 4983230072969 + 3 ^ 40 * 731865 * 2
def baseEnd_731865 : Nat := 18557951565574533754159

theorem tailTrace_731865 : CollatzResearch.WordTrace tailWord_731865 prefixEnd_731865 18557951565574533754159 := by
  unfold tailWord_731865
  simp only [CollatzResearch.WordTrace]
  refine ⟨26693309493585572435941049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17795539662390381623960699 26693309493585572435941049)
  ·
    refine ⟨20019982120189179326955787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26693309493585572435941049 20019982120189179326955787)
    ·
      refine ⟨30029973180283768990433681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20019982120189179326955787 30029973180283768990433681)
      ·
        refine ⟨22522479885212826742825261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30029973180283768990433681 22522479885212826742825261)
        ·
          refine ⟨8445929956954810028559473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22522479885212826742825261 8445929956954810028559473)
          ·
            refine ⟨6334447467716107521419605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8445929956954810028559473 6334447467716107521419605)
            ·
              refine ⟨18557951565574533754159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6334447467716107521419605 18557951565574533754159)
              ·
                rfl

theorem cell21_731865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 10].length) (baseStart_731865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731865 prefixEnd_731865 := by exact prefixLift 731865
  have htrace : WordTrace (prefixWord ++ tailWord_731865) baseStart_731865 baseEnd_731865 := by
    simpa [prefixWord, tailWord_731865, baseEnd_731865] using wordTrace_append hprefix tailTrace_731865
  have hstable : (prefixWord ++ tailWord_731865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731865).length < 2 ^ (prefixWord ++ tailWord_731865).sum := by decide
  have hdescent : baseEnd_731865 < baseStart_731865 := by decide
  rcases family_descends (prefixWord ++ tailWord_731865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731885 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 4]
def baseStart_731885 : Nat := 118140960795 + 731885 * 2 ^ 59
def prefixEnd_731885 : Nat := 4983230072969 + 3 ^ 40 * 731885 * 2
def baseEnd_731885 : Nat := 167026128362655213454057

theorem tailTrace_731885 : CollatzResearch.WordTrace tailWord_731885 prefixEnd_731885 167026128362655213454057 := by
  unfold tailWord_731885
  simp only [CollatzResearch.WordTrace]
  refine ⟨26694038953513115851669109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17796025969008743901112739 26694038953513115851669109)
  ·
    refine ⟨2502566151891854611093979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26694038953513115851669109 2502566151891854611093979)
    ·
      refine ⟨3753849227837781916640969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502566151891854611093979 3753849227837781916640969)
      ·
        refine ⟨2815386920878336437480727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753849227837781916640969 2815386920878336437480727)
        ·
          refine ⟨4223080381317504656221091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815386920878336437480727 4223080381317504656221091)
          ·
            refine ⟨6334620571976256984331637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223080381317504656221091 6334620571976256984331637)
            ·
              refine ⟨593870678622774092281091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6334620571976256984331637 593870678622774092281091)
              ·
                refine ⟨890806017934161138421637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593870678622774092281091 890806017934161138421637)
                ·
                  refine ⟨167026128362655213454057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890806017934161138421637 167026128362655213454057)
                  ·
                    rfl

theorem cell21_731885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_731885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731885 prefixEnd_731885 := by exact prefixLift 731885
  have htrace : WordTrace (prefixWord ++ tailWord_731885) baseStart_731885 baseEnd_731885 := by
    simpa [prefixWord, tailWord_731885, baseEnd_731885] using wordTrace_append hprefix tailTrace_731885
  have hstable : (prefixWord ++ tailWord_731885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731885).length < 2 ^ (prefixWord ++ tailWord_731885).sum := by decide
  have hdescent : baseEnd_731885 < baseStart_731885 := by decide
  rcases family_descends (prefixWord ++ tailWord_731885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731896 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_731896 : Nat := 118140960795 + 731896 * 2 ^ 59
def prefixEnd_731896 : Nat := 4983230072969 + 3 ^ 40 * 731896 * 2
def baseEnd_731896 : Nat := 167028638712521638770701

theorem tailTrace_731896 : CollatzResearch.WordTrace tailWord_731896 prefixEnd_731896 167028638712521638770701 := by
  unfold tailWord_731896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347220078236632365159771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17796293437648843153546361 13347220078236632365159771)
  ·
    refine ⟨20020830117354948547739657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13347220078236632365159771 20020830117354948547739657)
    ·
      refine ⟨15015622588016211410804743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20020830117354948547739657 15015622588016211410804743)
      ·
        refine ⟨22523433882024317116207115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015622588016211410804743 22523433882024317116207115)
        ·
          refine ⟨33785150823036475674310673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22523433882024317116207115 33785150823036475674310673)
          ·
            refine ⟨25338863117277356755733005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33785150823036475674310673 25338863117277356755733005)
            ·
              refine ⟨9502073668979008783399877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25338863117277356755733005 9502073668979008783399877)
              ·
                refine ⟨1781638812933564146887477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9502073668979008783399877 1781638812933564146887477)
                ·
                  refine ⟨167028638712521638770701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1781638812933564146887477 167028638712521638770701)
                  ·
                    rfl

theorem cell21_731896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_731896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731896 prefixEnd_731896 := by exact prefixLift 731896
  have htrace : WordTrace (prefixWord ++ tailWord_731896) baseStart_731896 baseEnd_731896 := by
    simpa [prefixWord, tailWord_731896, baseEnd_731896] using wordTrace_append hprefix tailTrace_731896
  have hstable : (prefixWord ++ tailWord_731896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731896).length < 2 ^ (prefixWord ++ tailWord_731896).sum := by decide
  have hdescent : baseEnd_731896 < baseStart_731896 := by decide
  rcases family_descends (prefixWord ++ tailWord_731896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731944 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_731944 : Nat := 118140960795 + 731944 * 2 ^ 59
def prefixEnd_731944 : Nat := 4983230072969 + 3 ^ 40 * 731944 * 2
def baseEnd_731944 : Nat := 167039592966484221970603

theorem tailTrace_731944 : CollatzResearch.WordTrace tailWord_731944 prefixEnd_731944 167039592966484221970603 := by
  unfold tailWord_731944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348095430149684464033443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17797460573532912618711257 13348095430149684464033443)
  ·
    refine ⟨20022143145224526696050165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13348095430149684464033443 20022143145224526696050165)
    ·
      refine ⟨1877075919864799377754703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20022143145224526696050165 1877075919864799377754703)
      ·
        refine ⟨2815613879797199066632055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877075919864799377754703 2815613879797199066632055)
        ·
          refine ⟨4223420819695798599948083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815613879797199066632055 4223420819695798599948083)
          ·
            refine ⟨6335131229543697899922125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223420819695798599948083 6335131229543697899922125)
            ·
              refine ⟨2375674211078886712470797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6335131229543697899922125 2375674211078886712470797)
              ·
                refine ⟨890877829154582517176549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2375674211078886712470797 890877829154582517176549)
                ·
                  refine ⟨167039592966484221970603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890877829154582517176549 167039592966484221970603)
                  ·
                    rfl

theorem cell21_731944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_731944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731944 prefixEnd_731944 := by exact prefixLift 731944
  have htrace : WordTrace (prefixWord ++ tailWord_731944) baseStart_731944 baseEnd_731944 := by
    simpa [prefixWord, tailWord_731944, baseEnd_731944] using wordTrace_append hprefix tailTrace_731944
  have hstable : (prefixWord ++ tailWord_731944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731944).length < 2 ^ (prefixWord ++ tailWord_731944).sum := by decide
  have hdescent : baseEnd_731944 < baseStart_731944 := by decide
  rcases family_descends (prefixWord ++ tailWord_731944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731981 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 3]
def baseStart_731981 : Nat := 118140960795 + 731981 * 2 ^ 59
def prefixEnd_731981 : Nat := 4983230072969 + 3 ^ 40 * 731981 * 2
def baseEnd_731981 : Nat := 167048036870580379853861

theorem tailTrace_731981 : CollatzResearch.WordTrace tailWord_731981 prefixEnd_731981 167048036870580379853861 := by
  unfold tailWord_731981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26697540361165324247163797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17798360240776882831442531 26697540361165324247163797)
  ·
    refine ⟨1251447204429624574085803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26697540361165324247163797 1251447204429624574085803)
    ·
      refine ⟨1877170806644436861128705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251447204429624574085803 1877170806644436861128705)
      ·
        refine ⟨1407878104983327645846529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1877170806644436861128705 1407878104983327645846529)
        ·
          refine ⟨1055908578737495734384897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1407878104983327645846529 1055908578737495734384897)
          ·
            refine ⟨791931434053121800788673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055908578737495734384897 791931434053121800788673)
            ·
              refine ⟨593948575539841350591505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791931434053121800788673 593948575539841350591505)
              ·
                refine ⟨445461431654881012943629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593948575539841350591505 445461431654881012943629)
                ·
                  refine ⟨167048036870580379853861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445461431654881012943629 167048036870580379853861)
                  ·
                    rfl

theorem cell21_731981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_731981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_731981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_731981 prefixEnd_731981 := by exact prefixLift 731981
  have htrace : WordTrace (prefixWord ++ tailWord_731981) baseStart_731981 baseEnd_731981 := by
    simpa [prefixWord, tailWord_731981, baseEnd_731981] using wordTrace_append hprefix tailTrace_731981
  have hstable : (prefixWord ++ tailWord_731981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731981).length < 2 ^ (prefixWord ++ tailWord_731981).sum := by decide
  have hdescent : baseEnd_731981 < baseStart_731981 := by decide
  rcases family_descends (prefixWord ++ tailWord_731981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732065 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_732065 : Nat := 118140960795 + 732065 * 2 ^ 59
def prefixEnd_732065 : Nat := 4983230072969 + 3 ^ 40 * 732065 * 2
def baseEnd_732065 : Nat := 167067206815014900453689

theorem tailTrace_732065 : CollatzResearch.WordTrace tailWord_732065 prefixEnd_732065 167067206815014900453689 := by
  unfold tailWord_732065
  simp only [CollatzResearch.WordTrace]
  refine ⟨26700604092861006593221649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17800402728574004395481099 26700604092861006593221649)
  ·
    refine ⟨20025453069645754944916237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26700604092861006593221649 20025453069645754944916237)
    ·
      refine ⟨7509544901117158104343589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20025453069645754944916237 7509544901117158104343589)
      ·
        refine ⟨1408039668959467144564423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7509544901117158104343589 1408039668959467144564423)
        ·
          refine ⟨2112059503439200716846635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408039668959467144564423 2112059503439200716846635)
          ·
            refine ⟨3168089255158801075269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112059503439200716846635 3168089255158801075269953)
            ·
              refine ⟨2376066941369100806452465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168089255158801075269953 2376066941369100806452465)
              ·
                refine ⟨1782050206026825604839349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376066941369100806452465 1782050206026825604839349)
                ·
                  refine ⟨167067206815014900453689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782050206026825604839349 167067206815014900453689)
                  ·
                    rfl

theorem cell21_732065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_732065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732065 prefixEnd_732065 := by exact prefixLift 732065
  have htrace : WordTrace (prefixWord ++ tailWord_732065) baseStart_732065 baseEnd_732065 := by
    simpa [prefixWord, tailWord_732065, baseEnd_732065] using wordTrace_append hprefix tailTrace_732065
  have hstable : (prefixWord ++ tailWord_732065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732065).length < 2 ^ (prefixWord ++ tailWord_732065).sum := by decide
  have hdescent : baseEnd_732065 < baseStart_732065 := by decide
  rcases family_descends (prefixWord ++ tailWord_732065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732102 : List Nat := [6, 1, 3, 1, 1, 1, 2, 6]
def baseStart_732102 : Nat := 118140960795 + 732102 * 2 ^ 59
def prefixEnd_732102 : Nat := 4983230072969 + 3 ^ 40 * 732102 * 2
def baseEnd_732102 : Nat := 55691883573037019445649

theorem tailTrace_732102 : CollatzResearch.WordTrace tailWord_732102 prefixEnd_732102 55691883573037019445649 := by
  unfold tailWord_732102
  simp only [CollatzResearch.WordTrace]
  refine ⟨834436049803967559759955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17801302395817974608212373 834436049803967559759955)
  ·
    refine ⟨1251654074705951339639933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834436049803967559759955 1251654074705951339639933)
    ·
      refine ⟨469370278014731752364975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1251654074705951339639933 469370278014731752364975)
      ·
        refine ⟨704055417022097628547463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469370278014731752364975 704055417022097628547463)
        ·
          refine ⟨1056083125533146442821195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704055417022097628547463 1056083125533146442821195)
          ·
            refine ⟨1584124688299719664231793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056083125533146442821195 1584124688299719664231793)
            ·
              refine ⟨1188093516224789748173845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584124688299719664231793 1188093516224789748173845)
              ·
                refine ⟨55691883573037019445649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1188093516224789748173845 55691883573037019445649)
                ·
                  rfl

theorem cell21_732102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_732102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732102 prefixEnd_732102 := by exact prefixLift 732102
  have htrace : WordTrace (prefixWord ++ tailWord_732102) baseStart_732102 baseEnd_732102 := by
    simpa [prefixWord, tailWord_732102, baseEnd_732102] using wordTrace_append hprefix tailTrace_732102
  have hstable : (prefixWord ++ tailWord_732102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732102).length < 2 ^ (prefixWord ++ tailWord_732102).sum := by decide
  have hdescent : baseEnd_732102 < baseStart_732102 := by decide
  rcases family_descends (prefixWord ++ tailWord_732102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732110 : List Nat := [4, 1, 1, 1, 2, 4, 2, 6]
def baseStart_732110 : Nat := 118140960795 + 732110 * 2 ^ 59
def prefixEnd_732110 : Nat := 4983230072969 + 3 ^ 40 * 732110 * 2
def baseEnd_732110 : Nat := 55692492142701607401199

theorem tailTrace_732110 : CollatzResearch.WordTrace tailWord_732110 prefixEnd_732110 55692492142701607401199 := by
  unfold tailWord_732110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337780672212247409826223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17801496918465319519073189 3337780672212247409826223)
  ·
    refine ⟨5006671008318371114739335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3337780672212247409826223 5006671008318371114739335)
    ·
      refine ⟨7510006512477556672109003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5006671008318371114739335 7510006512477556672109003)
      ·
        refine ⟨11265009768716335008163505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510006512477556672109003 11265009768716335008163505)
        ·
          refine ⟨8448757326537251256122629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11265009768716335008163505 8448757326537251256122629)
          ·
            refine ⟨1584141998725734610522993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8448757326537251256122629 1584141998725734610522993)
            ·
              refine ⟨1188106499044300957892245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584141998725734610522993 1188106499044300957892245)
              ·
                refine ⟨55692492142701607401199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1188106499044300957892245 55692492142701607401199)
                ·
                  rfl

theorem cell21_732110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_732110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732110 prefixEnd_732110 := by exact prefixLift 732110
  have htrace : WordTrace (prefixWord ++ tailWord_732110) baseStart_732110 baseEnd_732110 := by
    simpa [prefixWord, tailWord_732110, baseEnd_732110] using wordTrace_append hprefix tailTrace_732110
  have hstable : (prefixWord ++ tailWord_732110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732110).length < 2 ^ (prefixWord ++ tailWord_732110).sum := by decide
  have hdescent : baseEnd_732110 < baseStart_732110 := by decide
  rcases family_descends (prefixWord ++ tailWord_732110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732186 : List Nat := [3, 1, 1, 3, 1, 2, 5, 5]
def baseStart_732186 : Nat := 118140960795 + 732186 * 2 ^ 59
def prefixEnd_732186 : Nat := 4983230072969 + 3 ^ 40 * 732186 * 2
def baseEnd_732186 : Nat := 55698273554515192978925

theorem tailTrace_732186 : CollatzResearch.WordTrace tailWord_732186 prefixEnd_732186 55698273554515192978925 := by
  unfold tailWord_732186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676254331355661064594103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17803344883615096172250941 6676254331355661064594103)
  ·
    refine ⟨10014381497033491596891155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6676254331355661064594103 10014381497033491596891155)
    ·
      refine ⟨15021572245550237395336733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10014381497033491596891155 15021572245550237395336733)
      ·
        refine ⟨5633089592081339023251275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15021572245550237395336733 5633089592081339023251275)
        ·
          refine ⟨8449634388122008534876913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633089592081339023251275 8449634388122008534876913)
          ·
            refine ⟨6337225791091506401157685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8449634388122008534876913 6337225791091506401157685)
            ·
              refine ⟨594114917914828725108533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6337225791091506401157685 594114917914828725108533)
              ·
                refine ⟨55698273554515192978925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 594114917914828725108533 55698273554515192978925)
                ·
                  rfl

theorem cell21_732186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_732186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732186 prefixEnd_732186 := by exact prefixLift 732186
  have htrace : WordTrace (prefixWord ++ tailWord_732186) baseStart_732186 baseEnd_732186 := by
    simpa [prefixWord, tailWord_732186, baseEnd_732186] using wordTrace_append hprefix tailTrace_732186
  have hstable : (prefixWord ++ tailWord_732186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732186).length < 2 ^ (prefixWord ++ tailWord_732186).sum := by decide
  have hdescent : baseEnd_732186 < baseStart_732186 := by decide
  rcases family_descends (prefixWord ++ tailWord_732186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732217 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_732217 : Nat := 118140960795 + 732217 * 2 ^ 59
def prefixEnd_732217 : Nat := 4983230072969 + 3 ^ 40 * 732217 * 2
def baseEnd_732217 : Nat := 167101895285896413920045

theorem tailTrace_732217 : CollatzResearch.WordTrace tailWord_732217 prefixEnd_732217 167101895285896413920045 := by
  unfold tailWord_732217
  simp only [CollatzResearch.WordTrace]
  refine ⟨26706147988310336552754905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17804098658873557701836603 26706147988310336552754905)
  ·
    refine ⟨20029610991232752414566179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26706147988310336552754905 20029610991232752414566179)
    ·
      refine ⟨30044416486849128621849269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20029610991232752414566179 30044416486849128621849269)
      ·
        refine ⟨2816664045642105808298369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30044416486849128621849269 2816664045642105808298369)
        ·
          refine ⟨2112498034231579356223777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816664045642105808298369 2112498034231579356223777)
          ·
            refine ⟨1584373525673684517167833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112498034231579356223777 1584373525673684517167833)
            ·
              refine ⟨1188280144255263387875875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584373525673684517167833 1188280144255263387875875)
              ·
                refine ⟨1782420216382895081813813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188280144255263387875875 1782420216382895081813813)
                ·
                  refine ⟨167101895285896413920045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782420216382895081813813 167101895285896413920045)
                  ·
                    rfl

theorem cell21_732217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_732217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732217 prefixEnd_732217 := by exact prefixLift 732217
  have htrace : WordTrace (prefixWord ++ tailWord_732217) baseStart_732217 baseEnd_732217 := by
    simpa [prefixWord, tailWord_732217, baseEnd_732217] using wordTrace_append hprefix tailTrace_732217
  have hstable : (prefixWord ++ tailWord_732217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732217).length < 2 ^ (prefixWord ++ tailWord_732217).sum := by decide
  have hdescent : baseEnd_732217 < baseStart_732217 := by decide
  rcases family_descends (prefixWord ++ tailWord_732217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732245 : List Nat := [1, 3, 2, 2, 1, 2, 3, 7]
def baseStart_732245 : Nat := 118140960795 + 732245 * 2 ^ 59
def prefixEnd_732245 : Nat := 4983230072969 + 3 ^ 40 * 732245 * 2
def baseEnd_732245 : Nat := 55702761755791529151107

theorem tailTrace_732245 : CollatzResearch.WordTrace tailWord_732245 prefixEnd_732245 55702761755791529151107 := by
  unfold tailWord_732245
  simp only [CollatzResearch.WordTrace]
  refine ⟨26707169232208897334774189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17804779488139264889849459 26707169232208897334774189)
  ·
    refine ⟨10015188462078336500540321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26707169232208897334774189 10015188462078336500540321)
    ·
      refine ⟨7511391346558752375405241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10015188462078336500540321 7511391346558752375405241)
      ·
        refine ⟨5633543509919064281553931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7511391346558752375405241 5633543509919064281553931)
        ·
          refine ⟨8450315264878596422330897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633543509919064281553931 8450315264878596422330897)
          ·
            refine ⟨6337736448658947316748173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8450315264878596422330897 6337736448658947316748173)
            ·
              refine ⟨2376651168247105243780565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6337736448658947316748173 2376651168247105243780565)
              ·
                refine ⟨55702761755791529151107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2376651168247105243780565 55702761755791529151107)
                ·
                  rfl

theorem cell21_732245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_732245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732245 prefixEnd_732245 := by exact prefixLift 732245
  have htrace : WordTrace (prefixWord ++ tailWord_732245) baseStart_732245 baseEnd_732245 := by
    simpa [prefixWord, tailWord_732245, baseEnd_732245] using wordTrace_append hprefix tailTrace_732245
  have hstable : (prefixWord ++ tailWord_732245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732245).length < 2 ^ (prefixWord ++ tailWord_732245).sum := by decide
  have hdescent : baseEnd_732245 < baseStart_732245 := by decide
  rcases family_descends (prefixWord ++ tailWord_732245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732324 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_732324 : Nat := 118140960795 + 732324 * 2 ^ 59
def prefixEnd_732324 : Nat := 4983230072969 + 3 ^ 40 * 732324 * 2
def baseEnd_732324 : Nat := 167126314143688005636493

theorem tailTrace_732324 : CollatzResearch.WordTrace tailWord_732324 prefixEnd_732324 167126314143688005636493 := by
  unfold tailWord_732324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13355025299461346913450013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17806700399281795884600017 13355025299461346913450013)
  ·
    refine ⟨5008134487298005092543755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13355025299461346913450013 5008134487298005092543755)
    ·
      refine ⟨7512201730947007638815633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008134487298005092543755 7512201730947007638815633)
      ·
        refine ⟨5634151298210255729111725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7512201730947007638815633 5634151298210255729111725)
        ·
          refine ⟨2112806736828845898416897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5634151298210255729111725 2112806736828845898416897)
          ·
            refine ⟨1584605052621634423812673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112806736828845898416897 1584605052621634423812673)
            ·
              refine ⟨1188453789466225817859505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584605052621634423812673 1188453789466225817859505)
              ·
                refine ⟨891340342099669363394629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188453789466225817859505 891340342099669363394629)
                ·
                  refine ⟨167126314143688005636493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891340342099669363394629 167126314143688005636493)
                  ·
                    rfl

theorem cell21_732324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_732324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732324 prefixEnd_732324 := by exact prefixLift 732324
  have htrace : WordTrace (prefixWord ++ tailWord_732324) baseStart_732324 baseEnd_732324 := by
    simpa [prefixWord, tailWord_732324, baseEnd_732324] using wordTrace_append hprefix tailTrace_732324
  have hstable : (prefixWord ++ tailWord_732324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732324).length < 2 ^ (prefixWord ++ tailWord_732324).sum := by decide
  have hdescent : baseEnd_732324 < baseStart_732324 := by decide
  rcases family_descends (prefixWord ++ tailWord_732324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732327 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 3]
def baseStart_732327 : Nat := 118140960795 + 732327 * 2 ^ 59
def prefixEnd_732327 : Nat := 4983230072969 + 3 ^ 40 * 732327 * 2
def baseEnd_732327 : Nat := 167126998784560667086487

theorem tailTrace_732327 : CollatzResearch.WordTrace tailWord_732327 prefixEnd_732327 167126998784560667086487 := by
  unfold tailWord_732327
  simp only [CollatzResearch.WordTrace]
  refine ⟨26710160017911825339259235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17806773345274550226172823 26710160017911825339259235)
  ·
    refine ⟨40065240026867738008888853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26710160017911825339259235 40065240026867738008888853)
    ·
      refine ⟨1878058126259425219166665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40065240026867738008888853 1878058126259425219166665)
      ·
        refine ⟨1408543594694568914374999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878058126259425219166665 1408543594694568914374999)
        ·
          refine ⟨2112815392041853371562499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408543594694568914374999 2112815392041853371562499)
          ·
            refine ⟨3169223088062780057343749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112815392041853371562499 3169223088062780057343749)
            ·
              refine ⟨594229329011771260751953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3169223088062780057343749 594229329011771260751953)
              ·
                refine ⟨445671996758828445563965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594229329011771260751953 445671996758828445563965)
                ·
                  refine ⟨167126998784560667086487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445671996758828445563965 167126998784560667086487)
                  ·
                    rfl

theorem cell21_732327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3].length) (baseStart_732327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732327 prefixEnd_732327 := by exact prefixLift 732327
  have htrace : WordTrace (prefixWord ++ tailWord_732327) baseStart_732327 baseEnd_732327 := by
    simpa [prefixWord, tailWord_732327, baseEnd_732327] using wordTrace_append hprefix tailTrace_732327
  have hstable : (prefixWord ++ tailWord_732327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732327).length < 2 ^ (prefixWord ++ tailWord_732327).sum := by decide
  have hdescent : baseEnd_732327 < baseStart_732327 := by decide
  rcases family_descends (prefixWord ++ tailWord_732327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732338 : List Nat := [3, 2, 1, 1, 1, 6, 1, 6]
def baseStart_732338 : Nat := 118140960795 + 732338 * 2 ^ 59
def prefixEnd_732338 : Nat := 4983230072969 + 3 ^ 40 * 732338 * 2
def baseEnd_732338 : Nat := 55709836378142364134377

theorem tailTrace_732338 : CollatzResearch.WordTrace tailWord_732338 prefixEnd_732338 55709836378142364134377 := by
  unfold tailWord_732338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6677640305217993554477417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17807040813914649478606445 6677640305217993554477417)
  ·
    refine ⟨5008230228913495165858063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6677640305217993554477417 5008230228913495165858063)
    ·
      refine ⟨7512345343370242748787095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008230228913495165858063 7512345343370242748787095)
      ·
        refine ⟨11268518015055364123180643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7512345343370242748787095 11268518015055364123180643)
        ·
          refine ⟨16902777022583046184770965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268518015055364123180643 16902777022583046184770965)
          ·
            refine ⟨792317672933580289911139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16902777022583046184770965 792317672933580289911139)
            ·
              refine ⟨1188476509400370434866709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792317672933580289911139 1188476509400370434866709)
              ·
                refine ⟨55709836378142364134377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1188476509400370434866709 55709836378142364134377)
                ·
                  rfl

theorem cell21_732338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_732338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732338 prefixEnd_732338 := by exact prefixLift 732338
  have htrace : WordTrace (prefixWord ++ tailWord_732338) baseStart_732338 baseEnd_732338 := by
    simpa [prefixWord, tailWord_732338, baseEnd_732338] using wordTrace_append hprefix tailTrace_732338
  have hstable : (prefixWord ++ tailWord_732338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732338).length < 2 ^ (prefixWord ++ tailWord_732338).sum := by decide
  have hdescent : baseEnd_732338 < baseStart_732338 := by decide
  rcases family_descends (prefixWord ++ tailWord_732338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732383 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_732383 : Nat := 118140960795 + 732383 * 2 ^ 59
def prefixEnd_732383 : Nat := 4983230072969 + 3 ^ 40 * 732383 * 2
def baseEnd_732383 : Nat := 167139778747517014153039

theorem tailTrace_732383 : CollatzResearch.WordTrace tailWord_732383 prefixEnd_732383 167139778747517014153039 := by
  unfold tailWord_732383
  simp only [CollatzResearch.WordTrace]
  refine ⟨26712202505708946903297803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17808135003805964602198535 26712202505708946903297803)
  ·
    refine ⟨40068303758563420354946705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26712202505708946903297803 40068303758563420354946705)
    ·
      refine ⟨30051227818922565266210029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40068303758563420354946705 30051227818922565266210029)
      ·
        refine ⟨11269210432095961974828761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30051227818922565266210029 11269210432095961974828761)
        ·
          refine ⟨8451907824071971481121571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11269210432095961974828761 8451907824071971481121571)
          ·
            refine ⟨12677861736107957221682357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451907824071971481121571 12677861736107957221682357)
            ·
              refine ⟨1188549537760120989532721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12677861736107957221682357 1188549537760120989532721)
              ·
                refine ⟨891412153320090742149541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188549537760120989532721 891412153320090742149541)
                ·
                  refine ⟨167139778747517014153039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891412153320090742149541 167139778747517014153039)
                  ·
                    rfl

theorem cell21_732383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_732383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732383 prefixEnd_732383 := by exact prefixLift 732383
  have htrace : WordTrace (prefixWord ++ tailWord_732383) baseStart_732383 baseEnd_732383 := by
    simpa [prefixWord, tailWord_732383, baseEnd_732383] using wordTrace_append hprefix tailTrace_732383
  have hstable : (prefixWord ++ tailWord_732383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732383).length < 2 ^ (prefixWord ++ tailWord_732383).sum := by decide
  have hdescent : baseEnd_732383 < baseStart_732383 := by decide
  rcases family_descends (prefixWord ++ tailWord_732383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732414 : List Nat := [4, 2, 2, 1, 1, 3, 1, 7]
def baseStart_732414 : Nat := 118140960795 + 732414 * 2 ^ 59
def prefixEnd_732414 : Nat := 4983230072969 + 3 ^ 40 * 732414 * 2
def baseEnd_732414 : Nat := 55715617789955949712103

theorem tailTrace_732414 : CollatzResearch.WordTrace tailWord_732414 prefixEnd_732414 55715617789955949712103 := by
  unfold tailWord_732414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339166646074579899709537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17808888779064426131784197 3339166646074579899709537)
  ·
    refine ⟨2504374984555934924782153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3339166646074579899709537 2504374984555934924782153)
    ·
      refine ⟨1878281238416951193586615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2504374984555934924782153 1878281238416951193586615)
      ·
        refine ⟨2817421857625426790379923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878281238416951193586615 2817421857625426790379923)
        ·
          refine ⟨4226132786438140185569885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817421857625426790379923 4226132786438140185569885)
          ·
            refine ⟨1584799794914302569588707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4226132786438140185569885 1584799794914302569588707)
            ·
              refine ⟨2377199692371453854383061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584799794914302569588707 2377199692371453854383061)
              ·
                refine ⟨55715617789955949712103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2377199692371453854383061 55715617789955949712103)
                ·
                  rfl

theorem cell21_732414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_732414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732414 prefixEnd_732414 := by exact prefixLift 732414
  have htrace : WordTrace (prefixWord ++ tailWord_732414) baseStart_732414 baseEnd_732414 := by
    simpa [prefixWord, tailWord_732414, baseEnd_732414] using wordTrace_append hprefix tailTrace_732414
  have hstable : (prefixWord ++ tailWord_732414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732414).length < 2 ^ (prefixWord ++ tailWord_732414).sum := by decide
  have hdescent : baseEnd_732414 < baseStart_732414 := by decide
  rcases family_descends (prefixWord ++ tailWord_732414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732445 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_732445 : Nat := 118140960795 + 732445 * 2 ^ 59
def prefixEnd_732445 : Nat := 4983230072969 + 3 ^ 40 * 732445 * 2
def baseEnd_732445 : Nat := 167153927992218684119579

theorem tailTrace_732445 : CollatzResearch.WordTrace tailWord_732445 prefixEnd_732445 167153927992218684119579 := by
  unfold tailWord_732445
  simp only [CollatzResearch.WordTrace]
  refine ⟨26714463831484331492054789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17809642554322887661369859 26714463831484331492054789)
  ·
    refine ⟨5008961968403312154760273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26714463831484331492054789 5008961968403312154760273)
    ·
      refine ⟨3756721476302484116070205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5008961968403312154760273 3756721476302484116070205)
      ·
        refine ⟨1408770553613431543526327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3756721476302484116070205 1408770553613431543526327)
        ·
          refine ⟨2113155830420147315289491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408770553613431543526327 2113155830420147315289491)
          ·
            refine ⟨3169733745630220972934237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113155830420147315289491 3169733745630220972934237)
            ·
              refine ⟨1188650154611332864850339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3169733745630220972934237 1188650154611332864850339)
              ·
                refine ⟨1782975231916999297275509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188650154611332864850339 1782975231916999297275509)
                ·
                  refine ⟨167153927992218684119579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782975231916999297275509 167153927992218684119579)
                  ·
                    rfl

theorem cell21_732445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_732445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732445 prefixEnd_732445 := by exact prefixLift 732445
  have htrace : WordTrace (prefixWord ++ tailWord_732445) baseStart_732445 baseEnd_732445 := by
    simpa [prefixWord, tailWord_732445, baseEnd_732445] using wordTrace_append hprefix tailTrace_732445
  have hstable : (prefixWord ++ tailWord_732445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732445).length < 2 ^ (prefixWord ++ tailWord_732445).sum := by decide
  have hdescent : baseEnd_732445 < baseStart_732445 := by decide
  rcases family_descends (prefixWord ++ tailWord_732445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732552 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_732552 : Nat := 118140960795 + 732552 * 2 ^ 59
def prefixEnd_732552 : Nat := 4983230072969 + 3 ^ 40 * 732552 * 2
def baseEnd_732552 : Nat := 167178346850010275836027

theorem tailTrace_732552 : CollatzResearch.WordTrace tailWord_732552 prefixEnd_732552 167178346850010275836027 := by
  unfold tailWord_732552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359183221048344383099955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17812244294731125844133273 13359183221048344383099955)
  ·
    refine ⟨20038774831572516574649933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359183221048344383099955 20038774831572516574649933)
    ·
      refine ⟨7514540561839693715493725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20038774831572516574649933 7514540561839693715493725)
      ·
        refine ⟨2817952710689885143310147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7514540561839693715493725 2817952710689885143310147)
        ·
          refine ⟨4226929066034827714965221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817952710689885143310147 4226929066034827714965221)
          ·
            refine ⟨792549199881530196555979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4226929066034827714965221 792549199881530196555979)
            ·
              refine ⟨1188823799822295294833969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792549199881530196555979 1188823799822295294833969)
              ·
                refine ⟨891617849866721471125477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188823799822295294833969 891617849866721471125477)
                ·
                  refine ⟨167178346850010275836027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891617849866721471125477 167178346850010275836027)
                  ·
                    rfl

theorem cell21_732552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_732552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732552 prefixEnd_732552 := by exact prefixLift 732552
  have htrace : WordTrace (prefixWord ++ tailWord_732552) baseStart_732552 baseEnd_732552 := by
    simpa [prefixWord, tailWord_732552, baseEnd_732552] using wordTrace_append hprefix tailTrace_732552
  have hstable : (prefixWord ++ tailWord_732552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732552).length < 2 ^ (prefixWord ++ tailWord_732552).sum := by decide
  have hdescent : baseEnd_732552 < baseStart_732552 := by decide
  rcases family_descends (prefixWord ++ tailWord_732552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732608 : List Nat := [2, 1, 1, 2, 3, 1, 11]
def baseStart_732608 : Nat := 118140960795 + 732608 * 2 ^ 59
def prefixEnd_732608 : Nat := 4983230072969 + 3 ^ 40 * 732608 * 2
def baseEnd_732608 : Nat := 18576791868107402544731

theorem tailTrace_732608 : CollatzResearch.WordTrace tailWord_732608 prefixEnd_732608 18576791868107402544731 := by
  unfold tailWord_732608
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360204464946905165119239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17813605953262540220158985 13360204464946905165119239)
  ·
    refine ⟨20040306697420357747678859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13360204464946905165119239 20040306697420357747678859)
    ·
      refine ⟨30060460046130536621518289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20040306697420357747678859 30060460046130536621518289)
      ·
        refine ⟨22545345034597902466138717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30060460046130536621518289 22545345034597902466138717)
        ·
          refine ⟨8454504387974213424802019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22545345034597902466138717 8454504387974213424802019)
          ·
            refine ⟨12681756581961320137203029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8454504387974213424802019 12681756581961320137203029)
            ·
              refine ⟨18576791868107402544731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12681756581961320137203029 18576791868107402544731)
              ·
                rfl

theorem cell21_732608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 11].length) (baseStart_732608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732608 prefixEnd_732608 := by exact prefixLift 732608
  have htrace : WordTrace (prefixWord ++ tailWord_732608) baseStart_732608 baseEnd_732608 := by
    simpa [prefixWord, tailWord_732608, baseEnd_732608] using wordTrace_append hprefix tailTrace_732608
  have hstable : (prefixWord ++ tailWord_732608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732608).length < 2 ^ (prefixWord ++ tailWord_732608).sum := by decide
  have hdescent : baseEnd_732608 < baseStart_732608 := by decide
  rcases family_descends (prefixWord ++ tailWord_732608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732628 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_732628 : Nat := 118140960795 + 732628 * 2 ^ 59
def prefixEnd_732628 : Nat := 4983230072969 + 3 ^ 40 * 732628 * 2
def baseEnd_732628 : Nat := 167195691085451032569205

theorem tailTrace_732628 : CollatzResearch.WordTrace tailWord_732628 prefixEnd_732628 167195691085451032569205 := by
  unfold tailWord_732628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360569194910676872983269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17814092259880902497311025 13360569194910676872983269)
  ·
    refine ⟨2505106724045751913684363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13360569194910676872983269 2505106724045751913684363)
    ·
      refine ⟨3757660086068627870526545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505106724045751913684363 3757660086068627870526545)
      ·
        refine ⟨2818245064551470902894909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3757660086068627870526545 2818245064551470902894909)
        ·
          refine ⟨1056841899206801588585591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2818245064551470902894909 1056841899206801588585591)
          ·
            refine ⟨1585262848810202382878387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056841899206801588585591 1585262848810202382878387)
            ·
              refine ⟨2377894273215303574317581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585262848810202382878387 2377894273215303574317581)
              ·
                refine ⟨891710352455738840369093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377894273215303574317581 891710352455738840369093)
                ·
                  refine ⟨167195691085451032569205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891710352455738840369093 167195691085451032569205)
                  ·
                    rfl

theorem cell21_732628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_732628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732628 prefixEnd_732628 := by exact prefixLift 732628
  have htrace : WordTrace (prefixWord ++ tailWord_732628) baseStart_732628 baseEnd_732628 := by
    simpa [prefixWord, tailWord_732628, baseEnd_732628] using wordTrace_append hprefix tailTrace_732628
  have hstable : (prefixWord ++ tailWord_732628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732628).length < 2 ^ (prefixWord ++ tailWord_732628).sum := by decide
  have hdescent : baseEnd_732628 < baseStart_732628 := by decide
  rcases family_descends (prefixWord ++ tailWord_732628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732639 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_732639 : Nat := 118140960795 + 732639 * 2 ^ 59
def prefixEnd_732639 : Nat := 4983230072969 + 3 ^ 40 * 732639 * 2
def baseEnd_732639 : Nat := 167198201435317457885849

theorem tailTrace_732639 : CollatzResearch.WordTrace tailWord_732639 prefixEnd_732639 167198201435317457885849 := by
  unfold tailWord_732639
  simp only [CollatzResearch.WordTrace]
  refine ⟨26721539592781502624616971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17814359728521001749744647 26721539592781502624616971)
  ·
    refine ⟨40082309389172253936925457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26721539592781502624616971 40082309389172253936925457)
    ·
      refine ⟨30061732041879190452694093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40082309389172253936925457 30061732041879190452694093)
      ·
        refine ⟨11273149515704696419760285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30061732041879190452694093 11273149515704696419760285)
        ·
          refine ⟨4227431068389261157410107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11273149515704696419760285 4227431068389261157410107)
          ·
            refine ⟨6341146602583891736115161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227431068389261157410107 6341146602583891736115161)
            ·
              refine ⟨4755859951937918802086371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6341146602583891736115161 4755859951937918802086371)
              ·
                refine ⟨7133789927906878203129557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755859951937918802086371 7133789927906878203129557)
                ·
                  refine ⟨167198201435317457885849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7133789927906878203129557 167198201435317457885849)
                  ·
                    rfl

theorem cell21_732639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_732639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732639 prefixEnd_732639 := by exact prefixLift 732639
  have htrace : WordTrace (prefixWord ++ tailWord_732639) baseStart_732639 baseEnd_732639 := by
    simpa [prefixWord, tailWord_732639, baseEnd_732639] using wordTrace_append hprefix tailTrace_732639
  have hstable : (prefixWord ++ tailWord_732639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732639).length < 2 ^ (prefixWord ++ tailWord_732639).sum := by decide
  have hdescent : baseEnd_732639 < baseStart_732639 := by decide
  rcases family_descends (prefixWord ++ tailWord_732639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732836 : List Nat := [2, 3, 1, 2, 2, 11]
def baseStart_732836 : Nat := 118140960795 + 732836 * 2 ^ 59
def prefixEnd_732836 : Nat := 4983230072969 + 3 ^ 40 * 732836 * 2
def baseEnd_732836 : Nat := 6194191093306996040819

theorem tailTrace_732836 : CollatzResearch.WordTrace tailWord_732836 prefixEnd_732836 6194191093306996040819 := by
  unfold tailWord_732836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13364362386533902634769181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17819149848711870179692241 13364362386533902634769181)
  ·
    refine ⟨5011635894950213488038443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13364362386533902634769181 5011635894950213488038443)
    ·
      refine ⟨7517453842425320232057665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011635894950213488038443 7517453842425320232057665)
      ·
        refine ⟨5638090381818990174043249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7517453842425320232057665 5638090381818990174043249)
        ·
          refine ⟨4228567786364242630532437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5638090381818990174043249 4228567786364242630532437)
          ·
            refine ⟨6194191093306996040819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4228567786364242630532437 6194191093306996040819)
            ·
              rfl

theorem cell21_732836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 11].length) (baseStart_732836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732836 prefixEnd_732836 := by exact prefixLift 732836
  have htrace : WordTrace (prefixWord ++ tailWord_732836) baseStart_732836 baseEnd_732836 := by
    simpa [prefixWord, tailWord_732836, baseEnd_732836] using wordTrace_append hprefix tailTrace_732836
  have hstable : (prefixWord ++ tailWord_732836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732836).length < 2 ^ (prefixWord ++ tailWord_732836).sum := by decide
  have hdescent : baseEnd_732836 < baseStart_732836 := by decide
  rcases family_descends (prefixWord ++ tailWord_732836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732929 : List Nat := [1, 2, 4, 1, 1, 1, 6, 5]
def baseStart_732929 : Nat := 118140960795 + 732929 * 2 ^ 59
def prefixEnd_732929 : Nat := 4983230072969 + 3 ^ 40 * 732929 * 2
def baseEnd_732929 : Nat := 55754794462113799350641

theorem tailTrace_732929 : CollatzResearch.WordTrace tailWord_732929 prefixEnd_732929 55754794462113799350641 := by
  unfold tailWord_732929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26732116761730882152673841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17821411174487254768449227 26732116761730882152673841)
  ·
    refine ⟨20049087571298161614505381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26732116761730882152673841 20049087571298161614505381)
    ·
      refine ⟨3759203919618405302719759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20049087571298161614505381 3759203919618405302719759)
      ·
        refine ⟨5638805879427607954079639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759203919618405302719759 5638805879427607954079639)
        ·
          refine ⟨8458208819141411931119459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638805879427607954079639 8458208819141411931119459)
          ·
            refine ⟨12687313228712117896679189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458208819141411931119459 12687313228712117896679189)
            ·
              refine ⟨594717807595880526406837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12687313228712117896679189 594717807595880526406837)
              ·
                refine ⟨55754794462113799350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 594717807595880526406837 55754794462113799350641)
                ·
                  rfl

theorem cell21_732929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 5].length) (baseStart_732929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732929 prefixEnd_732929 := by exact prefixLift 732929
  have htrace : WordTrace (prefixWord ++ tailWord_732929) baseStart_732929 baseEnd_732929 := by
    simpa [prefixWord, tailWord_732929, baseEnd_732929] using wordTrace_append hprefix tailTrace_732929
  have hstable : (prefixWord ++ tailWord_732929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732929).length < 2 ^ (prefixWord ++ tailWord_732929).sum := by decide
  have hdescent : baseEnd_732929 < baseStart_732929 := by decide
  rcases family_descends (prefixWord ++ tailWord_732929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732935 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 3]
def baseStart_732935 : Nat := 118140960795 + 732935 * 2 ^ 59
def prefixEnd_732935 : Nat := 4983230072969 + 3 ^ 40 * 732935 * 2
def baseEnd_732935 : Nat := 167265752668086720951911

theorem tailTrace_732935 : CollatzResearch.WordTrace tailWord_732935 prefixEnd_732935 167265752668086720951911 := by
  unfold tailWord_732935
  simp only [CollatzResearch.WordTrace]
  refine ⟨26732335599709145177392259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17821557066472763451594839 26732335599709145177392259)
  ·
    refine ⟨40098503399563717766088389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26732335599709145177392259 40098503399563717766088389)
    ·
      refine ⟨7518469387418197081141573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40098503399563717766088389 7518469387418197081141573)
      ·
        refine ⟨1409713010140911952714045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7518469387418197081141573 1409713010140911952714045)
        ·
          refine ⟨528642378802841982267767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1409713010140911952714045 528642378802841982267767)
          ·
            refine ⟨792963568204262973401651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528642378802841982267767 792963568204262973401651)
            ·
              refine ⟨1189445352306394460102477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792963568204262973401651 1189445352306394460102477)
              ·
                refine ⟨446042007114897922538429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189445352306394460102477 446042007114897922538429)
                ·
                  refine ⟨167265752668086720951911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446042007114897922538429 167265752668086720951911)
                  ·
                    rfl

theorem cell21_732935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3].length) (baseStart_732935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732935 prefixEnd_732935 := by exact prefixLift 732935
  have htrace : WordTrace (prefixWord ++ tailWord_732935) baseStart_732935 baseEnd_732935 := by
    simpa [prefixWord, tailWord_732935, baseEnd_732935] using wordTrace_append hprefix tailTrace_732935
  have hstable : (prefixWord ++ tailWord_732935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732935).length < 2 ^ (prefixWord ++ tailWord_732935).sum := by decide
  have hdescent : baseEnd_732935 < baseStart_732935 := by decide
  rcases family_descends (prefixWord ++ tailWord_732935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732946 : List Nat := [3, 2, 4, 1, 1, 3, 7]
def baseStart_732946 : Nat := 118140960795 + 732946 * 2 ^ 59
def prefixEnd_732946 : Nat := 4983230072969 + 3 ^ 40 * 732946 * 2
def baseEnd_732946 : Nat := 18585362557550349585395

theorem tailTrace_732946 : CollatzResearch.WordTrace tailWord_732946 prefixEnd_732946 18585362557550349585395 := by
  unfold tailWord_732946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683184200667323514010673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17821824535112862704028461 6683184200667323514010673)
  ·
    refine ⟨5012388150500492635508005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6683184200667323514010673 5012388150500492635508005)
    ·
      refine ⟨939822778218842369157751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5012388150500492635508005 939822778218842369157751)
      ·
        refine ⟨1409734167328263553736627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939822778218842369157751 1409734167328263553736627)
        ·
          refine ⟨2114601250992395330604941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409734167328263553736627 2114601250992395330604941)
          ·
            refine ⟨792975469122148248976853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2114601250992395330604941 792975469122148248976853)
            ·
              refine ⟨18585362557550349585395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 792975469122148248976853 18585362557550349585395)
              ·
                rfl

theorem cell21_732946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 7].length) (baseStart_732946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732946 prefixEnd_732946 := by exact prefixLift 732946
  have htrace : WordTrace (prefixWord ++ tailWord_732946) baseStart_732946 baseEnd_732946 := by
    simpa [prefixWord, tailWord_732946, baseEnd_732946] using wordTrace_append hprefix tailTrace_732946
  have hstable : (prefixWord ++ tailWord_732946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732946).length < 2 ^ (prefixWord ++ tailWord_732946).sum := by decide
  have hdescent : baseEnd_732946 < baseStart_732946 := by decide
  rcases family_descends (prefixWord ++ tailWord_732946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732988 : List Nat := [2, 2, 2, 2, 1, 1, 4, 7]
def baseStart_732988 : Nat := 118140960795 + 732988 * 2 ^ 59
def prefixEnd_732988 : Nat := 4983230072969 + 3 ^ 40 * 732988 * 2
def baseEnd_732988 : Nat := 55759282663390135522823

theorem tailTrace_732988 : CollatzResearch.WordTrace tailWord_732988 prefixEnd_732988 55759282663390135522823 := by
  unfold tailWord_732988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367134334258567614535809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17822845779011423486047745 13367134334258567614535809)
  ·
    refine ⟨10025350750693925710901857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13367134334258567614535809 10025350750693925710901857)
    ·
      refine ⟨7519013063020444283176393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10025350750693925710901857 7519013063020444283176393)
      ·
        refine ⟨5639259797265333212382295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7519013063020444283176393 5639259797265333212382295)
        ·
          refine ⟨8458889695897999818573443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639259797265333212382295 8458889695897999818573443)
          ·
            refine ⟨12688334543846999727860165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458889695897999818573443 12688334543846999727860165)
            ·
              refine ⟨2379062726971312448973781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12688334543846999727860165 2379062726971312448973781)
              ·
                refine ⟨55759282663390135522823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2379062726971312448973781 55759282663390135522823)
                ·
                  rfl

theorem cell21_732988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_732988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_732988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_732988 prefixEnd_732988 := by exact prefixLift 732988
  have htrace : WordTrace (prefixWord ++ tailWord_732988) baseStart_732988 baseEnd_732988 := by
    simpa [prefixWord, tailWord_732988, baseEnd_732988] using wordTrace_append hprefix tailTrace_732988
  have hstable : (prefixWord ++ tailWord_732988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732988).length < 2 ^ (prefixWord ++ tailWord_732988).sum := by decide
  have hdescent : baseEnd_732988 < baseStart_732988 := by decide
  rcases family_descends (prefixWord ++ tailWord_732988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733005 : List Nat := [1, 6, 1, 2, 1, 10]
def baseStart_733005 : Nat := 118140960795 + 733005 * 2 ^ 59
def prefixEnd_733005 : Nat := 4983230072969 + 3 ^ 40 * 733005 * 2
def baseEnd_733005 : Nat := 6195619541547487214263

theorem tailTrace_733005 : CollatzResearch.WordTrace tailWord_733005 prefixEnd_733005 6195619541547487214263 := by
  unfold tailWord_733005
  simp only [CollatzResearch.WordTrace]
  refine ⟨26734888709455547132440469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823259139637031421626979 26734888709455547132440469)
  ·
    refine ⟨1253197908255728771833147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26734888709455547132440469 1253197908255728771833147)
    ·
      refine ⟨1879796862383593157749721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253197908255728771833147 1879796862383593157749721)
      ·
        refine ⟨1409847646787694868312291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1879796862383593157749721 1409847646787694868312291)
        ·
          refine ⟨2114771470181542302468437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409847646787694868312291 2114771470181542302468437)
          ·
            refine ⟨6195619541547487214263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2114771470181542302468437 6195619541547487214263)
            ·
              rfl

theorem cell21_733005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 10].length) (baseStart_733005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733005 prefixEnd_733005 := by exact prefixLift 733005
  have htrace : WordTrace (prefixWord ++ tailWord_733005) baseStart_733005 baseEnd_733005 := by
    simpa [prefixWord, tailWord_733005, baseEnd_733005] using wordTrace_append hprefix tailTrace_733005
  have hstable : (prefixWord ++ tailWord_733005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733005).length < 2 ^ (prefixWord ++ tailWord_733005).sum := by decide
  have hdescent : baseEnd_733005 < baseStart_733005 := by decide
  rcases family_descends (prefixWord ++ tailWord_733005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733084 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_733084 : Nat := 118140960795 + 733084 * 2 ^ 59
def prefixEnd_733084 : Nat := 4983230072969 + 3 ^ 40 * 733084 * 2
def baseEnd_733084 : Nat := 167299756498095572968273

theorem tailTrace_733084 : CollatzResearch.WordTrace tailWord_733084 prefixEnd_733084 167299756498095572968273 := by
  unfold tailWord_733084
  simp only [CollatzResearch.WordTrace]
  refine ⟨13368885038084671812283153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17825180050779562416377537 13368885038084671812283153)
  ·
    refine ⟨10026663778563503859212365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13368885038084671812283153 10026663778563503859212365)
    ·
      refine ⟨3759998916961313947204637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10026663778563503859212365 3759998916961313947204637)
      ·
        refine ⟨1409999593860492730201739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3759998916961313947204637 1409999593860492730201739)
        ·
          refine ⟨2114999390790739095302609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409999593860492730201739 2114999390790739095302609)
          ·
            refine ⟨1586249543093054321476957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114999390790739095302609 1586249543093054321476957)
            ·
              refine ⟨594843578659895370553859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1586249543093054321476957 594843578659895370553859)
              ·
                refine ⟨892265367989843055830789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594843578659895370553859 892265367989843055830789)
                ·
                  refine ⟨167299756498095572968273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892265367989843055830789 167299756498095572968273)
                  ·
                    rfl

theorem cell21_733084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_733084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733084 prefixEnd_733084 := by exact prefixLift 733084
  have htrace : WordTrace (prefixWord ++ tailWord_733084) baseStart_733084 baseEnd_733084 := by
    simpa [prefixWord, tailWord_733084, baseEnd_733084] using wordTrace_append hprefix tailTrace_733084
  have hstable : (prefixWord ++ tailWord_733084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733084).length < 2 ^ (prefixWord ++ tailWord_733084).sum := by decide
  have hdescent : baseEnd_733084 < baseStart_733084 := by decide
  rcases family_descends (prefixWord ++ tailWord_733084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733292 : List Nat := [2, 2, 1, 1, 3, 5, 7]
def baseStart_733292 : Nat := 118140960795 + 733292 * 2 ^ 59
def prefixEnd_733292 : Nat := 4983230072969 + 3 ^ 40 * 733292 * 2
def baseEnd_733292 : Nat := 18594136103548159277909

theorem tailTrace_733292 : CollatzResearch.WordTrace tailWord_733292 prefixEnd_733292 18594136103548159277909 := by
  unfold tailWord_733292
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372678229707897574069065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17830237639610530098758753 13372678229707897574069065)
  ·
    refine ⟨10029508672280923180551799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13372678229707897574069065 10029508672280923180551799)
    ·
      refine ⟨15044263008421384770827699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10029508672280923180551799 15044263008421384770827699)
      ·
        refine ⟨22566394512632077156241549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15044263008421384770827699 22566394512632077156241549)
        ·
          refine ⟨8462397942237028933590581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22566394512632077156241549 8462397942237028933590581)
          ·
            refine ⟨793349807084721462524117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8462397942237028933590581 793349807084721462524117)
            ·
              refine ⟨18594136103548159277909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 793349807084721462524117 18594136103548159277909)
              ·
                rfl

theorem cell21_733292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 7].length) (baseStart_733292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733292 prefixEnd_733292 := by exact prefixLift 733292
  have htrace : WordTrace (prefixWord ++ tailWord_733292) baseStart_733292 baseEnd_733292 := by
    simpa [prefixWord, tailWord_733292, baseEnd_733292] using wordTrace_append hprefix tailTrace_733292
  have hstable : (prefixWord ++ tailWord_733292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733292).length < 2 ^ (prefixWord ++ tailWord_733292).sum := by decide
  have hdescent : baseEnd_733292 < baseStart_733292 := by decide
  rcases family_descends (prefixWord ++ tailWord_733292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733340 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_733340 : Nat := 118140960795 + 733340 * 2 ^ 59
def prefixEnd_733340 : Nat := 4983230072969 + 3 ^ 40 * 733340 * 2
def baseEnd_733340 : Nat := 167358179185896016701083

theorem tailTrace_733340 : CollatzResearch.WordTrace tailWord_733340 prefixEnd_733340 167358179185896016701083 := by
  unfold tailWord_733340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13373553581620949672942737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17831404775494599563923649 13373553581620949672942737)
  ·
    refine ⟨10030165186215712254707053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13373553581620949672942737 10030165186215712254707053)
    ·
      refine ⟨3761311944830892095515145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10030165186215712254707053 3761311944830892095515145)
      ·
        refine ⟨2820983958623169071636359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3761311944830892095515145 2820983958623169071636359)
        ·
          refine ⟨4231475937934753607454539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820983958623169071636359 4231475937934753607454539)
          ·
            refine ⟨6347213906902130411181809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231475937934753607454539 6347213906902130411181809)
            ·
              refine ⟨4760410430176597808386357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347213906902130411181809 4760410430176597808386357)
              ·
                refine ⟨446288477829056044536221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4760410430176597808386357 446288477829056044536221)
                ·
                  refine ⟨167358179185896016701083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446288477829056044536221 167358179185896016701083)
                  ·
                    rfl

theorem cell21_733340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_733340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733340 prefixEnd_733340 := by exact prefixLift 733340
  have htrace : WordTrace (prefixWord ++ tailWord_733340) baseStart_733340 baseEnd_733340 := by
    simpa [prefixWord, tailWord_733340, baseEnd_733340] using wordTrace_append hprefix tailTrace_733340
  have hstable : (prefixWord ++ tailWord_733340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733340).length < 2 ^ (prefixWord ++ tailWord_733340).sum := by decide
  have hdescent : baseEnd_733340 < baseStart_733340 := by decide
  rcases family_descends (prefixWord ++ tailWord_733340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733357 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 3]
def baseStart_733357 : Nat := 118140960795 + 733357 * 2 ^ 59
def prefixEnd_733357 : Nat := 4983230072969 + 3 ^ 40 * 733357 * 2
def baseEnd_733357 : Nat := 167362058817507764917715

theorem tailTrace_733357 : CollatzResearch.WordTrace tailWord_733357 prefixEnd_733357 167362058817507764917715 := by
  unfold tailWord_733357
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747727204180311249254325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17831818136120207499502883 26747727204180311249254325)
  ·
    refine ⟨2507599425391904179617593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26747727204180311249254325 2507599425391904179617593)
    ·
      refine ⟨1880699569043928134713195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2507599425391904179617593 1880699569043928134713195)
      ·
        refine ⟨2821049353565892202069793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880699569043928134713195 2821049353565892202069793)
        ·
          refine ⟨2115787015174419151552345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821049353565892202069793 2115787015174419151552345)
          ·
            refine ⟨1586840261380814363664259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2115787015174419151552345 1586840261380814363664259)
            ·
              refine ⟨2380260392071221545496389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586840261380814363664259 2380260392071221545496389)
              ·
                refine ⟨446298823513354039780573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2380260392071221545496389 446298823513354039780573)
                ·
                  refine ⟨167362058817507764917715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446298823513354039780573 167362058817507764917715)
                  ·
                    rfl

theorem cell21_733357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_733357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733357 prefixEnd_733357 := by exact prefixLift 733357
  have htrace : WordTrace (prefixWord ++ tailWord_733357) baseStart_733357 baseEnd_733357 := by
    simpa [prefixWord, tailWord_733357, baseEnd_733357] using wordTrace_append hprefix tailTrace_733357
  have hstable : (prefixWord ++ tailWord_733357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733357).length < 2 ^ (prefixWord ++ tailWord_733357).sum := by decide
  have hdescent : baseEnd_733357 < baseStart_733357 := by decide
  rcases family_descends (prefixWord ++ tailWord_733357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733416 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_733416 : Nat := 118140960795 + 733416 * 2 ^ 59
def prefixEnd_733416 : Nat := 4983230072969 + 3 ^ 40 * 733416 * 2
def baseEnd_733416 : Nat := 167375523421336773434261

theorem tailTrace_733416 : CollatzResearch.WordTrace tailWord_733416 prefixEnd_733416 167375523421336773434261 := by
  unfold tailWord_733416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374939555483282162826051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17833252740644376217101401 13374939555483282162826051)
  ·
    refine ⟨20062409333224923244239077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13374939555483282162826051 20062409333224923244239077)
    ·
      refine ⟨3761701749979673108294827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20062409333224923244239077 3761701749979673108294827)
      ·
        refine ⟨5642552624969509662442241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761701749979673108294827 5642552624969509662442241)
        ·
          refine ⟨4231914468727132246831681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5642552624969509662442241 4231914468727132246831681)
          ·
            refine ⟨3173935851545349185123761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231914468727132246831681 3173935851545349185123761)
            ·
              refine ⟨2380451888659011888842821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173935851545349185123761 2380451888659011888842821)
              ·
                refine ⟨446334729123564729158029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2380451888659011888842821 446334729123564729158029)
                ·
                  refine ⟨167375523421336773434261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446334729123564729158029 167375523421336773434261)
                  ·
                    rfl

theorem cell21_733416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_733416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733416 prefixEnd_733416 := by exact prefixLift 733416
  have htrace : WordTrace (prefixWord ++ tailWord_733416) baseStart_733416 baseEnd_733416 := by
    simpa [prefixWord, tailWord_733416, baseEnd_733416] using wordTrace_append hprefix tailTrace_733416
  have hstable : (prefixWord ++ tailWord_733416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733416).length < 2 ^ (prefixWord ++ tailWord_733416).sum := by decide
  have hdescent : baseEnd_733416 < baseStart_733416 := by decide
  rcases family_descends (prefixWord ++ tailWord_733416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733427 : List Nat := [1, 1, 1, 2, 2, 4, 2, 8]
def baseStart_733427 : Nat := 118140960795 + 733427 * 2 ^ 59
def prefixEnd_733427 : Nat := 4983230072969 + 3 ^ 40 * 733427 * 2
def baseEnd_733427 : Nat := 55792677923734399583635

theorem tailTrace_733427 : CollatzResearch.WordTrace tailWord_733427 prefixEnd_733427 55792677923734399583635 := by
  unfold tailWord_733427
  simp only [CollatzResearch.WordTrace]
  refine ⟨26750280313926713204302535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17833520209284475469535023 26750280313926713204302535)
  ·
    refine ⟨40125420470890069806453803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26750280313926713204302535 40125420470890069806453803)
    ·
      refine ⟨60188130706335104709680705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40125420470890069806453803 60188130706335104709680705)
      ·
        refine ⟨45141098029751328532260529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60188130706335104709680705 45141098029751328532260529)
        ·
          refine ⟨33855823522313496399195397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45141098029751328532260529 33855823522313496399195397)
          ·
            refine ⟨6347966910433780574849137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33855823522313496399195397 6347966910433780574849137)
            ·
              refine ⟨4760975182825335431136853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347966910433780574849137 4760975182825335431136853)
              ·
                refine ⟨55792677923734399583635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4760975182825335431136853 55792677923734399583635)
                ·
                  rfl

theorem cell21_733427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_733427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733427 prefixEnd_733427 := by exact prefixLift 733427
  have htrace : WordTrace (prefixWord ++ tailWord_733427) baseStart_733427 baseEnd_733427 := by
    simpa [prefixWord, tailWord_733427, baseEnd_733427] using wordTrace_append hprefix tailTrace_733427
  have hstable : (prefixWord ++ tailWord_733427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733427).length < 2 ^ (prefixWord ++ tailWord_733427).sum := by decide
  have hdescent : baseEnd_733427 < baseStart_733427 := by decide
  rcases family_descends (prefixWord ++ tailWord_733427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733430 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_733430 : Nat := 118140960795 + 733430 * 2 ^ 59
def prefixEnd_733430 : Nat := 4983230072969 + 3 ^ 40 * 733430 * 2
def baseEnd_733430 : Nat := 167378718412075860200899

theorem tailTrace_733430 : CollatzResearch.WordTrace tailWord_733430 prefixEnd_733430 167378718412075860200899 := by
  unfold tailWord_733430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671899358307240294791359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17833593155277229811107829 1671899358307240294791359)
  ·
    refine ⟨2507849037460860442187039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671899358307240294791359 2507849037460860442187039)
    ·
      refine ⟨3761773556191290663280559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507849037460860442187039 3761773556191290663280559)
      ·
        refine ⟨5642660334286935994920839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761773556191290663280559 5642660334286935994920839)
        ·
          refine ⟨8463990501430403992381259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642660334286935994920839 8463990501430403992381259)
          ·
            refine ⟨12695985752145605988571889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463990501430403992381259 12695985752145605988571889)
            ·
              refine ⟨9521989314109204491428917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12695985752145605988571889 9521989314109204491428917)
              ·
                refine ⟨892686498197737921071461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9521989314109204491428917 892686498197737921071461)
                ·
                  refine ⟨167378718412075860200899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892686498197737921071461 167378718412075860200899)
                  ·
                    rfl

theorem cell21_733430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_733430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733430 prefixEnd_733430 := by exact prefixLift 733430
  have htrace : WordTrace (prefixWord ++ tailWord_733430) baseStart_733430 baseEnd_733430 := by
    simpa [prefixWord, tailWord_733430, baseEnd_733430] using wordTrace_append hprefix tailTrace_733430
  have hstable : (prefixWord ++ tailWord_733430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733430).length < 2 ^ (prefixWord ++ tailWord_733430).sum := by decide
  have hdescent : baseEnd_733430 < baseStart_733430 := by decide
  rcases family_descends (prefixWord ++ tailWord_733430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733503 : List Nat := [1, 1, 2, 2, 4, 1, 1, 9]
def baseStart_733503 : Nat := 118140960795 + 733503 * 2 ^ 59
def prefixEnd_733503 : Nat := 4983230072969 + 3 ^ 40 * 733503 * 2
def baseEnd_733503 : Nat := 55798459335547985161361

theorem tailTrace_733503 : CollatzResearch.WordTrace tailWord_733503 prefixEnd_733503 55798459335547985161361 := by
  unfold tailWord_733503
  simp only [CollatzResearch.WordTrace]
  refine ⟨26753052261651378184069163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17835368174434252122712775 26753052261651378184069163)
  ·
    refine ⟨40129578392477067276103745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26753052261651378184069163 40129578392477067276103745)
    ·
      refine ⟨30097183794357800457077809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40129578392477067276103745 30097183794357800457077809)
      ·
        refine ⟨22572887845768350342808357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30097183794357800457077809 22572887845768350342808357)
        ·
          refine ⟨4232416471081565689276567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22572887845768350342808357 4232416471081565689276567)
          ·
            refine ⟨6348624706622348533914851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232416471081565689276567 6348624706622348533914851)
            ·
              refine ⟨9522937059933522800872277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348624706622348533914851 9522937059933522800872277)
              ·
                refine ⟨55798459335547985161361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9522937059933522800872277 55798459335547985161361)
                ·
                  rfl

theorem cell21_733503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_733503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733503 prefixEnd_733503 := by exact prefixLift 733503
  have htrace : WordTrace (prefixWord ++ tailWord_733503) baseStart_733503 baseEnd_733503 := by
    simpa [prefixWord, tailWord_733503, baseEnd_733503] using wordTrace_append hprefix tailTrace_733503
  have hstable : (prefixWord ++ tailWord_733503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733503).length < 2 ^ (prefixWord ++ tailWord_733503).sum := by decide
  have hdescent : baseEnd_733503 < baseStart_733503 := by decide
  rcases family_descends (prefixWord ++ tailWord_733503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733579 : List Nat := [1, 1, 1, 1, 4, 5, 8]
def baseStart_733579 : Nat := 118140960795 + 733579 * 2 ^ 59
def prefixEnd_733579 : Nat := 4983230072969 + 3 ^ 40 * 733579 * 2
def baseEnd_733579 : Nat := 18601413582453856913029

theorem tailTrace_733579 : CollatzResearch.WordTrace tailWord_733579 prefixEnd_733579 18601413582453856913029 := by
  unfold tailWord_733579
  simp only [CollatzResearch.WordTrace]
  refine ⟨26755824209376043163835791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17837216139584028775890527 26755824209376043163835791)
  ·
    refine ⟨40133736314064064745753687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26755824209376043163835791 40133736314064064745753687)
    ·
      refine ⟨60200604471096097118630531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40133736314064064745753687 60200604471096097118630531)
      ·
        refine ⟨90300906706644145677945797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60200604471096097118630531 90300906706644145677945797)
        ·
          refine ⟨16931420007495777314614837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90300906706644145677945797 16931420007495777314614837)
          ·
            refine ⟨1587320625702729123245141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16931420007495777314614837 1587320625702729123245141)
            ·
              refine ⟨18601413582453856913029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1587320625702729123245141 18601413582453856913029)
              ·
                rfl

theorem cell21_733579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 8].length) (baseStart_733579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733579 prefixEnd_733579 := by exact prefixLift 733579
  have htrace : WordTrace (prefixWord ++ tailWord_733579) baseStart_733579 baseEnd_733579 := by
    simpa [prefixWord, tailWord_733579, baseEnd_733579] using wordTrace_append hprefix tailTrace_733579
  have hstable : (prefixWord ++ tailWord_733579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733579).length < 2 ^ (prefixWord ++ tailWord_733579).sum := by decide
  have hdescent : baseEnd_733579 < baseStart_733579 := by decide
  rcases family_descends (prefixWord ++ tailWord_733579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733582 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_733582 : Nat := 118140960795 + 733582 * 2 ^ 59
def prefixEnd_733582 : Nat := 4983230072969 + 3 ^ 40 * 733582 * 2
def baseEnd_733582 : Nat := 167413406882957373667255

theorem tailTrace_733582 : CollatzResearch.WordTrace tailWord_733582 prefixEnd_733582 167413406882957373667255 := by
  unfold tailWord_733582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344491703545646834524375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17837289085576783117463333 3344491703545646834524375)
  ·
    refine ⟨5016737555318470251786563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3344491703545646834524375 5016737555318470251786563)
    ·
      refine ⟨7525106332977705377679845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5016737555318470251786563 7525106332977705377679845)
      ·
        refine ⟨1410957437433319758314971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7525106332977705377679845 1410957437433319758314971)
        ·
          refine ⟨2116436156149979637472457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410957437433319758314971 2116436156149979637472457)
          ·
            refine ⟨1587327117112484728104343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116436156149979637472457 1587327117112484728104343)
            ·
              refine ⟨2380990675668727092156515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587327117112484728104343 2380990675668727092156515)
              ·
                refine ⟨3571486013503090638234773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380990675668727092156515 3571486013503090638234773)
                ·
                  refine ⟨167413406882957373667255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3571486013503090638234773 167413406882957373667255)
                  ·
                    rfl

theorem cell21_733582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_733582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733582 prefixEnd_733582 := by exact prefixLift 733582
  have htrace : WordTrace (prefixWord ++ tailWord_733582) baseStart_733582 baseEnd_733582 := by
    simpa [prefixWord, tailWord_733582, baseEnd_733582] using wordTrace_append hprefix tailTrace_733582
  have hstable : (prefixWord ++ tailWord_733582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733582).length < 2 ^ (prefixWord ++ tailWord_733582).sum := by decide
  have hdescent : baseEnd_733582 < baseStart_733582 := by decide
  rcases family_descends (prefixWord ++ tailWord_733582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733613 : List Nat := [1, 5, 2, 2, 2, 1, 1, 7]
def baseStart_733613 : Nat := 118140960795 + 733613 * 2 ^ 59
def prefixEnd_733613 : Nat := 4983230072969 + 3 ^ 40 * 733613 * 2
def baseEnd_733613 : Nat := 55806827168436069550175

theorem tailTrace_733613 : CollatzResearch.WordTrace tailWord_733613 prefixEnd_733613 55806827168436069550175 := by
  unfold tailWord_733613
  simp only [CollatzResearch.WordTrace]
  refine ⟨26757064291252866970573493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17838042860835244647048995 26757064291252866970573493)
  ·
    refine ⟨2508474777304956278491265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26757064291252866970573493 2508474777304956278491265)
    ·
      refine ⟨1881356082978717208868449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2508474777304956278491265 1881356082978717208868449)
      ·
        refine ⟨1411017062234037906651337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881356082978717208868449 1411017062234037906651337)
        ·
          refine ⟨1058262796675528429988503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411017062234037906651337 1058262796675528429988503)
          ·
            refine ⟨1587394195013292644982755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058262796675528429988503 1587394195013292644982755)
            ·
              refine ⟨2381091292519938967474133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587394195013292644982755 2381091292519938967474133)
              ·
                refine ⟨55806827168436069550175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2381091292519938967474133 55806827168436069550175)
                ·
                  rfl

theorem cell21_733613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_733613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733613 prefixEnd_733613 := by exact prefixLift 733613
  have htrace : WordTrace (prefixWord ++ tailWord_733613) baseStart_733613 baseEnd_733613 := by
    simpa [prefixWord, tailWord_733613, baseEnd_733613] using wordTrace_append hprefix tailTrace_733613
  have hstable : (prefixWord ++ tailWord_733613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733613).length < 2 ^ (prefixWord ++ tailWord_733613).sum := by decide
  have hdescent : baseEnd_733613 < baseStart_733613 := by decide
  rcases family_descends (prefixWord ++ tailWord_733613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733644 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_733644 : Nat := 118140960795 + 733644 * 2 ^ 59
def prefixEnd_733644 : Nat := 4983230072969 + 3 ^ 40 * 733644 * 2
def baseEnd_733644 : Nat := 167427556127659043633795

theorem tailTrace_733644 : CollatzResearch.WordTrace tailWord_733644 prefixEnd_733644 167427556127659043633795 := by
  unfold tailWord_733644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379097477070279632475993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17838796636093706176634657 13379097477070279632475993)
  ·
    refine ⟨10034323107802709724356995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13379097477070279632475993 10034323107802709724356995)
    ·
      refine ⟨15051484661704064586535493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10034323107802709724356995 15051484661704064586535493)
      ·
        refine ⟨2822153374069512109975405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15051484661704064586535493 2822153374069512109975405)
        ·
          refine ⟨1058307515276067041240777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2822153374069512109975405 1058307515276067041240777)
          ·
            refine ⟨793730636457050280930583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058307515276067041240777 793730636457050280930583)
            ·
              refine ⟨1190595954685575421395875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793730636457050280930583 1190595954685575421395875)
              ·
                refine ⟨1785893932028363132093813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190595954685575421395875 1785893932028363132093813)
                ·
                  refine ⟨167427556127659043633795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1785893932028363132093813 167427556127659043633795)
                  ·
                    rfl

theorem cell21_733644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_733644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733644 prefixEnd_733644 := by exact prefixLift 733644
  have htrace : WordTrace (prefixWord ++ tailWord_733644) baseStart_733644 baseEnd_733644 := by
    simpa [prefixWord, tailWord_733644, baseEnd_733644] using wordTrace_append hprefix tailTrace_733644
  have hstable : (prefixWord ++ tailWord_733644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733644).length < 2 ^ (prefixWord ++ tailWord_733644).sum := by decide
  have hdescent : baseEnd_733644 < baseStart_733644 := by decide
  rcases family_descends (prefixWord ++ tailWord_733644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733717 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_733717 : Nat := 118140960795 + 733717 * 2 ^ 59
def prefixEnd_733717 : Nat := 4983230072969 + 3 ^ 40 * 733717 * 2
def baseEnd_733717 : Nat := 167444215722227138916979

theorem tailTrace_733717 : CollatzResearch.WordTrace tailWord_733717 prefixEnd_733717 167444215722227138916979 := by
  unfold tailWord_733717
  simp only [CollatzResearch.WordTrace]
  refine ⟨26760857482876092732359405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17840571655250728488239603 26760857482876092732359405)
  ·
    refine ⟨10035321556078534774634777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26760857482876092732359405 10035321556078534774634777)
    ·
      refine ⟨7526491167058901080976083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10035321556078534774634777 7526491167058901080976083)
      ·
        refine ⟨11289736750588351621464125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526491167058901080976083 11289736750588351621464125)
        ·
          refine ⟨4233651281470631858049047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11289736750588351621464125 4233651281470631858049047)
          ·
            refine ⟨6350476922205947787073571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233651281470631858049047 6350476922205947787073571)
            ·
              refine ⟨9525715383308921680610357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350476922205947787073571 9525715383308921680610357)
              ·
                refine ⟨893035817185211407557221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9525715383308921680610357 893035817185211407557221)
                ·
                  refine ⟨167444215722227138916979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893035817185211407557221 167444215722227138916979)
                  ·
                    rfl

theorem cell21_733717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_733717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733717 prefixEnd_733717 := by exact prefixLift 733717
  have htrace : WordTrace (prefixWord ++ tailWord_733717) baseStart_733717 baseEnd_733717 := by
    simpa [prefixWord, tailWord_733717, baseEnd_733717] using wordTrace_append hprefix tailTrace_733717
  have hstable : (prefixWord ++ tailWord_733717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733717).length < 2 ^ (prefixWord ++ tailWord_733717).sum := by decide
  have hdescent : baseEnd_733717 < baseStart_733717 := by decide
  rcases family_descends (prefixWord ++ tailWord_733717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733813 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 5]
def baseStart_733813 : Nat := 118140960795 + 733813 * 2 ^ 59
def prefixEnd_733813 : Nat := 4983230072969 + 3 ^ 40 * 733813 * 2
def baseEnd_733813 : Nat := 167466124230152305316783

theorem tailTrace_733813 : CollatzResearch.WordTrace tailWord_733813 prefixEnd_733813 167466124230152305316783 := by
  unfold tailWord_733813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764358890528301127854093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17842905927018867418569395 26764358890528301127854093)
  ·
    refine ⟨10036634583948112922945285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26764358890528301127854093 10036634583948112922945285)
    ·
      refine ⟨1881868984490271173052241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10036634583948112922945285 1881868984490271173052241)
      ·
        refine ⟨1411401738367703379789181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881868984490271173052241 1411401738367703379789181)
        ·
          refine ⟨529275651887888767420943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1411401738367703379789181 529275651887888767420943)
          ·
            refine ⟨793913477831833151131415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529275651887888767420943 793913477831833151131415)
            ·
              refine ⟨1190870216747749726697123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793913477831833151131415 1190870216747749726697123)
              ·
                refine ⟨1786305325121624590045685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190870216747749726697123 1786305325121624590045685)
                ·
                  refine ⟨167466124230152305316783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1786305325121624590045685 167466124230152305316783)
                  ·
                    rfl

theorem cell21_733813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_733813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733813 prefixEnd_733813 := by exact prefixLift 733813
  have htrace : WordTrace (prefixWord ++ tailWord_733813) baseStart_733813 baseEnd_733813 := by
    simpa [prefixWord, tailWord_733813, baseEnd_733813] using wordTrace_append hprefix tailTrace_733813
  have hstable : (prefixWord ++ tailWord_733813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733813).length < 2 ^ (prefixWord ++ tailWord_733813).sum := by decide
  have hdescent : baseEnd_733813 < baseStart_733813 := by decide
  rcases family_descends (prefixWord ++ tailWord_733813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733838 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_733838 : Nat := 118140960795 + 733838 * 2 ^ 59
def prefixEnd_733838 : Nat := 4983230072969 + 3 ^ 40 * 733838 * 2
def baseEnd_733838 : Nat := 167471829570757817400065

theorem tailTrace_733838 : CollatzResearch.WordTrace tailWord_733838 prefixEnd_733838 167471829570757817400065 := by
  unfold tailWord_733838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345658839429716299689271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17843513810291820265009445 3345658839429716299689271)
  ·
    refine ⟨5018488259144574449533907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3345658839429716299689271 5018488259144574449533907)
    ·
      refine ⟨7527732388716861674300861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5018488259144574449533907 7527732388716861674300861)
      ·
        refine ⟨2822899645768823127862823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7527732388716861674300861 2822899645768823127862823)
        ·
          refine ⟨4234349468653234691794235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822899645768823127862823 4234349468653234691794235)
          ·
            refine ⟨6351524202979852037691353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234349468653234691794235 6351524202979852037691353)
            ·
              refine ⟨4763643152234889028268515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351524202979852037691353 4763643152234889028268515)
              ·
                refine ⟨7145464728352333542402773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763643152234889028268515 7145464728352333542402773)
                ·
                  refine ⟨167471829570757817400065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7145464728352333542402773 167471829570757817400065)
                  ·
                    rfl

theorem cell21_733838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_733838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_733838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_733838 prefixEnd_733838 := by exact prefixLift 733838
  have htrace : WordTrace (prefixWord ++ tailWord_733838) baseStart_733838 baseEnd_733838 := by
    simpa [prefixWord, tailWord_733838, baseEnd_733838] using wordTrace_append hprefix tailTrace_733838
  have hstable : (prefixWord ++ tailWord_733838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733838).length < 2 ^ (prefixWord ++ tailWord_733838).sum := by decide
  have hdescent : baseEnd_733838 < baseStart_733838 := by decide
  rcases family_descends (prefixWord ++ tailWord_733838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734052 : List Nat := [2, 3, 1, 1, 4, 3, 1, 6]
def baseStart_734052 : Nat := 118140960795 + 734052 * 2 ^ 59
def prefixEnd_734052 : Nat := 4983230072969 + 3 ^ 40 * 734052 * 2
def baseEnd_734052 : Nat := 55840222428780333610987

theorem tailTrace_734052 : CollatzResearch.WordTrace tailWord_734052 prefixEnd_734052 55840222428780333610987 := by
  unfold tailWord_734052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386537968331222472902205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17848717291108296630536273 13386537968331222472902205)
  ·
    refine ⟨5019951738124208427338327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13386537968331222472902205 5019951738124208427338327)
    ·
      refine ⟨7529927607186312641007491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019951738124208427338327 7529927607186312641007491)
      ·
        refine ⟨11294891410779468961511237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529927607186312641007491 11294891410779468961511237)
        ·
          refine ⟨2117792139521150430283357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11294891410779468961511237 2117792139521150430283357)
          ·
            refine ⟨794172052320431411356259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2117792139521150430283357 794172052320431411356259)
            ·
              refine ⟨1191258078480647117034389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794172052320431411356259 1191258078480647117034389)
              ·
                refine ⟨55840222428780333610987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1191258078480647117034389 55840222428780333610987)
                ·
                  rfl

theorem cell21_734052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_734052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734052 prefixEnd_734052 := by exact prefixLift 734052
  have htrace : WordTrace (prefixWord ++ tailWord_734052) baseStart_734052 baseEnd_734052 := by
    simpa [prefixWord, tailWord_734052, baseEnd_734052] using wordTrace_append hprefix tailTrace_734052
  have hstable : (prefixWord ++ tailWord_734052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734052).length < 2 ^ (prefixWord ++ tailWord_734052).sum := by decide
  have hdescent : baseEnd_734052 < baseStart_734052 := by decide
  rcases family_descends (prefixWord ++ tailWord_734052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734083 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 3]
def baseStart_734083 : Nat := 118140960795 + 734083 * 2 ^ 59
def prefixEnd_734083 : Nat := 4983230072969 + 3 ^ 40 * 734083 * 2
def baseEnd_734083 : Nat := 167527741908691835816231

theorem tailTrace_734083 : CollatzResearch.WordTrace tailWord_734083 prefixEnd_734083 167527741908691835816231 := by
  unfold tailWord_734083
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774206599550137240182903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17849471066366758160121935 26774206599550137240182903)
  ·
    refine ⟨40161309899325205860274355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26774206599550137240182903 40161309899325205860274355)
    ·
      refine ⟨60241964848987808790411533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40161309899325205860274355 60241964848987808790411533)
      ·
        refine ⟨22590736818370428296404325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60241964848987808790411533 22590736818370428296404325)
        ·
          refine ⟨4235763153444455305575811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22590736818370428296404325 4235763153444455305575811)
          ·
            refine ⟨6353644730166682958363717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235763153444455305575811 6353644730166682958363717)
            ·
              refine ⟨1191308386906253054693197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6353644730166682958363717 1191308386906253054693197)
              ·
                refine ⟨446740645089844895509949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191308386906253054693197 446740645089844895509949)
                ·
                  refine ⟨167527741908691835816231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446740645089844895509949 167527741908691835816231)
                  ·
                    rfl

theorem cell21_734083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3].length) (baseStart_734083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734083 prefixEnd_734083 := by exact prefixLift 734083
  have htrace : WordTrace (prefixWord ++ tailWord_734083) baseStart_734083 baseEnd_734083 := by
    simpa [prefixWord, tailWord_734083, baseEnd_734083] using wordTrace_append hprefix tailTrace_734083
  have hstable : (prefixWord ++ tailWord_734083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734083).length < 2 ^ (prefixWord ++ tailWord_734083).sum := by decide
  have hdescent : baseEnd_734083 < baseStart_734083 := by decide
  rcases family_descends (prefixWord ++ tailWord_734083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734156 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_734156 : Nat := 118140960795 + 734156 * 2 ^ 59
def prefixEnd_734156 : Nat := 4983230072969 + 3 ^ 40 * 734156 * 2
def baseEnd_734156 : Nat := 167544401503259931099415

theorem tailTrace_734156 : CollatzResearch.WordTrace tailWord_734156 prefixEnd_734156 167544401503259931099415 := by
  unfold tailWord_734156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388434564142835353795161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17851246085523780471726881 13388434564142835353795161)
  ·
    refine ⟨10041325923107126515346371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13388434564142835353795161 10041325923107126515346371)
    ·
      refine ⟨15061988884660689773019557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10041325923107126515346371 15061988884660689773019557)
      ·
        refine ⟨2824122915873879332441167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15061988884660689773019557 2824122915873879332441167)
        ·
          refine ⟨4236184373810818998661751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824122915873879332441167 4236184373810818998661751)
          ·
            refine ⟨6354276560716228497992627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236184373810818998661751 6354276560716228497992627)
            ·
              refine ⟨9531414841074342746988941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354276560716228497992627 9531414841074342746988941)
              ·
                refine ⟨3574280565402878530120853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9531414841074342746988941 3574280565402878530120853)
                ·
                  refine ⟨167544401503259931099415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3574280565402878530120853 167544401503259931099415)
                  ·
                    rfl

theorem cell21_734156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_734156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734156 prefixEnd_734156 := by exact prefixLift 734156
  have htrace : WordTrace (prefixWord ++ tailWord_734156) baseStart_734156 baseEnd_734156 := by
    simpa [prefixWord, tailWord_734156, baseEnd_734156] using wordTrace_append hprefix tailTrace_734156
  have hstable : (prefixWord ++ tailWord_734156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734156).length < 2 ^ (prefixWord ++ tailWord_734156).sum := by decide
  have hdescent : baseEnd_734156 < baseStart_734156 := by decide
  rcases family_descends (prefixWord ++ tailWord_734156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734277 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_734277 : Nat := 118140960795 + 734277 * 2 ^ 59
def prefixEnd_734277 : Nat := 4983230072969 + 3 ^ 40 * 734277 * 2
def baseEnd_734277 : Nat := 167572015351790609582501

theorem tailTrace_734277 : CollatzResearch.WordTrace tailWord_734277 prefixEnd_734277 167572015351790609582501 := by
  unfold tailWord_734277
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781282360847308372745085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17854188240564872248496723 26781282360847308372745085)
  ·
    refine ⟨10042980885317740639779407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26781282360847308372745085 10042980885317740639779407)
    ·
      refine ⟨15064471327976610959669111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10042980885317740639779407 15064471327976610959669111)
      ·
        refine ⟨22596706991964916439503667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15064471327976610959669111 22596706991964916439503667)
        ·
          refine ⟨33895060487947374659255501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22596706991964916439503667 33895060487947374659255501)
          ·
            refine ⟨12710647682980265497220813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33895060487947374659255501 12710647682980265497220813)
            ·
              refine ⟨4766492881117599561457805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12710647682980265497220813 4766492881117599561457805)
              ·
                refine ⟨1787434830419099835546677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4766492881117599561457805 1787434830419099835546677)
                ·
                  refine ⟨167572015351790609582501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1787434830419099835546677 167572015351790609582501)
                  ·
                    rfl

theorem cell21_734277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_734277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734277 prefixEnd_734277 := by exact prefixLift 734277
  have htrace : WordTrace (prefixWord ++ tailWord_734277) baseStart_734277 baseEnd_734277 := by
    simpa [prefixWord, tailWord_734277, baseEnd_734277] using wordTrace_append hprefix tailTrace_734277
  have hstable : (prefixWord ++ tailWord_734277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734277).length < 2 ^ (prefixWord ++ tailWord_734277).sum := by decide
  have hdescent : baseEnd_734277 < baseStart_734277 := by decide
  rcases family_descends (prefixWord ++ tailWord_734277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734291 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_734291 : Nat := 118140960795 + 734291 * 2 ^ 59
def prefixEnd_734291 : Nat := 4983230072969 + 3 ^ 40 * 734291 * 2
def baseEnd_734291 : Nat := 167575210342529696349139

theorem tailTrace_734291 : CollatzResearch.WordTrace tailWord_734291 prefixEnd_734291 167575210342529696349139 := by
  unfold tailWord_734291
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781792982796588763754727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17854528655197725842503151 26781792982796588763754727)
  ·
    refine ⟨40172689474194883145632091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26781792982796588763754727 40172689474194883145632091)
    ·
      refine ⟨60259034211292324718448137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40172689474194883145632091 60259034211292324718448137)
      ·
        refine ⟨45194275658469243538836103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60259034211292324718448137 45194275658469243538836103)
        ·
          refine ⟨67791413487703865308254155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45194275658469243538836103 67791413487703865308254155)
          ·
            refine ⟨101687120231555797962381233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67791413487703865308254155 101687120231555797962381233)
            ·
              refine ⟨76265340173666848471785925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101687120231555797962381233 76265340173666848471785925)
              ·
                refine ⟨14299751282562534088459861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76265340173666848471785925 14299751282562534088459861)
                ·
                  refine ⟨167575210342529696349139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14299751282562534088459861 167575210342529696349139)
                  ·
                    rfl

theorem cell21_734291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_734291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734291 prefixEnd_734291 := by exact prefixLift 734291
  have htrace : WordTrace (prefixWord ++ tailWord_734291) baseStart_734291 baseEnd_734291 := by
    simpa [prefixWord, tailWord_734291, baseEnd_734291] using wordTrace_append hprefix tailTrace_734291
  have hstable : (prefixWord ++ tailWord_734291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734291).length < 2 ^ (prefixWord ++ tailWord_734291).sum := by decide
  have hdescent : baseEnd_734291 < baseStart_734291 := by decide
  rcases family_descends (prefixWord ++ tailWord_734291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734311 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 3]
def baseStart_734311 : Nat := 118140960795 + 734311 * 2 ^ 59
def prefixEnd_734311 : Nat := 4983230072969 + 3 ^ 40 * 734311 * 2
def baseEnd_734311 : Nat := 167579774615014106015765

theorem tailTrace_734311 : CollatzResearch.WordTrace tailWord_734311 prefixEnd_734311 167579774615014106015765 := by
  unfold tailWord_734311
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782522442724132179482787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17855014961816088119655191 26782522442724132179482787)
  ·
    refine ⟨40173783664086198269224181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26782522442724132179482787 40173783664086198269224181)
    ·
      refine ⟨3766292218508081087739767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40173783664086198269224181 3766292218508081087739767)
      ·
        refine ⟨5649438327762121631609651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766292218508081087739767 5649438327762121631609651)
        ·
          refine ⟨8474157491643182447414477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649438327762121631609651 8474157491643182447414477)
          ·
            refine ⟨3177809059366193417780429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8474157491643182447414477 3177809059366193417780429)
            ·
              refine ⟨1191678397262322531667661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3177809059366193417780429 1191678397262322531667661)
              ·
                refine ⟨446879398973370949375373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191678397262322531667661 446879398973370949375373)
                ·
                  refine ⟨167579774615014106015765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446879398973370949375373 167579774615014106015765)
                  ·
                    rfl

theorem cell21_734311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3].length) (baseStart_734311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734311 prefixEnd_734311 := by exact prefixLift 734311
  have htrace : WordTrace (prefixWord ++ tailWord_734311) baseStart_734311 baseEnd_734311 := by
    simpa [prefixWord, tailWord_734311, baseEnd_734311] using wordTrace_append hprefix tailTrace_734311
  have hstable : (prefixWord ++ tailWord_734311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734311).length < 2 ^ (prefixWord ++ tailWord_734311).sum := by decide
  have hdescent : baseEnd_734311 < baseStart_734311 := by decide
  rcases family_descends (prefixWord ++ tailWord_734311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734334 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_734334 : Nat := 118140960795 + 734334 * 2 ^ 59
def prefixEnd_734334 : Nat := 4983230072969 + 3 ^ 40 * 734334 * 2
def baseEnd_734334 : Nat := 167585023528371177132385

theorem tailTrace_734334 : CollatzResearch.WordTrace tailWord_734334 prefixEnd_734334 167585023528371177132385 := by
  unfold tailWord_734334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347920165205100888446257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17855574214427204738380037 3347920165205100888446257)
  ·
    refine ⟨2510940123903825666334693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3347920165205100888446257 2510940123903825666334693)
    ·
      refine ⟨470801273231967312437755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2510940123903825666334693 470801273231967312437755)
      ·
        refine ⟨706201909847950968656633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470801273231967312437755 706201909847950968656633)
        ·
          refine ⟨529651432385963226492475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706201909847950968656633 529651432385963226492475)
          ·
            refine ⟨794477148578944839738713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529651432385963226492475 794477148578944839738713)
            ·
              refine ⟨595857861434208629804035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794477148578944839738713 595857861434208629804035)
              ·
                refine ⟨893786792151312944706053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595857861434208629804035 893786792151312944706053)
                ·
                  refine ⟨167585023528371177132385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893786792151312944706053 167585023528371177132385)
                  ·
                    rfl

theorem cell21_734334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_734334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734334 prefixEnd_734334 := by exact prefixLift 734334
  have htrace : WordTrace (prefixWord ++ tailWord_734334) baseStart_734334 baseEnd_734334 := by
    simpa [prefixWord, tailWord_734334, baseEnd_734334] using wordTrace_append hprefix tailTrace_734334
  have hstable : (prefixWord ++ tailWord_734334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734334).length < 2 ^ (prefixWord ++ tailWord_734334).sum := by decide
  have hdescent : baseEnd_734334 < baseStart_734334 := by decide
  rcases family_descends (prefixWord ++ tailWord_734334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734387 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 3]
def baseStart_734387 : Nat := 118140960795 + 734387 * 2 ^ 59
def prefixEnd_734387 : Nat := 4983230072969 + 3 ^ 40 * 734387 * 2
def baseEnd_734387 : Nat := 167597118850454862748943

theorem tailTrace_734387 : CollatzResearch.WordTrace tailWord_734387 prefixEnd_734387 167597118850454862748943 := by
  unfold tailWord_734387
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785294390448797159249415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17856862926965864772832943 26785294390448797159249415)
  ·
    refine ⟨40177941585673195738874123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26785294390448797159249415 40177941585673195738874123)
    ·
      refine ⟨60266912378509793608311185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40177941585673195738874123 60266912378509793608311185)
      ·
        refine ⟨45200184283882345206233389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60266912378509793608311185 45200184283882345206233389)
        ·
          refine ⟨16950069106455879452337521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45200184283882345206233389 16950069106455879452337521)
          ·
            refine ⟨12712551829841909589253141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16950069106455879452337521 12712551829841909589253141)
            ·
              refine ⟨595900867023839511996241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12712551829841909589253141 595900867023839511996241)
              ·
                refine ⟨446925650267879633997181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595900867023839511996241 446925650267879633997181)
                ·
                  refine ⟨167597118850454862748943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446925650267879633997181 167597118850454862748943)
                  ·
                    rfl

theorem cell21_734387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3].length) (baseStart_734387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734387 prefixEnd_734387 := by exact prefixLift 734387
  have htrace : WordTrace (prefixWord ++ tailWord_734387) baseStart_734387 baseEnd_734387 := by
    simpa [prefixWord, tailWord_734387, baseEnd_734387] using wordTrace_append hprefix tailTrace_734387
  have hstable : (prefixWord ++ tailWord_734387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734387).length < 2 ^ (prefixWord ++ tailWord_734387).sum := by decide
  have hdescent : baseEnd_734387 < baseStart_734387 := by decide
  rcases family_descends (prefixWord ++ tailWord_734387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734390 : List Nat := [5, 1, 3, 2, 1, 2, 1, 6]
def baseStart_734390 : Nat := 118140960795 + 734390 * 2 ^ 59
def prefixEnd_734390 : Nat := 4983230072969 + 3 ^ 40 * 734390 * 2
def baseEnd_734390 : Nat := 55865934497109174732979

theorem tailTrace_734390 : CollatzResearch.WordTrace tailWord_734390 prefixEnd_734390 55865934497109174732979 := by
  unfold tailWord_734390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674087738089870541975539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17856935872958619114405749 1674087738089870541975539)
  ·
    refine ⟨2511131607134805812963309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674087738089870541975539 2511131607134805812963309)
    ·
      refine ⟨941674352675552179861241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2511131607134805812963309 941674352675552179861241)
      ·
        refine ⟨706255764506664134895931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 941674352675552179861241 706255764506664134895931)
        ·
          refine ⟨1059383646759996202343897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706255764506664134895931 1059383646759996202343897)
          ·
            refine ⟨794537735069997151757923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059383646759996202343897 794537735069997151757923)
            ·
              refine ⟨1191806602604995727636885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794537735069997151757923 1191806602604995727636885)
              ·
                refine ⟨55865934497109174732979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1191806602604995727636885 55865934497109174732979)
                ·
                  rfl

theorem cell21_734390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_734390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734390 prefixEnd_734390 := by exact prefixLift 734390
  have htrace : WordTrace (prefixWord ++ tailWord_734390) baseStart_734390 baseEnd_734390 := by
    simpa [prefixWord, tailWord_734390, baseEnd_734390] using wordTrace_append hprefix tailTrace_734390
  have hstable : (prefixWord ++ tailWord_734390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734390).length < 2 ^ (prefixWord ++ tailWord_734390).sum := by decide
  have hdescent : baseEnd_734390 < baseStart_734390 := by decide
  rcases family_descends (prefixWord ++ tailWord_734390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734466 : List Nat := [3, 4, 1, 1, 4, 1, 2, 5]
def baseStart_734466 : Nat := 118140960795 + 734466 * 2 ^ 59
def prefixEnd_734466 : Nat := 4983230072969 + 3 ^ 40 * 734466 * 2
def baseEnd_734466 : Nat := 55871715908922760310705

theorem tailTrace_734466 : CollatzResearch.WordTrace tailWord_734466 prefixEnd_734466 55871715908922760310705 := by
  unfold tailWord_734466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697043939290648412843813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17858783838108395767583501 6697043939290648412843813)
  ·
    refine ⟨1255695738616996577408215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6697043939290648412843813 1255695738616996577408215)
    ·
      refine ⟨1883543607925494866112323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1255695738616996577408215 1883543607925494866112323)
      ·
        refine ⟨2825315411888242299168485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883543607925494866112323 2825315411888242299168485)
        ·
          refine ⟨529746639729045431094091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2825315411888242299168485 529746639729045431094091)
          ·
            refine ⟨794619959593568146641137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529746639729045431094091 794619959593568146641137)
            ·
              refine ⟨595964969695176109980853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794619959593568146641137 595964969695176109980853)
              ·
                refine ⟨55871715908922760310705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 595964969695176109980853 55871715908922760310705)
                ·
                  rfl

theorem cell21_734466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_734466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734466 prefixEnd_734466 := by exact prefixLift 734466
  have htrace : WordTrace (prefixWord ++ tailWord_734466) baseStart_734466 baseEnd_734466 := by
    simpa [prefixWord, tailWord_734466, baseEnd_734466] using wordTrace_append hprefix tailTrace_734466
  have hstable : (prefixWord ++ tailWord_734466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734466).length < 2 ^ (prefixWord ++ tailWord_734466).sum := by decide
  have hdescent : baseEnd_734466 < baseStart_734466 := by decide
  rcases family_descends (prefixWord ++ tailWord_734466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734640 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_734640 : Nat := 118140960795 + 734640 * 2 ^ 59
def prefixEnd_734640 : Nat := 4983230072969 + 3 ^ 40 * 734640 * 2
def baseEnd_734640 : Nat := 167654856897382645031759

theorem tailTrace_734640 : CollatzResearch.WordTrace tailWord_734640 prefixEnd_734640 167654856897382645031759 := by
  unfold tailWord_734640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13397261029266110684104687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17863014705688147578806249 13397261029266110684104687)
  ·
    refine ⟨20095891543899166026157031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13397261029266110684104687 20095891543899166026157031)
    ·
      refine ⟨30143837315848749039235547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20095891543899166026157031 30143837315848749039235547)
      ·
        refine ⟨45215755973773123558853321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30143837315848749039235547 45215755973773123558853321)
        ·
          refine ⟨33911816980329842669139991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45215755973773123558853321 33911816980329842669139991)
          ·
            refine ⟨50867725470494764003709987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33911816980329842669139991 50867725470494764003709987)
            ·
              refine ⟨76301588205742146005564981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50867725470494764003709987 76301588205742146005564981)
              ·
                refine ⟨7153273894288326188021717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76301588205742146005564981 7153273894288326188021717)
                ·
                  refine ⟨167654856897382645031759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7153273894288326188021717 167654856897382645031759)
                  ·
                    rfl

theorem cell21_734640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_734640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734640 prefixEnd_734640 := by exact prefixLift 734640
  have htrace : WordTrace (prefixWord ++ tailWord_734640) baseStart_734640 baseEnd_734640 := by
    simpa [prefixWord, tailWord_734640, baseEnd_734640] using wordTrace_append hprefix tailTrace_734640
  have hstable : (prefixWord ++ tailWord_734640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734640).length < 2 ^ (prefixWord ++ tailWord_734640).sum := by decide
  have hdescent : baseEnd_734640 < baseStart_734640 := by decide
  rcases family_descends (prefixWord ++ tailWord_734640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734671 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_734671 : Nat := 118140960795 + 734671 * 2 ^ 59
def prefixEnd_734671 : Nat := 4983230072969 + 3 ^ 40 * 734671 * 2
def baseEnd_734671 : Nat := 167661931519733480015029

theorem tailTrace_734671 : CollatzResearch.WordTrace tailWord_734671 prefixEnd_734671 167661931519733480015029 := by
  unfold tailWord_734671
  simp only [CollatzResearch.WordTrace]
  refine ⟨26795652721419913662587867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17863768480946609108391911 26795652721419913662587867)
  ·
    refine ⟨40193479082129870493881801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26795652721419913662587867 40193479082129870493881801)
    ·
      refine ⟨30145109311597402870411351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40193479082129870493881801 30145109311597402870411351)
      ·
        refine ⟨45217663967396104305617027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30145109311597402870411351 45217663967396104305617027)
        ·
          refine ⟨67826495951094156458425541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45217663967396104305617027 67826495951094156458425541)
          ·
            refine ⟨12717467990830154335954789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67826495951094156458425541 12717467990830154335954789)
            ·
              refine ⟨2384525248280653937991523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12717467990830154335954789 2384525248280653937991523)
              ·
                refine ⟨3576787872420980906987285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384525248280653937991523 3576787872420980906987285)
                ·
                  refine ⟨167661931519733480015029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3576787872420980906987285 167661931519733480015029)
                  ·
                    rfl

theorem cell21_734671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_734671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734671 prefixEnd_734671 := by exact prefixLift 734671
  have htrace : WordTrace (prefixWord ++ tailWord_734671) baseStart_734671 baseEnd_734671 := by
    simpa [prefixWord, tailWord_734671, baseEnd_734671] using wordTrace_append hprefix tailTrace_734671
  have hstable : (prefixWord ++ tailWord_734671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734671).length < 2 ^ (prefixWord ++ tailWord_734671).sum := by decide
  have hdescent : baseEnd_734671 < baseStart_734671 := by decide
  rcases family_descends (prefixWord ++ tailWord_734671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734702 : List Nat := [4, 1, 2, 1, 2, 1, 1, 9]
def baseStart_734702 : Nat := 118140960795 + 734702 * 2 ^ 59
def prefixEnd_734702 : Nat := 4983230072969 + 3 ^ 40 * 734702 * 2
def baseEnd_734702 : Nat := 55889668714028104999433

theorem tailTrace_734702 : CollatzResearch.WordTrace tailWord_734702 prefixEnd_734702 55889668714028104999433 := by
  unfold tailWord_734702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349597923038450744620795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17864522256205070637977573 3349597923038450744620795)
  ·
    refine ⟨5024396884557676116931193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349597923038450744620795 5024396884557676116931193)
    ·
      refine ⟨3768297663418257087698395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5024396884557676116931193 3768297663418257087698395)
      ·
        refine ⟨5652446495127385631547593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768297663418257087698395 5652446495127385631547593)
        ·
          refine ⟨4239334871345539223660695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5652446495127385631547593 4239334871345539223660695)
          ·
            refine ⟨6359002307018308835491043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239334871345539223660695 6359002307018308835491043)
            ·
              refine ⟨9538503460527463253236565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359002307018308835491043 9538503460527463253236565)
              ·
                refine ⟨55889668714028104999433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9538503460527463253236565 55889668714028104999433)
                ·
                  rfl

theorem cell21_734702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_734702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734702 prefixEnd_734702 := by exact prefixLift 734702
  have htrace : WordTrace (prefixWord ++ tailWord_734702) baseStart_734702 baseEnd_734702 := by
    simpa [prefixWord, tailWord_734702, baseEnd_734702] using wordTrace_append hprefix tailTrace_734702
  have hstable : (prefixWord ++ tailWord_734702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734702).length < 2 ^ (prefixWord ++ tailWord_734702).sum := by decide
  have hdescent : baseEnd_734702 < baseStart_734702 := by decide
  rcases family_descends (prefixWord ++ tailWord_734702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734722 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_734722 : Nat := 118140960795 + 734722 * 2 ^ 59
def prefixEnd_734722 : Nat := 4983230072969 + 3 ^ 40 * 734722 * 2
def baseEnd_734722 : Nat := 167673570414568724664925

theorem tailTrace_734722 : CollatzResearch.WordTrace tailWord_734722 prefixEnd_734722 167673570414568724664925 := by
  unfold tailWord_734722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699378211058787343173605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17865008562823432915129613 6699378211058787343173605)
  ·
    refine ⟨1256133414573522626845051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6699378211058787343173605 1256133414573522626845051)
    ·
      refine ⟨1884200121860283940267577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256133414573522626845051 1884200121860283940267577)
      ·
        refine ⟨1413150091395212955200683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1884200121860283940267577 1413150091395212955200683)
        ·
          refine ⟨2119725137092819432801025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413150091395212955200683 2119725137092819432801025)
          ·
            refine ⟨1589793852819614574600769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119725137092819432801025 1589793852819614574600769)
            ·
              refine ⟨1192345389614710930950577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589793852819614574600769 1192345389614710930950577)
              ·
                refine ⟨894259042211033198212933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192345389614710930950577 894259042211033198212933)
                ·
                  refine ⟨167673570414568724664925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894259042211033198212933 167673570414568724664925)
                  ·
                    rfl

theorem cell21_734722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_734722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734722 prefixEnd_734722 := by exact prefixLift 734722
  have htrace : WordTrace (prefixWord ++ tailWord_734722) baseStart_734722 baseEnd_734722 := by
    simpa [prefixWord, tailWord_734722, baseEnd_734722] using wordTrace_append hprefix tailTrace_734722
  have hstable : (prefixWord ++ tailWord_734722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734722).length < 2 ^ (prefixWord ++ tailWord_734722).sum := by decide
  have hdescent : baseEnd_734722 < baseStart_734722 := by decide
  rcases family_descends (prefixWord ++ tailWord_734722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734812 : List Nat := [2, 2, 4, 1, 2, 3, 2, 5]
def baseStart_734812 : Nat := 118140960795 + 734812 * 2 ^ 59
def prefixEnd_734812 : Nat := 4983230072969 + 3 ^ 40 * 734812 * 2
def baseEnd_734812 : Nat := 55898036546916189388247

theorem tailTrace_734812 : CollatzResearch.WordTrace tailWord_734812 prefixEnd_734812 55898036546916189388247 := by
  unfold tailWord_734812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400397706954547371735345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17867196942606063162313793 13400397706954547371735345)
  ·
    refine ⟨10050298280215910528801509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13400397706954547371735345 10050298280215910528801509)
    ·
      refine ⟨1884430927540483224150283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10050298280215910528801509 1884430927540483224150283)
      ·
        refine ⟨2826646391310724836225425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884430927540483224150283 2826646391310724836225425)
        ·
          refine ⟨2119984793483043627169069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826646391310724836225425 2119984793483043627169069)
          ·
            refine ⟨794994297556141360188401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2119984793483043627169069 794994297556141360188401)
            ·
              refine ⟨596245723167106020141301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794994297556141360188401 596245723167106020141301)
              ·
                refine ⟨55898036546916189388247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596245723167106020141301 55898036546916189388247)
                ·
                  rfl

theorem cell21_734812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_734812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734812 prefixEnd_734812 := by exact prefixLift 734812
  have htrace : WordTrace (prefixWord ++ tailWord_734812) baseStart_734812 baseEnd_734812 := by
    simpa [prefixWord, tailWord_734812, baseEnd_734812] using wordTrace_append hprefix tailTrace_734812
  have hstable : (prefixWord ++ tailWord_734812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734812).length < 2 ^ (prefixWord ++ tailWord_734812).sum := by decide
  have hdescent : baseEnd_734812 < baseStart_734812 := by decide
  rcases family_descends (prefixWord ++ tailWord_734812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734823 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_734823 : Nat := 118140960795 + 734823 * 2 ^ 59
def prefixEnd_734823 : Nat := 4983230072969 + 3 ^ 40 * 734823 * 2
def baseEnd_734823 : Nat := 167696619990614993481385

theorem tailTrace_734823 : CollatzResearch.WordTrace tailWord_734823 prefixEnd_734823 167696619990614993481385 := by
  unfold tailWord_734823
  simp only [CollatzResearch.WordTrace]
  refine ⟨26801196616869243622121123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17867464411246162414747415 26801196616869243622121123)
  ·
    refine ⟨40201794925303865433181685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26801196616869243622121123 40201794925303865433181685)
    ·
      refine ⟨3768918274247237384360783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40201794925303865433181685 3768918274247237384360783)
      ·
        refine ⟨5653377411370856076541175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768918274247237384360783 5653377411370856076541175)
        ·
          refine ⟨8480066117056284114811763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653377411370856076541175 8480066117056284114811763)
          ·
            refine ⟨12720099175584426172217645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8480066117056284114811763 12720099175584426172217645)
            ·
              refine ⟨4770037190844159814581617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12720099175584426172217645 4770037190844159814581617)
              ·
                refine ⟨3577527893133119860936213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770037190844159814581617 3577527893133119860936213)
                ·
                  refine ⟨167696619990614993481385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3577527893133119860936213 167696619990614993481385)
                  ·
                    rfl

theorem cell21_734823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_734823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734823 prefixEnd_734823 := by exact prefixLift 734823
  have htrace : WordTrace (prefixWord ++ tailWord_734823) baseStart_734823 baseEnd_734823 := by
    simpa [prefixWord, tailWord_734823, baseEnd_734823] using wordTrace_append hprefix tailTrace_734823
  have hstable : (prefixWord ++ tailWord_734823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734823).length < 2 ^ (prefixWord ++ tailWord_734823).sum := by decide
  have hdescent : baseEnd_734823 < baseStart_734823 := by decide
  rcases family_descends (prefixWord ++ tailWord_734823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734888 : List Nat := [2, 1, 7, 1, 1, 9]
def baseStart_734888 : Nat := 118140960795 + 734888 * 2 ^ 59
def prefixEnd_734888 : Nat := 4983230072969 + 3 ^ 40 * 734888 * 2
def baseEnd_734888 : Nat := 6211535328747752773997

theorem tailTrace_734888 : CollatzResearch.WordTrace tailWord_734888 prefixEnd_734888 6211535328747752773997 := by
  unfold tailWord_734888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401783680816879861618659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17869044907755839815491545 13401783680816879861618659)
  ·
    refine ⟨20102675521225319792427989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13401783680816879861618659 20102675521225319792427989)
    ·
      refine ⟨471156457528718432635031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20102675521225319792427989 471156457528718432635031)
      ·
        refine ⟨706734686293077648952547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471156457528718432635031 706734686293077648952547)
        ·
          refine ⟨1060102029439616473428821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706734686293077648952547 1060102029439616473428821)
          ·
            refine ⟨6211535328747752773997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1060102029439616473428821 6211535328747752773997)
            ·
              rfl

theorem cell21_734888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 9].length) (baseStart_734888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734888 prefixEnd_734888 := by exact prefixLift 734888
  have htrace : WordTrace (prefixWord ++ tailWord_734888) baseStart_734888 baseEnd_734888 := by
    simpa [prefixWord, tailWord_734888, baseEnd_734888] using wordTrace_append hprefix tailTrace_734888
  have hstable : (prefixWord ++ tailWord_734888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734888).length < 2 ^ (prefixWord ++ tailWord_734888).sum := by decide
  have hdescent : baseEnd_734888 < baseStart_734888 := by decide
  rcases family_descends (prefixWord ++ tailWord_734888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734894 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_734894 : Nat := 118140960795 + 734894 * 2 ^ 59
def prefixEnd_734894 : Nat := 4983230072969 + 3 ^ 40 * 734894 * 2
def baseEnd_734894 : Nat := 167712823157934647797907

theorem tailTrace_734894 : CollatzResearch.WordTrace tailWord_734894 prefixEnd_734894 167712823157934647797907 := by
  unfold tailWord_734894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350473274951502843494467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17869190799741348498637157 3350473274951502843494467)
  ·
    refine ⟨5025709912427254265241701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3350473274951502843494467 5025709912427254265241701)
    ·
      refine ⟨942320608580110174732819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5025709912427254265241701 942320608580110174732819)
      ·
        refine ⟨1413480912870165262099229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942320608580110174732819 1413480912870165262099229)
        ·
          refine ⟨530055342326311973287211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1413480912870165262099229 530055342326311973287211)
          ·
            refine ⟨795083013489467959930817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530055342326311973287211 795083013489467959930817)
            ·
              refine ⟨596312260117100969948113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795083013489467959930817 596312260117100969948113)
              ·
                refine ⟨447234195087825727461085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596312260117100969948113 447234195087825727461085)
                ·
                  refine ⟨167712823157934647797907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447234195087825727461085 167712823157934647797907)
                  ·
                    rfl

theorem cell21_734894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_734894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734894 prefixEnd_734894 := by exact prefixLift 734894
  have htrace : WordTrace (prefixWord ++ tailWord_734894) baseStart_734894 baseEnd_734894 := by
    simpa [prefixWord, tailWord_734894, baseEnd_734894] using wordTrace_append hprefix tailTrace_734894
  have hstable : (prefixWord ++ tailWord_734894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734894).length < 2 ^ (prefixWord ++ tailWord_734894).sum := by decide
  have hdescent : baseEnd_734894 < baseStart_734894 := by decide
  rcases family_descends (prefixWord ++ tailWord_734894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734916 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_734916 : Nat := 118140960795 + 734916 * 2 ^ 59
def prefixEnd_734916 : Nat := 4983230072969 + 3 ^ 40 * 734916 * 2
def baseEnd_734916 : Nat := 167717843857667498431195

theorem tailTrace_734916 : CollatzResearch.WordTrace tailWord_734916 prefixEnd_734916 167717843857667498431195 := by
  unfold tailWord_734916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13402294302766160252628301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17869725737021547003504401 13402294302766160252628301)
  ·
    refine ⟨5025860363537310094735613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13402294302766160252628301 5025860363537310094735613)
    ·
      refine ⟨1884697636326491285525855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5025860363537310094735613 1884697636326491285525855)
      ·
        refine ⟨2827046454489736928288783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884697636326491285525855 2827046454489736928288783)
        ·
          refine ⟨4240569681734605392433175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827046454489736928288783 4240569681734605392433175)
          ·
            refine ⟨6360854522601908088649763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240569681734605392433175 6360854522601908088649763)
            ·
              refine ⟨9541281783902862132974645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360854522601908088649763 9541281783902862132974645)
              ·
                refine ⟨894495167240893324966373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9541281783902862132974645 894495167240893324966373)
                ·
                  refine ⟨167717843857667498431195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894495167240893324966373 167717843857667498431195)
                  ·
                    rfl

theorem cell21_734916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_734916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734916 prefixEnd_734916 := by exact prefixLift 734916
  have htrace : WordTrace (prefixWord ++ tailWord_734916) baseStart_734916 baseEnd_734916 := by
    simpa [prefixWord, tailWord_734916, baseEnd_734916] using wordTrace_append hprefix tailTrace_734916
  have hstable : (prefixWord ++ tailWord_734916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734916).length < 2 ^ (prefixWord ++ tailWord_734916).sum := by decide
  have hdescent : baseEnd_734916 < baseStart_734916 := by decide
  rcases family_descends (prefixWord ++ tailWord_734916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734961 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_734961 : Nat := 118140960795 + 734961 * 2 ^ 59
def prefixEnd_734961 : Nat := 4983230072969 + 3 ^ 40 * 734961 * 2
def baseEnd_734961 : Nat := 167728113470757420181103

theorem tailTrace_734961 : CollatzResearch.WordTrace tailWord_734961 prefixEnd_734961 167728113470757420181103 := by
  unfold tailWord_734961
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806229890369293190644737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17870819926912862127096491 26806229890369293190644737)
  ·
    refine ⟨20104672417776969892983553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26806229890369293190644737 20104672417776969892983553)
    ·
      refine ⟨15078504313332727419737665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20104672417776969892983553 15078504313332727419737665)
      ·
        refine ⟨11308878234999545564803249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15078504313332727419737665 11308878234999545564803249)
        ·
          refine ⟨8481658676249659173602437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11308878234999545564803249 8481658676249659173602437)
          ·
            refine ⟨1590311001796811095050457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8481658676249659173602437 1590311001796811095050457)
            ·
              refine ⟨1192733251347608321287843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590311001796811095050457 1192733251347608321287843)
              ·
                refine ⟨1789099877021412481931765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192733251347608321287843 1789099877021412481931765)
                ·
                  refine ⟨167728113470757420181103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789099877021412481931765 167728113470757420181103)
                  ·
                    rfl

theorem cell21_734961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_734961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734961 prefixEnd_734961 := by exact prefixLift 734961
  have htrace : WordTrace (prefixWord ++ tailWord_734961) baseStart_734961 baseEnd_734961 := by
    simpa [prefixWord, tailWord_734961, baseEnd_734961] using wordTrace_append hprefix tailTrace_734961
  have hstable : (prefixWord ++ tailWord_734961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734961).length < 2 ^ (prefixWord ++ tailWord_734961).sum := by decide
  have hdescent : baseEnd_734961 < baseStart_734961 := by decide
  rcases family_descends (prefixWord ++ tailWord_734961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734975 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_734975 : Nat := 118140960795 + 734975 * 2 ^ 59
def prefixEnd_734975 : Nat := 4983230072969 + 3 ^ 40 * 734975 * 2
def baseEnd_734975 : Nat := 167731308461496506947741

theorem tailTrace_734975 : CollatzResearch.WordTrace tailWord_734975 prefixEnd_734975 167731308461496506947741 := by
  unfold tailWord_734975
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806740512318573581654379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17871160341545715721102919 26806740512318573581654379)
  ·
    refine ⟨40210110768477860372481569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26806740512318573581654379 40210110768477860372481569)
    ·
      refine ⟨30157583076358395279361177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40210110768477860372481569 30157583076358395279361177)
      ·
        refine ⟨22618187307268796459520883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30157583076358395279361177 22618187307268796459520883)
        ·
          refine ⟨33927280960903194689281325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22618187307268796459520883 33927280960903194689281325)
          ·
            refine ⟨12722730360338698008480497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33927280960903194689281325 12722730360338698008480497)
            ·
              refine ⟨9542047770254023506360373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12722730360338698008480497 9542047770254023506360373)
              ·
                refine ⟨894566978461314703721285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9542047770254023506360373 894566978461314703721285)
                ·
                  refine ⟨167731308461496506947741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894566978461314703721285 167731308461496506947741)
                  ·
                    rfl

theorem cell21_734975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_734975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_734975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_734975 prefixEnd_734975 := by exact prefixLift 734975
  have htrace : WordTrace (prefixWord ++ tailWord_734975) baseStart_734975 baseEnd_734975 := by
    simpa [prefixWord, tailWord_734975, baseEnd_734975] using wordTrace_append hprefix tailTrace_734975
  have hstable : (prefixWord ++ tailWord_734975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734975).length < 2 ^ (prefixWord ++ tailWord_734975).sum := by decide
  have hdescent : baseEnd_734975 < baseStart_734975 := by decide
  rcases family_descends (prefixWord ++ tailWord_734975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735071 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 3]
def baseStart_735071 : Nat := 118140960795 + 735071 * 2 ^ 59
def prefixEnd_735071 : Nat := 4983230072969 + 3 ^ 40 * 735071 * 2
def baseEnd_735071 : Nat := 167753216969421673347545

theorem tailTrace_735071 : CollatzResearch.WordTrace tailWord_735071 prefixEnd_735071 167753216969421673347545 := by
  unfold tailWord_735071
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810241919970781977149067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17873494613313854651432711 26810241919970781977149067)
  ·
    refine ⟨40215362879956172965723601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26810241919970781977149067 40215362879956172965723601)
    ·
      refine ⟨30161522159967129724292701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40215362879956172965723601 30161522159967129724292701)
      ·
        refine ⟨11310570809987673646609763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30161522159967129724292701 11310570809987673646609763)
        ·
          refine ⟨16965856214981510469914645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310570809987673646609763 16965856214981510469914645)
          ·
            refine ⟨795274510077258303277249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16965856214981510469914645 795274510077258303277249)
            ·
              refine ⟨596455882557943727457937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795274510077258303277249 596455882557943727457937)
              ·
                refine ⟨447341911918457795593453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596455882557943727457937 447341911918457795593453)
                ·
                  refine ⟨167753216969421673347545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447341911918457795593453 167753216969421673347545)
                  ·
                    rfl

theorem cell21_735071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3].length) (baseStart_735071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735071 prefixEnd_735071 := by exact prefixLift 735071
  have htrace : WordTrace (prefixWord ++ tailWord_735071) baseStart_735071 baseEnd_735071 := by
    simpa [prefixWord, tailWord_735071, baseEnd_735071] using wordTrace_append hprefix tailTrace_735071
  have hstable : (prefixWord ++ tailWord_735071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735071).length < 2 ^ (prefixWord ++ tailWord_735071).sum := by decide
  have hdescent : baseEnd_735071 < baseStart_735071 := by decide
  rcases family_descends (prefixWord ++ tailWord_735071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735127 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_735127 : Nat := 118140960795 + 735127 * 2 ^ 59
def prefixEnd_735127 : Nat := 4983230072969 + 3 ^ 40 * 735127 * 2
def baseEnd_735127 : Nat := 167765996932378020414097

theorem tailTrace_735127 : CollatzResearch.WordTrace tailWord_735127 prefixEnd_735127 167765996932378020414097 := by
  unfold tailWord_735127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26812284407767903541187635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17874856271845269027458423 26812284407767903541187635)
  ·
    refine ⟨40218426611651855311781453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26812284407767903541187635 40218426611651855311781453)
    ·
      refine ⟨15081909979369445741918045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40218426611651855311781453 15081909979369445741918045)
      ·
        refine ⟨5655716242263542153219267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15081909979369445741918045 5655716242263542153219267)
        ·
          refine ⟨8483574363395313229828901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655716242263542153219267 8483574363395313229828901)
          ·
            refine ⟨1590670193136621230592919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8483574363395313229828901 1590670193136621230592919)
            ·
              refine ⟨2386005289704931845889379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590670193136621230592919 2386005289704931845889379)
              ·
                refine ⟨3579007934557397768834069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386005289704931845889379 3579007934557397768834069)
                ·
                  refine ⟨167765996932378020414097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3579007934557397768834069 167765996932378020414097)
                  ·
                    rfl

theorem cell21_735127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_735127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735127 prefixEnd_735127 := by exact prefixLift 735127
  have htrace : WordTrace (prefixWord ++ tailWord_735127) baseStart_735127 baseEnd_735127 := by
    simpa [prefixWord, tailWord_735127, baseEnd_735127] using wordTrace_append hprefix tailTrace_735127
  have hstable : (prefixWord ++ tailWord_735127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735127).length < 2 ^ (prefixWord ++ tailWord_735127).sum := by decide
  have hdescent : baseEnd_735127 < baseStart_735127 := by decide
  rcases family_descends (prefixWord ++ tailWord_735127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735130 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_735130 : Nat := 118140960795 + 735130 * 2 ^ 59
def prefixEnd_735130 : Nat := 4983230072969 + 3 ^ 40 * 735130 * 2
def baseEnd_735130 : Nat := 167766681573250681864091

theorem tailTrace_735130 : CollatzResearch.WordTrace tailWord_735130 prefixEnd_735130 167766681573250681864091 := by
  unfold tailWord_735130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703098456689258763386711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17874929217838023369031229 6703098456689258763386711)
  ·
    refine ⟨10054647685033888145080067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6703098456689258763386711 10054647685033888145080067)
    ·
      refine ⟨15081971527550832217620101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054647685033888145080067 15081971527550832217620101)
      ·
        refine ⟨2827869661415781040803769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15081971527550832217620101 2827869661415781040803769)
        ·
          refine ⟨2120902246061835780602827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827869661415781040803769 2120902246061835780602827)
          ·
            refine ⟨3181353369092753670904241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120902246061835780602827 3181353369092753670904241)
            ·
              refine ⟨2386015026819565253178181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181353369092753670904241 2386015026819565253178181)
              ·
                refine ⟨447377817528668484970909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2386015026819565253178181 447377817528668484970909)
                ·
                  refine ⟨167766681573250681864091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447377817528668484970909 167766681573250681864091)
                  ·
                    rfl

theorem cell21_735130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_735130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735130 prefixEnd_735130 := by exact prefixLift 735130
  have htrace : WordTrace (prefixWord ++ tailWord_735130) baseStart_735130 baseEnd_735130 := by
    simpa [prefixWord, tailWord_735130, baseEnd_735130] using wordTrace_append hprefix tailTrace_735130
  have hstable : (prefixWord ++ tailWord_735130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735130).length < 2 ^ (prefixWord ++ tailWord_735130).sum := by decide
  have hdescent : baseEnd_735130 < baseStart_735130 := by decide
  rcases family_descends (prefixWord ++ tailWord_735130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735150 : List Nat := [4, 1, 5, 1, 1, 2, 2, 5]
def baseStart_735150 : Nat := 118140960795 + 735150 * 2 ^ 59
def prefixEnd_735150 : Nat := 4983230072969 + 3 ^ 40 * 735150 * 2
def baseEnd_735150 : Nat := 55923748615245030510239

theorem tailTrace_735150 : CollatzResearch.WordTrace tailWord_735150 prefixEnd_735150 55923748615245030510239 := by
  unfold tailWord_735150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351640410835572308659363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17875415524456385646183269 3351640410835572308659363)
  ·
    refine ⟨5027460616253358462989045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351640410835572308659363 5027460616253358462989045)
    ·
      refine ⟨471324432773752355905223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5027460616253358462989045 471324432773752355905223)
      ·
        refine ⟨706986649160628533857835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471324432773752355905223 706986649160628533857835)
        ·
          refine ⟨1060479973740942800786753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706986649160628533857835 1060479973740942800786753)
          ·
            refine ⟨795359980305707100590065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060479973740942800786753 795359980305707100590065)
            ·
              refine ⟨596519985229280325442549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795359980305707100590065 596519985229280325442549)
              ·
                refine ⟨55923748615245030510239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596519985229280325442549 55923748615245030510239)
                ·
                  rfl

theorem cell21_735150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_735150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735150 prefixEnd_735150 := by exact prefixLift 735150
  have htrace : WordTrace (prefixWord ++ tailWord_735150) baseStart_735150 baseEnd_735150 := by
    simpa [prefixWord, tailWord_735150, baseEnd_735150] using wordTrace_append hprefix tailTrace_735150
  have hstable : (prefixWord ++ tailWord_735150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735150).length < 2 ^ (prefixWord ++ tailWord_735150).sum := by decide
  have hdescent : baseEnd_735150 < baseStart_735150 := by decide
  rcases family_descends (prefixWord ++ tailWord_735150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735164 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_735164 : Nat := 118140960795 + 735164 * 2 ^ 59
def prefixEnd_735164 : Nat := 4983230072969 + 3 ^ 40 * 735164 * 2
def baseEnd_735164 : Nat := 167774440836474178297355

theorem tailTrace_735164 : CollatzResearch.WordTrace tailWord_735164 prefixEnd_735164 167774440836474178297355 := by
  unfold tailWord_735164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406816954316929430142273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17875755939089239240189697 13406816954316929430142273)
  ·
    refine ⟨10055112715737697072606705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13406816954316929430142273 10055112715737697072606705)
    ·
      refine ⟨7541334536803272804455029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10055112715737697072606705 7541334536803272804455029)
      ·
        refine ⟨707000112825306825417659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7541334536803272804455029 707000112825306825417659)
        ·
          refine ⟨1060500169237960238126489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707000112825306825417659 1060500169237960238126489)
          ·
            refine ⟨795375126928470178594867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060500169237960238126489 795375126928470178594867)
            ·
              refine ⟨1193062690392705267892301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795375126928470178594867 1193062690392705267892301)
              ·
                refine ⟨447398508897264475459613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193062690392705267892301 447398508897264475459613)
                ·
                  refine ⟨167774440836474178297355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447398508897264475459613 167774440836474178297355)
                  ·
                    rfl

theorem cell21_735164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_735164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735164 prefixEnd_735164 := by exact prefixLift 735164
  have htrace : WordTrace (prefixWord ++ tailWord_735164) baseStart_735164 baseEnd_735164 := by
    simpa [prefixWord, tailWord_735164, baseEnd_735164] using wordTrace_append hprefix tailTrace_735164
  have hstable : (prefixWord ++ tailWord_735164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735164).length < 2 ^ (prefixWord ++ tailWord_735164).sum := by decide
  have hdescent : baseEnd_735164 < baseStart_735164 := by decide
  rcases family_descends (prefixWord ++ tailWord_735164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735189 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_735189 : Nat := 118140960795 + 735189 * 2 ^ 59
def prefixEnd_735189 : Nat := 4983230072969 + 3 ^ 40 * 735189 * 2
def baseEnd_735189 : Nat := 167780146177079690380637

theorem tailTrace_735189 : CollatzResearch.WordTrace tailWord_735189 prefixEnd_735189 167780146177079690380637 := by
  unfold tailWord_735189
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814545733543288129944621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17876363822362192086629747 26814545733543288129944621)
  ·
    refine ⟨10055454650078733048729233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26814545733543288129944621 10055454650078733048729233)
    ·
      refine ⟨7541590987559049786546925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10055454650078733048729233 7541590987559049786546925)
      ·
        refine ⟨2828096620334643669955097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7541590987559049786546925 2828096620334643669955097)
        ·
          refine ⟨2121072465250982752466323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828096620334643669955097 2121072465250982752466323)
          ·
            refine ⟨3181608697876474128699485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121072465250982752466323 3181608697876474128699485)
            ·
              refine ⟨1193103261703677798262307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3181608697876474128699485 1193103261703677798262307)
              ·
                refine ⟨1789654892555516697393461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193103261703677798262307 1789654892555516697393461)
                ·
                  refine ⟨167780146177079690380637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789654892555516697393461 167780146177079690380637)
                  ·
                    rfl

theorem cell21_735189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_735189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735189 prefixEnd_735189 := by exact prefixLift 735189
  have htrace : WordTrace (prefixWord ++ tailWord_735189) baseStart_735189 baseEnd_735189 := by
    simpa [prefixWord, tailWord_735189, baseEnd_735189] using wordTrace_append hprefix tailTrace_735189
  have hstable : (prefixWord ++ tailWord_735189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735189).length < 2 ^ (prefixWord ++ tailWord_735189).sum := by decide
  have hdescent : baseEnd_735189 < baseStart_735189 := by decide
  rcases family_descends (prefixWord ++ tailWord_735189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735265 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_735265 : Nat := 118140960795 + 735265 * 2 ^ 59
def prefixEnd_735265 : Nat := 4983230072969 + 3 ^ 40 * 735265 * 2
def baseEnd_735265 : Nat := 167797490412520447113815

theorem tailTrace_735265 : CollatzResearch.WordTrace tailWord_735265 prefixEnd_735265 167797490412520447113815 := by
  unfold tailWord_735265
  simp only [CollatzResearch.WordTrace]
  refine ⟨26817317681267953109711249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17878211787511968739807499 26817317681267953109711249)
  ·
    refine ⟨20112988260950964832283437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26817317681267953109711249 20112988260950964832283437)
    ·
      refine ⟨7542370597856611812106289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20112988260950964832283437 7542370597856611812106289)
      ·
        refine ⟨5656777948392458859079717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542370597856611812106289 5656777948392458859079717)
        ·
          refine ⟨1060645865323586036077447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5656777948392458859079717 1060645865323586036077447)
          ·
            refine ⟨1590968797985379054116171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060645865323586036077447 1590968797985379054116171)
            ·
              refine ⟨2386453196978068581174257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590968797985379054116171 2386453196978068581174257)
              ·
                refine ⟨1789839897733551435880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386453196978068581174257 1789839897733551435880693)
                ·
                  refine ⟨167797490412520447113815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789839897733551435880693 167797490412520447113815)
                  ·
                    rfl

theorem cell21_735265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_735265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735265 prefixEnd_735265 := by exact prefixLift 735265
  have htrace : WordTrace (prefixWord ++ tailWord_735265) baseStart_735265 baseEnd_735265 := by
    simpa [prefixWord, tailWord_735265, baseEnd_735265] using wordTrace_append hprefix tailTrace_735265
  have hstable : (prefixWord ++ tailWord_735265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735265).length < 2 ^ (prefixWord ++ tailWord_735265).sum := by decide
  have hdescent : baseEnd_735265 < baseStart_735265 := by decide
  rcases family_descends (prefixWord ++ tailWord_735265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735282 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_735282 : Nat := 118140960795 + 735282 * 2 ^ 59
def prefixEnd_735282 : Nat := 4983230072969 + 3 ^ 40 * 735282 * 2
def baseEnd_735282 : Nat := 167801370044132195330447

theorem tailTrace_735282 : CollatzResearch.WordTrace tailWord_735282 prefixEnd_735282 167801370044132195330447 := by
  unfold tailWord_735282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704484430551591253270025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17878625148137576675386733 6704484430551591253270025)
  ·
    refine ⟨5028363322913693439952519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6704484430551591253270025 5028363322913693439952519)
    ·
      refine ⟨7542544984370540159928779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028363322913693439952519 7542544984370540159928779)
      ·
        refine ⟨11313817476555810239893169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542544984370540159928779 11313817476555810239893169)
        ·
          refine ⟨8485363107416857679919877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11313817476555810239893169 8485363107416857679919877)
          ·
            refine ⟨1591005582640660814984977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8485363107416857679919877 1591005582640660814984977)
            ·
              refine ⟨1193254186980495611238733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591005582640660814984977 1193254186980495611238733)
              ·
                refine ⟨447470320117685854214525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193254186980495611238733 447470320117685854214525)
                ·
                  refine ⟨167801370044132195330447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447470320117685854214525 167801370044132195330447)
                  ·
                    rfl

theorem cell21_735282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_735282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735282 prefixEnd_735282 := by exact prefixLift 735282
  have htrace : WordTrace (prefixWord ++ tailWord_735282) baseStart_735282 baseEnd_735282 := by
    simpa [prefixWord, tailWord_735282, baseEnd_735282] using wordTrace_append hprefix tailTrace_735282
  have hstable : (prefixWord ++ tailWord_735282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735282).length < 2 ^ (prefixWord ++ tailWord_735282).sum := by decide
  have hdescent : baseEnd_735282 < baseStart_735282 := by decide
  rcases family_descends (prefixWord ++ tailWord_735282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735293 : List Nat := [1, 4, 1, 3, 1, 1, 10]
def baseStart_735293 : Nat := 118140960795 + 735293 * 2 ^ 59
def prefixEnd_735293 : Nat := 4983230072969 + 3 ^ 40 * 735293 * 2
def baseEnd_735293 : Nat := 18644875599333180071899

theorem tailTrace_735293 : CollatzResearch.WordTrace tailWord_735293 prefixEnd_735293 18644875599333180071899 := by
  unfold tailWord_735293
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818338925166513891730533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17878892616777675927820355 26818338925166513891730533)
  ·
    refine ⟨5028438548468721354699475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26818338925166513891730533 5028438548468721354699475)
    ·
      refine ⟨7542657822703082032049213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028438548468721354699475 7542657822703082032049213)
      ·
        refine ⟨2828496683513655762018455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7542657822703082032049213 2828496683513655762018455)
        ·
          refine ⟨4242745025270483643027683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828496683513655762018455 4242745025270483643027683)
          ·
            refine ⟨6364117537905725464541525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242745025270483643027683 6364117537905725464541525)
            ·
              refine ⟨18644875599333180071899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6364117537905725464541525 18644875599333180071899)
              ·
                rfl

theorem cell21_735293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 10].length) (baseStart_735293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735293 prefixEnd_735293 := by exact prefixLift 735293
  have htrace : WordTrace (prefixWord ++ tailWord_735293) baseStart_735293 baseEnd_735293 := by
    simpa [prefixWord, tailWord_735293, baseEnd_735293] using wordTrace_append hprefix tailTrace_735293
  have hstable : (prefixWord ++ tailWord_735293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735293).length < 2 ^ (prefixWord ++ tailWord_735293).sum := by decide
  have hdescent : baseEnd_735293 < baseStart_735293 := by decide
  rcases family_descends (prefixWord ++ tailWord_735293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735296 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_735296 : Nat := 118140960795 + 735296 * 2 ^ 59
def prefixEnd_735296 : Nat := 4983230072969 + 3 ^ 40 * 735296 * 2
def baseEnd_735296 : Nat := 167804565034871282097085

theorem tailTrace_735296 : CollatzResearch.WordTrace tailWord_735296 prefixEnd_735296 167804565034871282097085 := by
  unfold tailWord_735296
  simp only [CollatzResearch.WordTrace]
  refine ⟨13409224172077822702044871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17878965562770430269393161 13409224172077822702044871)
  ·
    refine ⟨20113836258116734053067307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13409224172077822702044871 20113836258116734053067307)
    ·
      refine ⟨30170754387175101079600961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20113836258116734053067307 30170754387175101079600961)
      ·
        refine ⟨22628065790381325809700721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30170754387175101079600961 22628065790381325809700721)
        ·
          refine ⟨16971049342785994357275541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22628065790381325809700721 16971049342785994357275541)
          ·
            refine ⟨795517937943093485497291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16971049342785994357275541 795517937943093485497291)
            ·
              refine ⟨1193276906914640228245937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795517937943093485497291 1193276906914640228245937)
              ·
                refine ⟨894957680185980171184453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193276906914640228245937 894957680185980171184453)
                ·
                  refine ⟨167804565034871282097085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894957680185980171184453 167804565034871282097085)
                  ·
                    rfl

theorem cell21_735296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_735296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735296 prefixEnd_735296 := by exact prefixLift 735296
  have htrace : WordTrace (prefixWord ++ tailWord_735296) baseStart_735296 baseEnd_735296 := by
    simpa [prefixWord, tailWord_735296, baseEnd_735296] using wordTrace_append hprefix tailTrace_735296
  have hstable : (prefixWord ++ tailWord_735296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735296).length < 2 ^ (prefixWord ++ tailWord_735296).sum := by decide
  have hdescent : baseEnd_735296 < baseStart_735296 := by decide
  rcases family_descends (prefixWord ++ tailWord_735296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735307 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_735307 : Nat := 118140960795 + 735307 * 2 ^ 59
def prefixEnd_735307 : Nat := 4983230072969 + 3 ^ 40 * 735307 * 2
def baseEnd_735307 : Nat := 167807075384737707413729

theorem tailTrace_735307 : CollatzResearch.WordTrace tailWord_735307 prefixEnd_735307 167807075384737707413729 := by
  unfold tailWord_735307
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818849547115794282740175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17879233031410529521826783 26818849547115794282740175)
  ·
    refine ⟨40228274320673691424110263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26818849547115794282740175 40228274320673691424110263)
    ·
      refine ⟨60342411481010537136165395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40228274320673691424110263 60342411481010537136165395)
      ·
        refine ⟨90513617221515805704248093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60342411481010537136165395 90513617221515805704248093)
        ·
          refine ⟨33942606458068427139093035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90513617221515805704248093 33942606458068427139093035)
          ·
            refine ⟨50913909687102640708639553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33942606458068427139093035 50913909687102640708639553)
            ·
              refine ⟨38185432265326980531479665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50913909687102640708639553 38185432265326980531479665)
              ·
                refine ⟨28639074198995235398609749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38185432265326980531479665 28639074198995235398609749)
                ·
                  refine ⟨167807075384737707413729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28639074198995235398609749 167807075384737707413729)
                  ·
                    rfl

theorem cell21_735307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_735307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735307 prefixEnd_735307 := by exact prefixLift 735307
  have htrace : WordTrace (prefixWord ++ tailWord_735307) baseStart_735307 baseEnd_735307 := by
    simpa [prefixWord, tailWord_735307, baseEnd_735307] using wordTrace_append hprefix tailTrace_735307
  have hstable : (prefixWord ++ tailWord_735307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735307).length < 2 ^ (prefixWord ++ tailWord_735307).sum := by decide
  have hdescent : baseEnd_735307 < baseStart_735307 := by decide
  rcases family_descends (prefixWord ++ tailWord_735307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735369 : List Nat := [1, 2, 1, 1, 4, 2, 4, 6]
def baseStart_735369 : Nat := 118140960795 + 735369 * 2 ^ 59
def prefixEnd_735369 : Nat := 4983230072969 + 3 ^ 40 * 735369 * 2
def baseEnd_735369 : Nat := 55940408209813125793423

theorem tailTrace_735369 : CollatzResearch.WordTrace tailWord_735369 prefixEnd_735369 55940408209813125793423 := by
  unfold tailWord_735369
  simp only [CollatzResearch.WordTrace]
  refine ⟨26821110872891178871497161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17880740581927452580998107 26821110872891178871497161)
  ·
    refine ⟨20115833154668384153622871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26821110872891178871497161 20115833154668384153622871)
    ·
      refine ⟨30173749732002576230434307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20115833154668384153622871 30173749732002576230434307)
      ·
        refine ⟨45260624598003864345651461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30173749732002576230434307 45260624598003864345651461)
        ·
          refine ⟨8486367112125724564809649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45260624598003864345651461 8486367112125724564809649)
          ·
            refine ⟨6364775334094293423607237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8486367112125724564809649 6364775334094293423607237)
            ·
              refine ⟨1193395375142680016926357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6364775334094293423607237 1193395375142680016926357)
              ·
                refine ⟨55940408209813125793423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1193395375142680016926357 55940408209813125793423)
                ·
                  rfl

theorem cell21_735369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_735369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735369 prefixEnd_735369 := by exact prefixLift 735369
  have htrace : WordTrace (prefixWord ++ tailWord_735369) baseStart_735369 baseEnd_735369 := by
    simpa [prefixWord, tailWord_735369, baseEnd_735369] using wordTrace_append hprefix tailTrace_735369
  have hstable : (prefixWord ++ tailWord_735369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735369).length < 2 ^ (prefixWord ++ tailWord_735369).sum := by decide
  have hdescent : baseEnd_735369 < baseStart_735369 := by decide
  rcases family_descends (prefixWord ++ tailWord_735369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735406 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_735406 : Nat := 118140960795 + 735406 * 2 ^ 59
def prefixEnd_735406 : Nat := 4983230072969 + 3 ^ 40 * 735406 * 2
def baseEnd_735406 : Nat := 167829668533535535263527

theorem tailTrace_735406 : CollatzResearch.WordTrace tailWord_735406 prefixEnd_735406 167829668533535535263527 := by
  unfold tailWord_735406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352807546719641773824259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17881640249171422793729381 3352807546719641773824259)
  ·
    refine ⟨5029211320079462660736389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352807546719641773824259 5029211320079462660736389)
    ·
      refine ⟨942977122514899248888073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5029211320079462660736389 942977122514899248888073)
      ·
        refine ⟨707232841886174436666055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942977122514899248888073 707232841886174436666055)
        ·
          refine ⟨1060849262829261654999083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707232841886174436666055 1060849262829261654999083)
          ·
            refine ⟨1591273894243892482498625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060849262829261654999083 1591273894243892482498625)
            ·
              refine ⟨1193455420682919361873969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591273894243892482498625 1193455420682919361873969)
              ·
                refine ⟨895091565512189521405477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193455420682919361873969 895091565512189521405477)
                ·
                  refine ⟨167829668533535535263527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895091565512189521405477 167829668533535535263527)
                  ·
                    rfl

theorem cell21_735406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_735406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735406 prefixEnd_735406 := by exact prefixLift 735406
  have htrace : WordTrace (prefixWord ++ tailWord_735406) baseStart_735406 baseEnd_735406 := by
    simpa [prefixWord, tailWord_735406, baseEnd_735406] using wordTrace_append hprefix tailTrace_735406
  have hstable : (prefixWord ++ tailWord_735406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735406).length < 2 ^ (prefixWord ++ tailWord_735406).sum := by decide
  have hdescent : baseEnd_735406 < baseStart_735406 := by decide
  rcases family_descends (prefixWord ++ tailWord_735406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735417 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 3]
def baseStart_735417 : Nat := 118140960795 + 735417 * 2 ^ 59
def prefixEnd_735417 : Nat := 4983230072969 + 3 ^ 40 * 735417 * 2
def baseEnd_735417 : Nat := 167832178883401960580171

theorem tailTrace_735417 : CollatzResearch.WordTrace tailWord_735417 prefixEnd_735417 167832178883401960580171 := by
  unfold tailWord_735417
  simp only [CollatzResearch.WordTrace]
  refine ⟨26822861576717283069244505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17881907717811522046163003 26822861576717283069244505)
  ·
    refine ⟨20117146182537962301933379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26822861576717283069244505 20117146182537962301933379)
    ·
      refine ⟨30175719273806943452900069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20117146182537962301933379 30175719273806943452900069)
      ·
        refine ⟨5657947363838801897418763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30175719273806943452900069 5657947363838801897418763)
        ·
          refine ⟨8486921045758202846128145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657947363838801897418763 8486921045758202846128145)
          ·
            refine ⟨6365190784318652134596109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8486921045758202846128145 6365190784318652134596109)
            ·
              refine ⟨2386946544119494550473541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6365190784318652134596109 2386946544119494550473541)
              ·
                refine ⟨447552477022405228213789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2386946544119494550473541 447552477022405228213789)
                ·
                  refine ⟨167832178883401960580171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447552477022405228213789 167832178883401960580171)
                  ·
                    rfl

theorem cell21_735417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_735417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735417 prefixEnd_735417 := by exact prefixLift 735417
  have htrace : WordTrace (prefixWord ++ tailWord_735417) baseStart_735417 baseEnd_735417 := by
    simpa [prefixWord, tailWord_735417, baseEnd_735417] using wordTrace_append hprefix tailTrace_735417
  have hstable : (prefixWord ++ tailWord_735417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735417).length < 2 ^ (prefixWord ++ tailWord_735417).sum := by decide
  have hdescent : baseEnd_735417 < baseStart_735417 := by decide
  rcases family_descends (prefixWord ++ tailWord_735417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735538 : List Nat := [3, 2, 1, 1, 5, 1, 2, 6]
def baseStart_735538 : Nat := 118140960795 + 735538 * 2 ^ 59
def prefixEnd_735538 : Nat := 4983230072969 + 3 ^ 40 * 735538 * 2
def baseEnd_735538 : Nat := 55953264243977546354419

theorem tailTrace_735538 : CollatzResearch.WordTrace tailWord_735538 prefixEnd_735538 55953264243977546354419 := by
  unfold tailWord_735538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706818702319730183599817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17884849872852613822932845 6706818702319730183599817)
  ·
    refine ⟨5030114026739797637699863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6706818702319730183599817 5030114026739797637699863)
    ·
      refine ⟨7545171040109696456549795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030114026739797637699863 7545171040109696456549795)
      ·
        refine ⟨11317756560164544684824693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7545171040109696456549795 11317756560164544684824693)
        ·
          refine ⟨1061039677515426064202315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11317756560164544684824693 1061039677515426064202315)
          ·
            refine ⟨1591559516273139096303473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061039677515426064202315 1591559516273139096303473)
            ·
              refine ⟨1193669637204854322227605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591559516273139096303473 1193669637204854322227605)
              ·
                refine ⟨55953264243977546354419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1193669637204854322227605 55953264243977546354419)
                ·
                  rfl

theorem cell21_735538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_735538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735538 prefixEnd_735538 := by exact prefixLift 735538
  have htrace : WordTrace (prefixWord ++ tailWord_735538) baseStart_735538 baseEnd_735538 := by
    simpa [prefixWord, tailWord_735538, baseEnd_735538] using wordTrace_append hprefix tailTrace_735538
  have hstable : (prefixWord ++ tailWord_735538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735538).length < 2 ^ (prefixWord ++ tailWord_735538).sum := by decide
  have hdescent : baseEnd_735538 < baseStart_735538 := by decide
  rcases family_descends (prefixWord ++ tailWord_735538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735566 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_735566 : Nat := 118140960795 + 735566 * 2 ^ 59
def prefixEnd_735566 : Nat := 4983230072969 + 3 ^ 40 * 735566 * 2
def baseEnd_735566 : Nat := 167866182713410812596533

theorem tailTrace_735566 : CollatzResearch.WordTrace tailWord_735566 prefixEnd_735566 167866182713410812596533 := by
  unfold tailWord_735566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353537006647185189552319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17885530702118321010945701 3353537006647185189552319)
  ·
    refine ⟨5030305509970777784328479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353537006647185189552319 5030305509970777784328479)
    ·
      refine ⟨7545458264956166676492719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030305509970777784328479 7545458264956166676492719)
      ·
        refine ⟨11318187397434250014739079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7545458264956166676492719 11318187397434250014739079)
        ·
          refine ⟨16977281096151375022108619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11318187397434250014739079 16977281096151375022108619)
          ·
            refine ⟨25465921644227062533162929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16977281096151375022108619 25465921644227062533162929)
            ·
              refine ⟨19099441233170296899872197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25465921644227062533162929 19099441233170296899872197)
              ·
                refine ⟨3581145231219430668726037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19099441233170296899872197 3581145231219430668726037)
                ·
                  refine ⟨167866182713410812596533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3581145231219430668726037 167866182713410812596533)
                  ·
                    rfl

theorem cell21_735566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_735566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735566 prefixEnd_735566 := by exact prefixLift 735566
  have htrace : WordTrace (prefixWord ++ tailWord_735566) baseStart_735566 baseEnd_735566 := by
    simpa [prefixWord, tailWord_735566, baseEnd_735566] using wordTrace_append hprefix tailTrace_735566
  have hstable : (prefixWord ++ tailWord_735566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735566).length < 2 ^ (prefixWord ++ tailWord_735566).sum := by decide
  have hdescent : baseEnd_735566 < baseStart_735566 := by decide
  rcases family_descends (prefixWord ++ tailWord_735566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735586 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_735586 : Nat := 118140960795 + 735586 * 2 ^ 59
def prefixEnd_735586 : Nat := 4983230072969 + 3 ^ 40 * 735586 * 2
def baseEnd_735586 : Nat := 167870746985895222263159

theorem tailTrace_735586 : CollatzResearch.WordTrace tailWord_735586 prefixEnd_735586 167870746985895222263159 := by
  unfold tailWord_735586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6707256378276256233036653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17886017008736683288097741 6707256378276256233036653)
  ·
    refine ⟨2515221141853596087388745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6707256378276256233036653 2515221141853596087388745)
    ·
      refine ⟨1886415856390197065541559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515221141853596087388745 1886415856390197065541559)
      ·
        refine ⟨2829623784585295598312339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886415856390197065541559 2829623784585295598312339)
        ·
          refine ⟨4244435676877943397468509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829623784585295598312339 4244435676877943397468509)
          ·
            refine ⟨1591663378829228774050691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4244435676877943397468509 1591663378829228774050691)
            ·
              refine ⟨2387495068243843161076037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591663378829228774050691 2387495068243843161076037)
              ·
                refine ⟨447655325295720592701757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2387495068243843161076037 447655325295720592701757)
                ·
                  refine ⟨167870746985895222263159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447655325295720592701757 167870746985895222263159)
                  ·
                    rfl

theorem cell21_735586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_735586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735586 prefixEnd_735586 := by exact prefixLift 735586
  have htrace : WordTrace (prefixWord ++ tailWord_735586) baseStart_735586 baseEnd_735586 := by
    simpa [prefixWord, tailWord_735586, baseEnd_735586] using wordTrace_append hprefix tailTrace_735586
  have hstable : (prefixWord ++ tailWord_735586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735586).length < 2 ^ (prefixWord ++ tailWord_735586).sum := by decide
  have hdescent : baseEnd_735586 < baseStart_735586 := by decide
  rcases family_descends (prefixWord ++ tailWord_735586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735611 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_735611 : Nat := 118140960795 + 735611 * 2 ^ 59
def prefixEnd_735611 : Nat := 4983230072969 + 3 ^ 40 * 735611 * 2
def baseEnd_735611 : Nat := 167876452326500734346441

theorem tailTrace_735611 : CollatzResearch.WordTrace tailWord_735611 prefixEnd_735611 167876452326500734346441 := by
  unfold tailWord_735611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829937338014454201806687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17886624892009636134537791 26829937338014454201806687)
  ·
    refine ⟨40244906007021681302710031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26829937338014454201806687 40244906007021681302710031)
    ·
      refine ⟨60367359010532521954065047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40244906007021681302710031 60367359010532521954065047)
      ·
        refine ⟨90551038515798782931097571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60367359010532521954065047 90551038515798782931097571)
        ·
          refine ⟨135826557773698174396646357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90551038515798782931097571 135826557773698174396646357)
          ·
            refine ⟨3183434947821050962421399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135826557773698174396646357 3183434947821050962421399)
            ·
              refine ⟨4775152421731576443632099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183434947821050962421399 4775152421731576443632099)
              ·
                refine ⟨7162728632597364665448149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775152421731576443632099 7162728632597364665448149)
                ·
                  refine ⟨167876452326500734346441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7162728632597364665448149 167876452326500734346441)
                  ·
                    rfl

theorem cell21_735611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_735611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735611 prefixEnd_735611 := by exact prefixLift 735611
  have htrace : WordTrace (prefixWord ++ tailWord_735611) baseStart_735611 baseEnd_735611 := by
    simpa [prefixWord, tailWord_735611, baseEnd_735611] using wordTrace_append hprefix tailTrace_735611
  have hstable : (prefixWord ++ tailWord_735611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735611).length < 2 ^ (prefixWord ++ tailWord_735611).sum := by decide
  have hdescent : baseEnd_735611 < baseStart_735611 := by decide
  rcases family_descends (prefixWord ++ tailWord_735611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735645 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_735645 : Nat := 118140960795 + 735645 * 2 ^ 59
def prefixEnd_735645 : Nat := 4983230072969 + 3 ^ 40 * 735645 * 2
def baseEnd_735645 : Nat := 167884211589724230779705

theorem tailTrace_735645 : CollatzResearch.WordTrace tailWord_735645 prefixEnd_735645 167884211589724230779705 := by
  unfold tailWord_735645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26831177419891278008544389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17887451613260852005696259 26831177419891278008544389)
  ·
    refine ⟨5030845766229614626602073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26831177419891278008544389 5030845766229614626602073)
    ·
      refine ⟨3773134324672210969951555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5030845766229614626602073 3773134324672210969951555)
      ·
        refine ⟨5659701487008316454927333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773134324672210969951555 5659701487008316454927333)
        ·
          refine ⟨1061194028814059335298875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5659701487008316454927333 1061194028814059335298875)
          ·
            refine ⟨1591791043221089002948313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061194028814059335298875 1591791043221089002948313)
            ·
              refine ⟨1193843282415816752211235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591791043221089002948313 1193843282415816752211235)
              ·
                refine ⟨1790764923623725128316853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193843282415816752211235 1790764923623725128316853)
                ·
                  refine ⟨167884211589724230779705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1790764923623725128316853 167884211589724230779705)
                  ·
                    rfl

theorem cell21_735645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_735645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735645 prefixEnd_735645 := by exact prefixLift 735645
  have htrace : WordTrace (prefixWord ++ tailWord_735645) baseStart_735645 baseEnd_735645 := by
    simpa [prefixWord, tailWord_735645, baseEnd_735645] using wordTrace_append hprefix tailTrace_735645
  have hstable : (prefixWord ++ tailWord_735645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735645).length < 2 ^ (prefixWord ++ tailWord_735645).sum := by decide
  have hdescent : baseEnd_735645 < baseStart_735645 := by decide
  rcases family_descends (prefixWord ++ tailWord_735645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735673 : List Nat := [1, 2, 1, 4, 3, 2, 1, 7]
def baseStart_735673 : Nat := 118140960795 + 735673 * 2 ^ 59
def prefixEnd_735673 : Nat := 4983230072969 + 3 ^ 40 * 735673 * 2
def baseEnd_735673 : Nat := 55963533857067468104327

theorem tailTrace_735673 : CollatzResearch.WordTrace tailWord_735673 prefixEnd_735673 55963533857067468104327 := by
  unfold tailWord_735673
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832198663789838790563673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17888132442526559193709115 26832198663789838790563673)
  ·
    refine ⟨20124148997842379092922755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26832198663789838790563673 20124148997842379092922755)
    ·
      refine ⟨30186223496763568639384133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20124148997842379092922755 30186223496763568639384133)
      ·
        refine ⟨5659916905643169119884525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30186223496763568639384133 5659916905643169119884525)
        ·
          refine ⟨2122468839616188419956697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5659916905643169119884525 2122468839616188419956697)
          ·
            refine ⟨1591851629712141314967523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122468839616188419956697 1591851629712141314967523)
            ·
              refine ⟨2387777444568211972451285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591851629712141314967523 2387777444568211972451285)
              ·
                refine ⟨55963533857067468104327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2387777444568211972451285 55963533857067468104327)
                ·
                  rfl

theorem cell21_735673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_735673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735673 prefixEnd_735673 := by exact prefixLift 735673
  have htrace : WordTrace (prefixWord ++ tailWord_735673) baseStart_735673 baseEnd_735673 := by
    simpa [prefixWord, tailWord_735673, baseEnd_735673] using wordTrace_append hprefix tailTrace_735673
  have hstable : (prefixWord ++ tailWord_735673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735673).length < 2 ^ (prefixWord ++ tailWord_735673).sum := by decide
  have hdescent : baseEnd_735673 < baseStart_735673 := by decide
  rcases family_descends (prefixWord ++ tailWord_735673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735763 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_735763 : Nat := 118140960795 + 735763 * 2 ^ 59
def prefixEnd_735763 : Nat := 4983230072969 + 3 ^ 40 * 735763 * 2
def baseEnd_735763 : Nat := 167911140797382247812797

theorem tailTrace_735763 : CollatzResearch.WordTrace tailWord_735763 prefixEnd_735763 167911140797382247812797 := by
  unfold tailWord_735763
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835481233463784161339943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17890320822309189440893295 26835481233463784161339943)
  ·
    refine ⟨40253221850195676242009915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835481233463784161339943 40253221850195676242009915)
    ·
      refine ⟨60379832775293514363014873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40253221850195676242009915 60379832775293514363014873)
      ·
        refine ⟨45284874581470135772261155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60379832775293514363014873 45284874581470135772261155)
        ·
          refine ⟨67927311872205203658391733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45284874581470135772261155 67927311872205203658391733)
          ·
            refine ⟨6368185488019237842974225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67927311872205203658391733 6368185488019237842974225)
            ·
              refine ⟨4776139116014428382230669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6368185488019237842974225 4776139116014428382230669)
              ·
                refine ⟨1791052168505410643336501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4776139116014428382230669 1791052168505410643336501)
                ·
                  refine ⟨167911140797382247812797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791052168505410643336501 167911140797382247812797)
                  ·
                    rfl

theorem cell21_735763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_735763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735763 prefixEnd_735763 := by exact prefixLift 735763
  have htrace : WordTrace (prefixWord ++ tailWord_735763) baseStart_735763 baseEnd_735763 := by
    simpa [prefixWord, tailWord_735763, baseEnd_735763] using wordTrace_append hprefix tailTrace_735763
  have hstable : (prefixWord ++ tailWord_735763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735763).length < 2 ^ (prefixWord ++ tailWord_735763).sum := by decide
  have hdescent : baseEnd_735763 < baseStart_735763 := by decide
  rcases family_descends (prefixWord ++ tailWord_735763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735797 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 3]
def baseStart_735797 : Nat := 118140960795 + 735797 * 2 ^ 59
def prefixEnd_735797 : Nat := 4983230072969 + 3 ^ 40 * 735797 * 2
def baseEnd_735797 : Nat := 167918900060605744246061

theorem tailTrace_735797 : CollatzResearch.WordTrace tailWord_735797 prefixEnd_735797 167918900060605744246061 := by
  unfold tailWord_735797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26836721315340607968077645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17891147543560405312051763 26836721315340607968077645)
  ·
    refine ⟨10063770493252727988029117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26836721315340607968077645 10063770493252727988029117)
    ·
      refine ⟨3773913934969772995510919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10063770493252727988029117 3773913934969772995510919)
      ·
        refine ⟨5660870902454659493266379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773913934969772995510919 5660870902454659493266379)
        ·
          refine ⟨8491306353681989239899569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660870902454659493266379 8491306353681989239899569)
          ·
            refine ⟨6368479765261491929924677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491306353681989239899569 6368479765261491929924677)
            ·
              refine ⟨1194089955986529736860877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6368479765261491929924677 1194089955986529736860877)
              ·
                refine ⟨447783733494948651322829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194089955986529736860877 447783733494948651322829)
                ·
                  refine ⟨167918900060605744246061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447783733494948651322829 167918900060605744246061)
                  ·
                    rfl

theorem cell21_735797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_735797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735797 prefixEnd_735797 := by exact prefixLift 735797
  have htrace : WordTrace (prefixWord ++ tailWord_735797) baseStart_735797 baseEnd_735797 := by
    simpa [prefixWord, tailWord_735797, baseEnd_735797] using wordTrace_append hprefix tailTrace_735797
  have hstable : (prefixWord ++ tailWord_735797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735797).length < 2 ^ (prefixWord ++ tailWord_735797).sum := by decide
  have hdescent : baseEnd_735797 < baseStart_735797 := by decide
  rcases family_descends (prefixWord ++ tailWord_735797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735814 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_735814 : Nat := 118140960795 + 735814 * 2 ^ 59
def prefixEnd_735814 : Nat := 4983230072969 + 3 ^ 40 * 735814 * 2
def baseEnd_735814 : Nat := 167922779692217492462693

theorem tailTrace_735814 : CollatzResearch.WordTrace tailWord_735814 prefixEnd_735814 167922779692217492462693 := by
  unfold tailWord_735814
  simp only [CollatzResearch.WordTrace]
  refine ⟨838666917383719370982703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17891560904186013247630997 838666917383719370982703)
  ·
    refine ⟨1258000376075579056474055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 838666917383719370982703 1258000376075579056474055)
    ·
      refine ⟨1887000564113368584711083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258000376075579056474055 1887000564113368584711083)
      ·
        refine ⟨2830500846170052877066625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887000564113368584711083 2830500846170052877066625)
        ·
          refine ⟨2122875634627539657799969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2830500846170052877066625 2122875634627539657799969)
          ·
            refine ⟨1592156725970654743349977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122875634627539657799969 1592156725970654743349977)
            ·
              refine ⟨1194117544477991057512483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592156725970654743349977 1194117544477991057512483)
              ·
                refine ⟨1791176316716986586268725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194117544477991057512483 1791176316716986586268725)
                ·
                  refine ⟨167922779692217492462693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791176316716986586268725 167922779692217492462693)
                  ·
                    rfl

theorem cell21_735814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_735814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735814 prefixEnd_735814 := by exact prefixLift 735814
  have htrace : WordTrace (prefixWord ++ tailWord_735814) baseStart_735814 baseEnd_735814 := by
    simpa [prefixWord, tailWord_735814, baseEnd_735814] using wordTrace_append hprefix tailTrace_735814
  have hstable : (prefixWord ++ tailWord_735814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735814).length < 2 ^ (prefixWord ++ tailWord_735814).sum := by decide
  have hdescent : baseEnd_735814 < baseStart_735814 := by decide
  rcases family_descends (prefixWord ++ tailWord_735814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735828 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_735828 : Nat := 118140960795 + 735828 * 2 ^ 59
def prefixEnd_735828 : Nat := 4983230072969 + 3 ^ 40 * 735828 * 2
def baseEnd_735828 : Nat := 167925974682956579229331

theorem tailTrace_735828 : CollatzResearch.WordTrace tailWord_735828 prefixEnd_735828 167925974682956579229331 := by
  unfold tailWord_735828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418925989114150131228069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17891901318818866841637425 13418925989114150131228069)
  ·
    refine ⟨2516048622958903149605263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13418925989114150131228069 2516048622958903149605263)
    ·
      refine ⟨3774072934438354724407895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516048622958903149605263 3774072934438354724407895)
      ·
        refine ⟨5661109401657532086611843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774072934438354724407895 5661109401657532086611843)
        ·
          refine ⟨8491664102486298129917765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661109401657532086611843 8491664102486298129917765)
          ·
            refine ⟨1592187019216180899359581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8491664102486298129917765 1592187019216180899359581)
            ·
              refine ⟨597070132206067837259843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1592187019216180899359581 597070132206067837259843)
              ·
                refine ⟨895605198309101755889765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597070132206067837259843 895605198309101755889765)
                ·
                  refine ⟨167925974682956579229331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895605198309101755889765 167925974682956579229331)
                  ·
                    rfl

theorem cell21_735828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_735828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_735828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_735828 prefixEnd_735828 := by exact prefixLift 735828
  have htrace : WordTrace (prefixWord ++ tailWord_735828) baseStart_735828 baseEnd_735828 := by
    simpa [prefixWord, tailWord_735828, baseEnd_735828] using wordTrace_append hprefix tailTrace_735828
  have hstable : (prefixWord ++ tailWord_735828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735828).length < 2 ^ (prefixWord ++ tailWord_735828).sum := by decide
  have hdescent : baseEnd_735828 < baseStart_735828 := by decide
  rcases family_descends (prefixWord ++ tailWord_735828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736042 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_736042 : Nat := 118140960795 + 736042 * 2 ^ 59
def prefixEnd_736042 : Nat := 4983230072969 + 3 ^ 40 * 736042 * 2
def baseEnd_736042 : Nat := 167974812398539762662227

theorem tailTrace_736042 : CollatzResearch.WordTrace tailWord_736042 prefixEnd_736042 167974812398539762662227 := by
  unfold tailWord_736042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711414299863253702686595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17897104799635343207164253 6711414299863253702686595)
  ·
    refine ⟨10067121449794880554029893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6711414299863253702686595 10067121449794880554029893)
    ·
      refine ⟨1887585271836540103880605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10067121449794880554029893 1887585271836540103880605)
      ·
        refine ⟨707844476938702538955227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1887585271836540103880605 707844476938702538955227)
        ·
          refine ⟨1061766715408053808432841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707844476938702538955227 1061766715408053808432841)
          ·
            refine ⟨796325036556040356324631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061766715408053808432841 796325036556040356324631)
            ·
              refine ⟨1194487554834060534486947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796325036556040356324631 1194487554834060534486947)
              ·
                refine ⟨1791731332251090801730421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194487554834060534486947 1791731332251090801730421)
                ·
                  refine ⟨167974812398539762662227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791731332251090801730421 167974812398539762662227)
                  ·
                    rfl

theorem cell21_736042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_736042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736042 prefixEnd_736042 := by exact prefixLift 736042
  have htrace : WordTrace (prefixWord ++ tailWord_736042) baseStart_736042 baseEnd_736042 := by
    simpa [prefixWord, tailWord_736042, baseEnd_736042] using wordTrace_append hprefix tailTrace_736042
  have hstable : (prefixWord ++ tailWord_736042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736042).length < 2 ^ (prefixWord ++ tailWord_736042).sum := by decide
  have hdescent : baseEnd_736042 < baseStart_736042 := by decide
  rcases family_descends (prefixWord ++ tailWord_736042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736053 : List Nat := [1, 3, 3, 1, 3, 2, 2, 6]
def baseStart_736053 : Nat := 118140960795 + 736053 * 2 ^ 59
def prefixEnd_736053 : Nat := 4983230072969 + 3 ^ 40 * 736053 * 2
def baseEnd_736053 : Nat := 55992440916135395992957

theorem tailTrace_736053 : CollatzResearch.WordTrace tailWord_736053 prefixEnd_736053 55992440916135395992957 := by
  unfold tailWord_736053
  simp only [CollatzResearch.WordTrace]
  refine ⟨26846058402413163689396813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17897372268275442459597875 26846058402413163689396813)
  ·
    refine ⟨10067271900904936383523805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26846058402413163689396813 10067271900904936383523805)
    ·
      refine ⟨3775226962839351143821427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10067271900904936383523805 3775226962839351143821427)
      ·
        refine ⟨5662840444259026715732141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775226962839351143821427 5662840444259026715732141)
        ·
          refine ⟨2123565166597135018399553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5662840444259026715732141 2123565166597135018399553)
          ·
            refine ⟨1592673874947851263799665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2123565166597135018399553 1592673874947851263799665)
            ·
              refine ⟨1194505406210888447849749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592673874947851263799665 1194505406210888447849749)
              ·
                refine ⟨55992440916135395992957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1194505406210888447849749 55992440916135395992957)
                ·
                  rfl

theorem cell21_736053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_736053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736053 prefixEnd_736053 := by exact prefixLift 736053
  have htrace : WordTrace (prefixWord ++ tailWord_736053) baseStart_736053 baseEnd_736053 := by
    simpa [prefixWord, tailWord_736053, baseEnd_736053] using wordTrace_append hprefix tailTrace_736053
  have hstable : (prefixWord ++ tailWord_736053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736053).length < 2 ^ (prefixWord ++ tailWord_736053).sum := by decide
  have hdescent : baseEnd_736053 < baseStart_736053 := by decide
  rcases family_descends (prefixWord ++ tailWord_736053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736101 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 3]
def baseStart_736101 : Nat := 118140960795 + 736101 * 2 ^ 59
def prefixEnd_736101 : Nat := 4983230072969 + 3 ^ 40 * 736101 * 2
def baseEnd_736101 : Nat := 167988277002368771178773

theorem tailTrace_736101 : CollatzResearch.WordTrace tailWord_736101 prefixEnd_736101 167988277002368771178773 := by
  unfold tailWord_736101
  simp only [CollatzResearch.WordTrace]
  refine ⟨26847809106239267887144157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17898539404159511924762771 26847809106239267887144157)
  ·
    refine ⟨10067928414839725457679059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26847809106239267887144157 10067928414839725457679059)
    ·
      refine ⟨15101892622259588186518589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067928414839725457679059 15101892622259588186518589)
      ·
        refine ⟨5663209733347345569944471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15101892622259588186518589 5663209733347345569944471)
        ·
          refine ⟨8494814600021018354916707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663209733347345569944471 8494814600021018354916707)
          ·
            refine ⟨12742221900031527532375061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494814600021018354916707 12742221900031527532375061)
            ·
              refine ⟨597291651563977853080081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12742221900031527532375061 597291651563977853080081)
              ·
                refine ⟨447968738672983389810061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597291651563977853080081 447968738672983389810061)
                ·
                  refine ⟨167988277002368771178773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447968738672983389810061 167988277002368771178773)
                  ·
                    rfl

theorem cell21_736101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_736101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736101 prefixEnd_736101 := by exact prefixLift 736101
  have htrace : WordTrace (prefixWord ++ tailWord_736101) baseStart_736101 baseEnd_736101 := by
    simpa [prefixWord, tailWord_736101, baseEnd_736101] using wordTrace_append hprefix tailTrace_736101
  have hstable : (prefixWord ++ tailWord_736101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736101).length < 2 ^ (prefixWord ++ tailWord_736101).sum := by decide
  have hdescent : baseEnd_736101 < baseStart_736101 := by decide
  rcases family_descends (prefixWord ++ tailWord_736101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736112 : List Nat := [2, 1, 1, 1, 4, 1, 5, 6]
def baseStart_736112 : Nat := 118140960795 + 736112 * 2 ^ 59
def prefixEnd_736112 : Nat := 4983230072969 + 3 ^ 40 * 736112 * 2
def baseEnd_736112 : Nat := 55996929117411732165139

theorem tailTrace_736112 : CollatzResearch.WordTrace tailWord_736112 prefixEnd_736112 55996929117411732165139 := by
  unfold tailWord_736112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13424105154599708382897295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17898806872799611177196393 13424105154599708382897295)
  ·
    refine ⟨20136157731899562574345943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13424105154599708382897295 20136157731899562574345943)
    ·
      refine ⟨30204236597849343861518915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20136157731899562574345943 30204236597849343861518915)
      ·
        refine ⟨45306354896774015792278373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30204236597849343861518915 45306354896774015792278373)
        ·
          refine ⟨8494941543145127961052195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45306354896774015792278373 8494941543145127961052195)
          ·
            refine ⟨12742412314717691941578293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494941543145127961052195 12742412314717691941578293)
            ·
              refine ⟨1194601154504783619522965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12742412314717691941578293 1194601154504783619522965)
              ·
                refine ⟨55996929117411732165139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1194601154504783619522965 55996929117411732165139)
                ·
                  rfl

theorem cell21_736112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_736112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736112 prefixEnd_736112 := by exact prefixLift 736112
  have htrace : WordTrace (prefixWord ++ tailWord_736112) baseStart_736112 baseEnd_736112 := by
    simpa [prefixWord, tailWord_736112, baseEnd_736112] using wordTrace_append hprefix tailTrace_736112
  have hstable : (prefixWord ++ tailWord_736112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736112).length < 2 ^ (prefixWord ++ tailWord_736112).sum := by decide
  have hdescent : baseEnd_736112 < baseStart_736112 := by decide
  rcases family_descends (prefixWord ++ tailWord_736112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736160 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_736160 : Nat := 118140960795 + 736160 * 2 ^ 59
def prefixEnd_736160 : Nat := 4983230072969 + 3 ^ 40 * 736160 * 2
def baseEnd_736160 : Nat := 168001741606197779695319

theorem tailTrace_736160 : CollatzResearch.WordTrace tailWord_736160 prefixEnd_736160 168001741606197779695319 := by
  unfold tailWord_736160
  simp only [CollatzResearch.WordTrace]
  refine ⟨13424980506512760481770967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17899974008683680642361289 13424980506512760481770967)
  ·
    refine ⟨20137470759769140722656451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13424980506512760481770967 20137470759769140722656451)
    ·
      refine ⟨30206206139653711083984677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20137470759769140722656451 30206206139653711083984677)
      ·
        refine ⟨5663663651185070828247127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30206206139653711083984677 5663663651185070828247127)
        ·
          refine ⟨8495495476777606242370691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663663651185070828247127 8495495476777606242370691)
          ·
            refine ⟨12743243215166409363556037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495495476777606242370691 12743243215166409363556037)
            ·
              refine ⟨2389358102843701755666757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12743243215166409363556037 2389358102843701755666757)
              ·
                refine ⟨448004644283194079187517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2389358102843701755666757 448004644283194079187517)
                ·
                  refine ⟨168001741606197779695319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448004644283194079187517 168001741606197779695319)
                  ·
                    rfl

theorem cell21_736160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_736160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736160 prefixEnd_736160 := by exact prefixLift 736160
  have htrace : WordTrace (prefixWord ++ tailWord_736160) baseStart_736160 baseEnd_736160 := by
    simpa [prefixWord, tailWord_736160, baseEnd_736160] using wordTrace_append hprefix tailTrace_736160
  have hstable : (prefixWord ++ tailWord_736160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736160).length < 2 ^ (prefixWord ++ tailWord_736160).sum := by decide
  have hdescent : baseEnd_736160 < baseStart_736160 := by decide
  rcases family_descends (prefixWord ++ tailWord_736160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736270 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_736270 : Nat := 118140960795 + 736270 * 2 ^ 59
def prefixEnd_736270 : Nat := 4983230072969 + 3 ^ 40 * 736270 * 2
def baseEnd_736270 : Nat := 168026845104862032861761

theorem tailTrace_736270 : CollatzResearch.WordTrace tailWord_736270 prefixEnd_736270 168026845104862032861761 := by
  unfold tailWord_736270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356746630328376218755783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17902648695084673166697509 3356746630328376218755783)
  ·
    refine ⟨5035119945492564328133675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3356746630328376218755783 5035119945492564328133675)
    ·
      refine ⟨7552679918238846492200513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5035119945492564328133675 7552679918238846492200513)
      ·
        refine ⟨5664509938679134869150385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7552679918238846492200513 5664509938679134869150385)
        ·
          refine ⟨4248382454009351151862789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5664509938679134869150385 4248382454009351151862789)
          ·
            refine ⟨796571710126753340974273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4248382454009351151862789 796571710126753340974273)
            ·
              refine ⟨597428782595065005730705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796571710126753340974273 597428782595065005730705)
              ·
                refine ⟨448071586946298754298029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597428782595065005730705 448071586946298754298029)
                ·
                  refine ⟨168026845104862032861761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448071586946298754298029 168026845104862032861761)
                  ·
                    rfl

theorem cell21_736270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_736270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736270 prefixEnd_736270 := by exact prefixLift 736270
  have htrace : WordTrace (prefixWord ++ tailWord_736270) baseStart_736270 baseEnd_736270 := by
    simpa [prefixWord, tailWord_736270, baseEnd_736270] using wordTrace_append hprefix tailTrace_736270
  have hstable : (prefixWord ++ tailWord_736270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736270).length < 2 ^ (prefixWord ++ tailWord_736270).sum := by decide
  have hdescent : baseEnd_736270 < baseStart_736270 := by decide
  rcases family_descends (prefixWord ++ tailWord_736270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736298 : List Nat := [3, 1, 4, 1, 3, 1, 3, 5]
def baseStart_736298 : Nat := 118140960795 + 736298 * 2 ^ 59
def prefixEnd_736298 : Nat := 4983230072969 + 3 ^ 40 * 736298 * 2
def baseEnd_736298 : Nat := 56011078362113402131679

theorem tailTrace_736298 : CollatzResearch.WordTrace tailWord_736298 prefixEnd_736298 56011078362113402131679 := by
  unfold tailWord_736298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713748571631392633016387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17903329524350380354710365 6713748571631392633016387)
  ·
    refine ⟨10070622857447088949524581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713748571631392633016387 10070622857447088949524581)
    ·
      refine ⟨1888241785771329178035859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10070622857447088949524581 1888241785771329178035859)
      ·
        refine ⟨2832362678656993767053789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888241785771329178035859 2832362678656993767053789)
        ·
          refine ⟨1062136004496372662645171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2832362678656993767053789 1062136004496372662645171)
          ·
            refine ⟨1593204006744558993967757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062136004496372662645171 1593204006744558993967757)
            ·
              refine ⟨597451502529209622737909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593204006744558993967757 597451502529209622737909)
              ·
                refine ⟨56011078362113402131679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 597451502529209622737909 56011078362113402131679)
                ·
                  rfl

theorem cell21_736298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_736298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736298 prefixEnd_736298 := by exact prefixLift 736298
  have htrace : WordTrace (prefixWord ++ tailWord_736298) baseStart_736298 baseEnd_736298 := by
    simpa [prefixWord, tailWord_736298, baseEnd_736298] using wordTrace_append hprefix tailTrace_736298
  have hstable : (prefixWord ++ tailWord_736298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736298).length < 2 ^ (prefixWord ++ tailWord_736298).sum := by decide
  have hdescent : baseEnd_736298 < baseStart_736298 := by decide
  rcases family_descends (prefixWord ++ tailWord_736298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736309 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_736309 : Nat := 118140960795 + 736309 * 2 ^ 59
def prefixEnd_736309 : Nat := 4983230072969 + 3 ^ 40 * 736309 * 2
def baseEnd_736309 : Nat := 168035745436206631711681

theorem tailTrace_736309 : CollatzResearch.WordTrace tailWord_736309 prefixEnd_736309 168035745436206631711681 := by
  unfold tailWord_736309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855395489485719410715981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17903596992990479607143987 26855395489485719410715981)
  ·
    refine ⟨10070773308557144779018493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26855395489485719410715981 10070773308557144779018493)
    ·
      refine ⟨3776539990708929292131935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10070773308557144779018493 3776539990708929292131935)
      ·
        refine ⟨5664809986063393938197903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776539990708929292131935 5664809986063393938197903)
        ·
          refine ⟨8497214979095090907296855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5664809986063393938197903 8497214979095090907296855)
          ·
            refine ⟨12745822468642636360945283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8497214979095090907296855 12745822468642636360945283)
            ·
              refine ⟨19118733702963954541417925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12745822468642636360945283 19118733702963954541417925)
              ·
                refine ⟨3584762569305741476515861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19118733702963954541417925 3584762569305741476515861)
                ·
                  refine ⟨168035745436206631711681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3584762569305741476515861 168035745436206631711681)
                  ·
                    rfl

theorem cell21_736309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_736309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736309 prefixEnd_736309 := by exact prefixLift 736309
  have htrace : WordTrace (prefixWord ++ tailWord_736309) baseStart_736309 baseEnd_736309 := by
    simpa [prefixWord, tailWord_736309, baseEnd_736309] using wordTrace_append hprefix tailTrace_736309
  have hstable : (prefixWord ++ tailWord_736309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736309).length < 2 ^ (prefixWord ++ tailWord_736309).sum := by decide
  have hdescent : baseEnd_736309 < baseStart_736309 := by decide
  rcases family_descends (prefixWord ++ tailWord_736309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736312 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_736312 : Nat := 118140960795 + 736312 * 2 ^ 59
def prefixEnd_736312 : Nat := 4983230072969 + 3 ^ 40 * 736312 * 2
def baseEnd_736312 : Nat := 168036430077079293161675

theorem tailTrace_736312 : CollatzResearch.WordTrace tailWord_736312 prefixEnd_736312 168036430077079293161675 := by
  unfold tailWord_736312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13427752454237425461537595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17903669938983233948716793 13427752454237425461537595)
  ·
    refine ⟨20141628681356138192306393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13427752454237425461537595 20141628681356138192306393)
    ·
      refine ⟨15106221511017103644229795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20141628681356138192306393 15106221511017103644229795)
      ·
        refine ⟨22659332266525655466344693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106221511017103644229795 22659332266525655466344693)
        ·
          refine ⟨2124312399986780199969815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22659332266525655466344693 2124312399986780199969815)
          ·
            refine ⟨3186468599980170299954723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124312399986780199969815 3186468599980170299954723)
            ·
              refine ⟨4779702899970255449932085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186468599980170299954723 4779702899970255449932085)
              ·
                refine ⟨448097146872211448431133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4779702899970255449932085 448097146872211448431133)
                ·
                  refine ⟨168036430077079293161675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448097146872211448431133 168036430077079293161675)
                  ·
                    rfl

theorem cell21_736312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_736312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736312 prefixEnd_736312 := by exact prefixLift 736312
  have htrace : WordTrace (prefixWord ++ tailWord_736312) baseStart_736312 baseEnd_736312 := by
    simpa [prefixWord, tailWord_736312, baseEnd_736312] using wordTrace_append hprefix tailTrace_736312
  have hstable : (prefixWord ++ tailWord_736312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736312).length < 2 ^ (prefixWord ++ tailWord_736312).sum := by decide
  have hdescent : baseEnd_736312 < baseStart_736312 := by decide
  rcases family_descends (prefixWord ++ tailWord_736312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736323 : List Nat := [1, 1, 1, 3, 1, 2, 12]
def baseStart_736323 : Nat := 118140960795 + 736323 * 2 ^ 59
def prefixEnd_736323 : Nat := 4983230072969 + 3 ^ 40 * 736323 * 2
def baseEnd_736323 : Nat := 18670993380771746497591

theorem tailTrace_736323 : CollatzResearch.WordTrace tailWord_736323 prefixEnd_736323 18670993380771746497591 := by
  unfold tailWord_736323
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855906111434999801725623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17903937407623333201150415 26855906111434999801725623)
  ·
    refine ⟨40283859167152499702588435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26855906111434999801725623 40283859167152499702588435)
    ·
      refine ⟨60425788750728749553882653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40283859167152499702588435 60425788750728749553882653)
      ·
        refine ⟨22659670781523281082705995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60425788750728749553882653 22659670781523281082705995)
        ·
          refine ⟨33989506172284921624058993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659670781523281082705995 33989506172284921624058993)
          ·
            refine ⟨25492129629213691218044245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33989506172284921624058993 25492129629213691218044245)
            ·
              refine ⟨18670993380771746497591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25492129629213691218044245 18670993380771746497591)
              ·
                rfl

theorem cell21_736323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 12].length) (baseStart_736323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736323 prefixEnd_736323 := by exact prefixLift 736323
  have htrace : WordTrace (prefixWord ++ tailWord_736323) baseStart_736323 baseEnd_736323 := by
    simpa [prefixWord, tailWord_736323, baseEnd_736323] using wordTrace_append hprefix tailTrace_736323
  have hstable : (prefixWord ++ tailWord_736323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736323).length < 2 ^ (prefixWord ++ tailWord_736323).sum := by decide
  have hdescent : baseEnd_736323 < baseStart_736323 := by decide
  rcases family_descends (prefixWord ++ tailWord_736323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736388 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_736388 : Nat := 118140960795 + 736388 * 2 ^ 59
def prefixEnd_736388 : Nat := 4983230072969 + 3 ^ 40 * 736388 * 2
def baseEnd_736388 : Nat := 168053774312520049894853

theorem tailTrace_736388 : CollatzResearch.WordTrace tailWord_736388 prefixEnd_736388 168053774312520049894853 := by
  unfold tailWord_736388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429138428099757951420909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17905517904133010601894545 13429138428099757951420909)
  ·
    refine ⟨5035926910537409231782841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13429138428099757951420909 5035926910537409231782841)
    ·
      refine ⟨3776945182903056923837131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5035926910537409231782841 3776945182903056923837131)
      ·
        refine ⟨5665417774354585385755697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776945182903056923837131 5665417774354585385755697)
        ·
          refine ⟨4249063330765939039316773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5665417774354585385755697 4249063330765939039316773)
          ·
            refine ⟨796699374518613569871895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4249063330765939039316773 796699374518613569871895)
            ·
              refine ⟨1195049061777920354807843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796699374518613569871895 1195049061777920354807843)
              ·
                refine ⟨1792573592666880532211765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195049061777920354807843 1792573592666880532211765)
                ·
                  refine ⟨168053774312520049894853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792573592666880532211765 168053774312520049894853)
                  ·
                    rfl

theorem cell21_736388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_736388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736388 prefixEnd_736388 := by exact prefixLift 736388
  have htrace : WordTrace (prefixWord ++ tailWord_736388) baseStart_736388 baseEnd_736388 := by
    simpa [prefixWord, tailWord_736388, baseEnd_736388] using wordTrace_append hprefix tailTrace_736388
  have hstable : (prefixWord ++ tailWord_736388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736388).length < 2 ^ (prefixWord ++ tailWord_736388).sum := by decide
  have hdescent : baseEnd_736388 < baseStart_736388 := by decide
  rcases family_descends (prefixWord ++ tailWord_736388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736495 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 4]
def baseStart_736495 : Nat := 118140960795 + 736495 * 2 ^ 59
def prefixEnd_736495 : Nat := 4983230072969 + 3 ^ 40 * 736495 * 2
def baseEnd_736495 : Nat := 168078193170311641611301

theorem tailTrace_736495 : CollatzResearch.WordTrace tailWord_736495 prefixEnd_736495 168078193170311641611301 := by
  unfold tailWord_736495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26862179466811873176986939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17908119644541248784657959 26862179466811873176986939)
  ·
    refine ⟨40293269200217809765480409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26862179466811873176986939 40293269200217809765480409)
    ·
      refine ⟨30219951900163357324110307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40293269200217809765480409 30219951900163357324110307)
      ·
        refine ⟨45329927850245035986165461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30219951900163357324110307 45329927850245035986165461)
        ·
          refine ⟨1062420183990118030925753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45329927850245035986165461 1062420183990118030925753)
          ·
            refine ⟨796815137992588523194315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062420183990118030925753 796815137992588523194315)
            ·
              refine ⟨1195222706988882784791473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796815137992588523194315 1195222706988882784791473)
              ·
                refine ⟨896417030241662088593605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195222706988882784791473 896417030241662088593605)
                ·
                  refine ⟨168078193170311641611301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896417030241662088593605 168078193170311641611301)
                  ·
                    rfl

theorem cell21_736495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_736495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736495 prefixEnd_736495 := by exact prefixLift 736495
  have htrace : WordTrace (prefixWord ++ tailWord_736495) baseStart_736495 baseEnd_736495 := by
    simpa [prefixWord, tailWord_736495, baseEnd_736495] using wordTrace_append hprefix tailTrace_736495
  have hstable : (prefixWord ++ tailWord_736495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736495).length < 2 ^ (prefixWord ++ tailWord_736495).sum := by decide
  have hdescent : baseEnd_736495 < baseStart_736495 := by decide
  rcases family_descends (prefixWord ++ tailWord_736495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736540 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_736540 : Nat := 118140960795 + 736540 * 2 ^ 59
def prefixEnd_736540 : Nat := 4983230072969 + 3 ^ 40 * 736540 * 2
def baseEnd_736540 : Nat := 168088462783401563361209

theorem tailTrace_736540 : CollatzResearch.WordTrace tailWord_736540 prefixEnd_736540 168088462783401563361209 := by
  unfold tailWord_736540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431910375824422931187537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17909213834432563908250049 13431910375824422931187537)
  ·
    refine ⟨10073932781868317198390653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13431910375824422931187537 10073932781868317198390653)
    ·
      refine ⟨3777724793200618949396495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10073932781868317198390653 3777724793200618949396495)
      ·
        refine ⟨5666587189800928424094743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777724793200618949396495 5666587189800928424094743)
        ·
          refine ⟨8499880784701392636142115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5666587189800928424094743 8499880784701392636142115)
          ·
            refine ⟨12749821177052088954213173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499880784701392636142115 12749821177052088954213173)
            ·
              refine ⟨1195295735348633339457485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12749821177052088954213173 1195295735348633339457485)
              ·
                refine ⟨448235900755737502296557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195295735348633339457485 448235900755737502296557)
                ·
                  refine ⟨168088462783401563361209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448235900755737502296557 168088462783401563361209)
                  ·
                    rfl

theorem cell21_736540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_736540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736540 prefixEnd_736540 := by exact prefixLift 736540
  have htrace : WordTrace (prefixWord ++ tailWord_736540) baseStart_736540 baseEnd_736540 := by
    simpa [prefixWord, tailWord_736540, baseEnd_736540] using wordTrace_append hprefix tailTrace_736540
  have hstable : (prefixWord ++ tailWord_736540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736540).length < 2 ^ (prefixWord ++ tailWord_736540).sum := by decide
  have hdescent : baseEnd_736540 < baseStart_736540 := by decide
  rcases family_descends (prefixWord ++ tailWord_736540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736554 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_736554 : Nat := 118140960795 + 736554 * 2 ^ 59
def prefixEnd_736554 : Nat := 4983230072969 + 3 ^ 40 * 736554 * 2
def baseEnd_736554 : Nat := 168091657774140650127847

theorem tailTrace_736554 : CollatzResearch.WordTrace tailWord_736554 prefixEnd_736554 168091657774140650127847 := by
  unfold tailWord_736554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716082843399531563346179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17909554249065417502256477 6716082843399531563346179)
  ·
    refine ⟨10074124265099297345019269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716082843399531563346179 10074124265099297345019269)
    ·
      refine ⟨1888898299706118252191113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10074124265099297345019269 1888898299706118252191113)
      ·
        refine ⟨1416673724779588689143335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888898299706118252191113 1416673724779588689143335)
        ·
          refine ⟨2125010587169383033715003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416673724779588689143335 2125010587169383033715003)
          ·
            refine ⟨3187515880754074550572505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125010587169383033715003 3187515880754074550572505)
            ·
              refine ⟨2390636910565555912929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187515880754074550572505 2390636910565555912929379)
              ·
                refine ⟨3585955365848333869394069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390636910565555912929379 3585955365848333869394069)
                ·
                  refine ⟨168091657774140650127847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3585955365848333869394069 168091657774140650127847)
                  ·
                    rfl

theorem cell21_736554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_736554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736554 prefixEnd_736554 := by exact prefixLift 736554
  have htrace : WordTrace (prefixWord ++ tailWord_736554) baseStart_736554 baseEnd_736554 := by
    simpa [prefixWord, tailWord_736554, baseEnd_736554] using wordTrace_append hprefix tailTrace_736554
  have hstable : (prefixWord ++ tailWord_736554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736554).length < 2 ^ (prefixWord ++ tailWord_736554).sum := by decide
  have hdescent : baseEnd_736554 < baseStart_736554 := by decide
  rcases family_descends (prefixWord ++ tailWord_736554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736557 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 5]
def baseStart_736557 : Nat := 118140960795 + 736557 * 2 ^ 59
def prefixEnd_736557 : Nat := 4983230072969 + 3 ^ 40 * 736557 * 2
def baseEnd_736557 : Nat := 168092342415013311577841

theorem tailTrace_736557 : CollatzResearch.WordTrace tailWord_736557 prefixEnd_736557 168092342415013311577841 := by
  unfold tailWord_736557
  simp only [CollatzResearch.WordTrace]
  refine ⟨26864440792587257765743925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17909627195058171843829283 26864440792587257765743925)
  ·
    refine ⟨2518541324305055415538493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26864440792587257765743925 2518541324305055415538493)
    ·
      refine ⟨944452996614395780826935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2518541324305055415538493 944452996614395780826935)
      ·
        refine ⟨1416679494921593671240403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944452996614395780826935 1416679494921593671240403)
        ·
          refine ⟨2125019242382390506860605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416679494921593671240403 2125019242382390506860605)
          ·
            refine ⟨796882215893396440072727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2125019242382390506860605 796882215893396440072727)
            ·
              refine ⟨1195323323840094660109091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796882215893396440072727 1195323323840094660109091)
              ·
                refine ⟨1792984985760141990163637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195323323840094660109091 1792984985760141990163637)
                ·
                  refine ⟨168092342415013311577841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792984985760141990163637 168092342415013311577841)
                  ·
                    rfl

theorem cell21_736557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_736557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736557 prefixEnd_736557 := by exact prefixLift 736557
  have htrace : WordTrace (prefixWord ++ tailWord_736557) baseStart_736557 baseEnd_736557 := by
    simpa [prefixWord, tailWord_736557, baseEnd_736557] using wordTrace_append hprefix tailTrace_736557
  have hstable : (prefixWord ++ tailWord_736557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736557).length < 2 ^ (prefixWord ++ tailWord_736557).sum := by decide
  have hdescent : baseEnd_736557 < baseStart_736557 := by decide
  rcases family_descends (prefixWord ++ tailWord_736557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736605 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 4]
def baseStart_736605 : Nat := 118140960795 + 736605 * 2 ^ 59
def prefixEnd_736605 : Nat := 4983230072969 + 3 ^ 40 * 736605 * 2
def baseEnd_736605 : Nat := 168103296668975894777743

theorem tailTrace_736605 : CollatzResearch.WordTrace tailWord_736605 prefixEnd_736605 168103296668975894777743 := by
  unfold tailWord_736605
  simp only [CollatzResearch.WordTrace]
  refine ⟨26866191496413361963491269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17910794330942241308994179 26866191496413361963491269)
  ·
    refine ⟨5037410905577505368154613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26866191496413361963491269 5037410905577505368154613)
    ·
      refine ⟨472257272397891128264495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5037410905577505368154613 472257272397891128264495)
      ·
        refine ⟨708385908596836692396743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472257272397891128264495 708385908596836692396743)
        ·
          refine ⟨1062578862895255038595115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708385908596836692396743 1062578862895255038595115)
          ·
            refine ⟨1593868294342882557892673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062578862895255038595115 1593868294342882557892673)
            ·
              refine ⟨1195401220757161918419505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593868294342882557892673 1195401220757161918419505)
              ·
                refine ⟨896550915567871438814629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195401220757161918419505 896550915567871438814629)
                ·
                  refine ⟨168103296668975894777743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896550915567871438814629 168103296668975894777743)
                  ·
                    rfl

theorem cell21_736605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_736605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736605 prefixEnd_736605 := by exact prefixLift 736605
  have htrace : WordTrace (prefixWord ++ tailWord_736605) baseStart_736605 baseEnd_736605 := by
    simpa [prefixWord, tailWord_736605, baseEnd_736605] using wordTrace_append hprefix tailTrace_736605
  have hstable : (prefixWord ++ tailWord_736605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736605).length < 2 ^ (prefixWord ++ tailWord_736605).sum := by decide
  have hdescent : baseEnd_736605 < baseStart_736605 := by decide
  rcases family_descends (prefixWord ++ tailWord_736605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736664 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_736664 : Nat := 118140960795 + 736664 * 2 ^ 59
def prefixEnd_736664 : Nat := 4983230072969 + 3 ^ 40 * 736664 * 2
def baseEnd_736664 : Nat := 168116761272804903294289

theorem tailTrace_736664 : CollatzResearch.WordTrace tailWord_736664 prefixEnd_736664 168116761272804903294289 := by
  unfold tailWord_736664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13434171701599807519944523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17912228935466410026592697 13434171701599807519944523)
  ·
    refine ⟨20151257552399711279916785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13434171701599807519944523 20151257552399711279916785)
    ·
      refine ⟨15113443164299783459937589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20151257552399711279916785 15113443164299783459937589)
      ·
        refine ⟨1416885296653104699369149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15113443164299783459937589 1416885296653104699369149)
        ·
          refine ⟨531331986244914262263431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1416885296653104699369149 531331986244914262263431)
          ·
            refine ⟨796997979367371393395147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531331986244914262263431 796997979367371393395147)
            ·
              refine ⟨1195496969051057090092721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796997979367371393395147 1195496969051057090092721)
              ·
                refine ⟨896622726788292817569541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195496969051057090092721 896622726788292817569541)
                ·
                  refine ⟨168116761272804903294289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896622726788292817569541 168116761272804903294289)
                  ·
                    rfl

theorem cell21_736664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_736664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736664 prefixEnd_736664 := by exact prefixLift 736664
  have htrace : WordTrace (prefixWord ++ tailWord_736664) baseStart_736664 baseEnd_736664 := by
    simpa [prefixWord, tailWord_736664, baseEnd_736664] using wordTrace_append hprefix tailTrace_736664
  have hstable : (prefixWord ++ tailWord_736664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736664).length < 2 ^ (prefixWord ++ tailWord_736664).sum := by decide
  have hdescent : baseEnd_736664 < baseStart_736664 := by decide
  rcases family_descends (prefixWord ++ tailWord_736664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736675 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 3]
def baseStart_736675 : Nat := 118140960795 + 736675 * 2 ^ 59
def prefixEnd_736675 : Nat := 4983230072969 + 3 ^ 40 * 736675 * 2
def baseEnd_736675 : Nat := 168119271622671328610933

theorem tailTrace_736675 : CollatzResearch.WordTrace tailWord_736675 prefixEnd_736675 168119271622671328610933 := by
  unfold tailWord_736675
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868744606159763918539479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17912496404106509279026319 26868744606159763918539479)
  ·
    refine ⟨40303116909239645877809219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26868744606159763918539479 40303116909239645877809219)
    ·
      refine ⟨60454675363859468816713829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40303116909239645877809219 60454675363859468816713829)
      ·
        refine ⟨11335251630723650403133843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60454675363859468816713829 11335251630723650403133843)
        ·
          refine ⟨17002877446085475604700765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11335251630723650403133843 17002877446085475604700765)
          ·
            refine ⟨6376079042282053351762787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17002877446085475604700765 6376079042282053351762787)
            ·
              refine ⟨9564118563423080027644181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376079042282053351762787 9564118563423080027644181)
              ·
                refine ⟨448318057660456876295821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9564118563423080027644181 448318057660456876295821)
                ·
                  refine ⟨168119271622671328610933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448318057660456876295821 168119271622671328610933)
                  ·
                    rfl

theorem cell21_736675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3].length) (baseStart_736675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736675 prefixEnd_736675 := by exact prefixLift 736675
  have htrace : WordTrace (prefixWord ++ tailWord_736675) baseStart_736675 baseEnd_736675 := by
    simpa [prefixWord, tailWord_736675, baseEnd_736675] using wordTrace_append hprefix tailTrace_736675
  have hstable : (prefixWord ++ tailWord_736675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736675).length < 2 ^ (prefixWord ++ tailWord_736675).sum := by decide
  have hdescent : baseEnd_736675 < baseStart_736675 := by decide
  rcases family_descends (prefixWord ++ tailWord_736675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736726 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_736726 : Nat := 118140960795 + 736726 * 2 ^ 59
def prefixEnd_736726 : Nat := 4983230072969 + 3 ^ 40 * 736726 * 2
def baseEnd_736726 : Nat := 168130910517506573260829

theorem tailTrace_736726 : CollatzResearch.WordTrace tailWord_736726 prefixEnd_736726 168130910517506573260829 := by
  unfold tailWord_736726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679412795560937476790377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17913736485983333085764021 1679412795560937476790377)
  ·
    refine ⟨1259559596670703107592783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1679412795560937476790377 1259559596670703107592783)
    ·
      refine ⟨1889339395006054661389175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259559596670703107592783 1889339395006054661389175)
      ·
        refine ⟨2834009092509081992083763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889339395006054661389175 2834009092509081992083763)
        ·
          refine ⟨4251013638763622988125645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834009092509081992083763 4251013638763622988125645)
          ·
            refine ⟨1594130114536358620547117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251013638763622988125645 1594130114536358620547117)
            ·
              refine ⟨597798792951134482705169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1594130114536358620547117 597798792951134482705169)
              ·
                refine ⟨448349094713350862028877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597798792951134482705169 448349094713350862028877)
                ·
                  refine ⟨168130910517506573260829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448349094713350862028877 168130910517506573260829)
                  ·
                    rfl

theorem cell21_736726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_736726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736726 prefixEnd_736726 := by exact prefixLift 736726
  have htrace : WordTrace (prefixWord ++ tailWord_736726) baseStart_736726 baseEnd_736726 := by
    simpa [prefixWord, tailWord_736726, baseEnd_736726] using wordTrace_append hprefix tailTrace_736726
  have hstable : (prefixWord ++ tailWord_736726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736726).length < 2 ^ (prefixWord ++ tailWord_736726).sum := by decide
  have hdescent : baseEnd_736726 < baseStart_736726 := by decide
  rcases family_descends (prefixWord ++ tailWord_736726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736748 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_736748 : Nat := 118140960795 + 736748 * 2 ^ 59
def prefixEnd_736748 : Nat := 4983230072969 + 3 ^ 40 * 736748 * 2
def baseEnd_736748 : Nat := 168135931217239423894117

theorem tailTrace_736748 : CollatzResearch.WordTrace tailWord_736748 prefixEnd_736748 168135931217239423894117 := by
  unfold tailWord_736748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435703567447648692973449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17914271423263531590631265 13435703567447648692973449)
  ·
    refine ⟨10076777675585736519730087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13435703567447648692973449 10076777675585736519730087)
    ·
      refine ⟨15115166513378604779595131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10076777675585736519730087 15115166513378604779595131)
      ·
        refine ⟨22672749770067907169392697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115166513378604779595131 22672749770067907169392697)
        ·
          refine ⟨17004562327550930377044523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22672749770067907169392697 17004562327550930377044523)
          ·
            refine ⟨25506843491326395565566785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17004562327550930377044523 25506843491326395565566785)
            ·
              refine ⟨19130132618494796674175089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25506843491326395565566785 19130132618494796674175089)
              ·
                refine ⟨14347599463871097505631317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19130132618494796674175089 14347599463871097505631317)
                ·
                  refine ⟨168135931217239423894117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14347599463871097505631317 168135931217239423894117)
                  ·
                    rfl

theorem cell21_736748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_736748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736748 prefixEnd_736748 := by exact prefixLift 736748
  have htrace : WordTrace (prefixWord ++ tailWord_736748) baseStart_736748 baseEnd_736748 := by
    simpa [prefixWord, tailWord_736748, baseEnd_736748] using wordTrace_append hprefix tailTrace_736748
  have hstable : (prefixWord ++ tailWord_736748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736748).length < 2 ^ (prefixWord ++ tailWord_736748).sum := by decide
  have hdescent : baseEnd_736748 < baseStart_736748 := by decide
  rcases family_descends (prefixWord ++ tailWord_736748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736779 : List Nat := [1, 1, 1, 1, 8, 9]
def baseStart_736779 : Nat := 118140960795 + 736779 * 2 ^ 59
def prefixEnd_736779 : Nat := 4983230072969 + 3 ^ 40 * 736779 * 2
def baseEnd_736779 : Nat := 6227518734799639217681

theorem tailTrace_736779 : CollatzResearch.WordTrace tailWord_736779 prefixEnd_736779 6227518734799639217681 := by
  unfold tailWord_736779
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872537797782989680325391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17915025198521993120216927 26872537797782989680325391)
  ·
    refine ⟨40308806696674484520488087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26872537797782989680325391 40308806696674484520488087)
    ·
      refine ⟨60463210045011726780732131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40308806696674484520488087 60463210045011726780732131)
      ·
        refine ⟨90694815067517590171098197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60463210045011726780732131 90694815067517590171098197)
        ·
          refine ⟨1062829864072471759817557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 90694815067517590171098197 1062829864072471759817557)
          ·
            refine ⟨6227518734799639217681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1062829864072471759817557 6227518734799639217681)
            ·
              rfl

theorem cell21_736779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 9].length) (baseStart_736779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736779 prefixEnd_736779 := by exact prefixLift 736779
  have htrace : WordTrace (prefixWord ++ tailWord_736779) baseStart_736779 baseEnd_736779 := by
    simpa [prefixWord, tailWord_736779, baseEnd_736779] using wordTrace_append hprefix tailTrace_736779
  have hstable : (prefixWord ++ tailWord_736779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736779).length < 2 ^ (prefixWord ++ tailWord_736779).sum := by decide
  have hdescent : baseEnd_736779 < baseStart_736779 := by decide
  rcases family_descends (prefixWord ++ tailWord_736779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736872 : List Nat := [2, 1, 4, 3, 1, 2, 1, 7]
def baseStart_736872 : Nat := 118140960795 + 736872 * 2 ^ 59
def prefixEnd_736872 : Nat := 4983230072969 + 3 ^ 40 * 736872 * 2
def baseEnd_736872 : Nat := 56054743235547587942399

theorem tailTrace_736872 : CollatzResearch.WordTrace tailWord_736872 prefixEnd_736872 56054743235547587942399 := by
  unfold tailWord_736872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13437964893223033281730435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17917286524297377708973913 13437964893223033281730435)
  ·
    refine ⟨20156947339834549922595653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13437964893223033281730435 20156947339834549922595653)
    ·
      refine ⟨3779427626218978110486685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20156947339834549922595653 3779427626218978110486685)
      ·
        refine ⟨1417285359832116791432507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3779427626218978110486685 1417285359832116791432507)
        ·
          refine ⟨2125928039748175187148761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417285359832116791432507 2125928039748175187148761)
          ·
            refine ⟨1594446029811131390361571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125928039748175187148761 1594446029811131390361571)
            ·
              refine ⟨2391669044716697085542357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594446029811131390361571 2391669044716697085542357)
              ·
                refine ⟨56054743235547587942399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2391669044716697085542357 56054743235547587942399)
                ·
                  rfl

theorem cell21_736872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_736872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736872 prefixEnd_736872 := by exact prefixLift 736872
  have htrace : WordTrace (prefixWord ++ tailWord_736872) baseStart_736872 baseEnd_736872 := by
    simpa [prefixWord, tailWord_736872, baseEnd_736872] using wordTrace_append hprefix tailTrace_736872
  have hstable : (prefixWord ++ tailWord_736872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736872).length < 2 ^ (prefixWord ++ tailWord_736872).sum := by decide
  have hdescent : baseEnd_736872 < baseStart_736872 := by decide
  rcases family_descends (prefixWord ++ tailWord_736872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736878 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_736878 : Nat := 118140960795 + 736878 * 2 ^ 59
def prefixEnd_736878 : Nat := 4983230072969 + 3 ^ 40 * 736878 * 2
def baseEnd_736878 : Nat := 168165598988388086727185

theorem tailTrace_736878 : CollatzResearch.WordTrace tailWord_736878 prefixEnd_736878 168165598988388086727185 := by
  unfold tailWord_736878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359518578053041198522411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17917432416282886392119525 3359518578053041198522411)
  ·
    refine ⟨5039277867079561797783617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359518578053041198522411 5039277867079561797783617)
    ·
      refine ⟨3779458400309671348337713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039277867079561797783617 3779458400309671348337713)
      ·
        refine ⟨2834593800232253511253285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779458400309671348337713 2834593800232253511253285)
        ·
          refine ⟨531486337543547533359991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2834593800232253511253285 531486337543547533359991)
          ·
            refine ⟨797229506315321300039987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531486337543547533359991 797229506315321300039987)
            ·
              refine ⟨1195844259472981950059981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797229506315321300039987 1195844259472981950059981)
              ·
                refine ⟨448441597302368231272493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195844259472981950059981 448441597302368231272493)
                ·
                  refine ⟨168165598988388086727185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448441597302368231272493 168165598988388086727185)
                  ·
                    rfl

theorem cell21_736878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_736878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736878 prefixEnd_736878 := by exact prefixLift 736878
  have htrace : WordTrace (prefixWord ++ tailWord_736878) baseStart_736878 baseEnd_736878 := by
    simpa [prefixWord, tailWord_736878, baseEnd_736878] using wordTrace_append hprefix tailTrace_736878
  have hstable : (prefixWord ++ tailWord_736878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736878).length < 2 ^ (prefixWord ++ tailWord_736878).sum := by decide
  have hdescent : baseEnd_736878 < baseStart_736878 := by decide
  rcases family_descends (prefixWord ++ tailWord_736878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736903 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 5]
def baseStart_736903 : Nat := 118140960795 + 736903 * 2 ^ 59
def prefixEnd_736903 : Nat := 4983230072969 + 3 ^ 40 * 736903 * 2
def baseEnd_736903 : Nat := 168171304328993598810467

theorem tailTrace_736903 : CollatzResearch.WordTrace tailWord_736903 prefixEnd_736903 168171304328993598810467 := by
  unfold tailWord_736903
  simp only [CollatzResearch.WordTrace]
  refine ⟨26877060449333758857839363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17918040299555839238559575 26877060449333758857839363)
  ·
    refine ⟨40315590674000638286759045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26877060449333758857839363 40315590674000638286759045)
    ·
      refine ⟨7559173251375119678767321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40315590674000638286759045 7559173251375119678767321)
      ·
        refine ⟨5669379938531339759075491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7559173251375119678767321 5669379938531339759075491)
        ·
          refine ⟨8504069907797009638613237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669379938531339759075491 8504069907797009638613237)
          ·
            refine ⟨797256553855969653619991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8504069907797009638613237 797256553855969653619991)
            ·
              refine ⟨1195884830783954480429987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797256553855969653619991 1195884830783954480429987)
              ·
                refine ⟨1793827246175931720644981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195884830783954480429987 1793827246175931720644981)
                ·
                  refine ⟨168171304328993598810467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1793827246175931720644981 168171304328993598810467)
                  ·
                    rfl

theorem cell21_736903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_736903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_736903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_736903 prefixEnd_736903 := by exact prefixLift 736903
  have htrace : WordTrace (prefixWord ++ tailWord_736903) baseStart_736903 baseEnd_736903 := by
    simpa [prefixWord, tailWord_736903, baseEnd_736903] using wordTrace_append hprefix tailTrace_736903
  have hstable : (prefixWord ++ tailWord_736903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736903).length < 2 ^ (prefixWord ++ tailWord_736903).sum := by decide
  have hdescent : baseEnd_736903 < baseStart_736903 := by decide
  rcases family_descends (prefixWord ++ tailWord_736903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737038 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_737038 : Nat := 118140960795 + 737038 * 2 ^ 59
def prefixEnd_737038 : Nat := 4983230072969 + 3 ^ 40 * 737038 * 2
def baseEnd_737038 : Nat := 168202113168263364060191

theorem tailTrace_737038 : CollatzResearch.WordTrace tailWord_737038 prefixEnd_737038 168202113168263364060191 := by
  unfold tailWord_737038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360248037980584614250471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17921322869229784609335845 3360248037980584614250471)
  ·
    refine ⟨5040372056970876921375707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3360248037980584614250471 5040372056970876921375707)
    ·
      refine ⟨7560558085456315382063561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040372056970876921375707 7560558085456315382063561)
      ·
        refine ⟨5670418564092236536547671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7560558085456315382063561 5670418564092236536547671)
        ·
          refine ⟨8505627846138354804821507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670418564092236536547671 8505627846138354804821507)
          ·
            refine ⟨12758441769207532207232261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505627846138354804821507 12758441769207532207232261)
            ·
              refine ⟨2392207831726412288856049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12758441769207532207232261 2392207831726412288856049)
              ·
                refine ⟨1794155873794809216642037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392207831726412288856049 1794155873794809216642037)
                ·
                  refine ⟨168202113168263364060191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1794155873794809216642037 168202113168263364060191)
                  ·
                    rfl

theorem cell21_737038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_737038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737038 prefixEnd_737038 := by exact prefixLift 737038
  have htrace : WordTrace (prefixWord ++ tailWord_737038) baseStart_737038 baseEnd_737038 := by
    simpa [prefixWord, tailWord_737038, baseEnd_737038] using wordTrace_append hprefix tailTrace_737038
  have hstable : (prefixWord ++ tailWord_737038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737038).length < 2 ^ (prefixWord ++ tailWord_737038).sum := by decide
  have hdescent : baseEnd_737038 < baseStart_737038 := by decide
  rcases family_descends (prefixWord ++ tailWord_737038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737052 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_737052 : Nat := 118140960795 + 737052 * 2 ^ 59
def prefixEnd_737052 : Nat := 4983230072969 + 3 ^ 40 * 737052 * 2
def baseEnd_737052 : Nat := 168205308159002450826829

theorem tailTrace_737052 : CollatzResearch.WordTrace tailWord_737052 prefixEnd_737052 168205308159002450826829 := by
  unfold tailWord_737052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441247462896978652506705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17921663283862638203342273 13441247462896978652506705)
  ·
    refine ⟨10080935597172733989380029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13441247462896978652506705 10080935597172733989380029)
    ·
      refine ⟨3780350848939775246017511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10080935597172733989380029 3780350848939775246017511)
      ·
        refine ⟨5670526273409662869026267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780350848939775246017511 5670526273409662869026267)
        ·
          refine ⟨8505789410114494303539401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670526273409662869026267 8505789410114494303539401)
          ·
            refine ⟨6379342057585870727654551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8505789410114494303539401 6379342057585870727654551)
            ·
              refine ⟨9569013086378806091481827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6379342057585870727654551 9569013086378806091481827)
              ·
                refine ⟨14353519629568209137222741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9569013086378806091481827 14353519629568209137222741)
                ·
                  refine ⟨168205308159002450826829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14353519629568209137222741 168205308159002450826829)
                  ·
                    rfl

theorem cell21_737052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_737052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737052 prefixEnd_737052 := by exact prefixLift 737052
  have htrace : WordTrace (prefixWord ++ tailWord_737052) baseStart_737052 baseEnd_737052 := by
    simpa [prefixWord, tailWord_737052, baseEnd_737052] using wordTrace_append hprefix tailTrace_737052
  have hstable : (prefixWord ++ tailWord_737052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737052).length < 2 ^ (prefixWord ++ tailWord_737052).sum := by decide
  have hdescent : baseEnd_737052 < baseStart_737052 := by decide
  rcases family_descends (prefixWord ++ tailWord_737052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737086 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_737086 : Nat := 118140960795 + 737086 * 2 ^ 59
def prefixEnd_737086 : Nat := 4983230072969 + 3 ^ 40 * 737086 * 2
def baseEnd_737086 : Nat := 168213067422225947260093

theorem tailTrace_737086 : CollatzResearch.WordTrace tailWord_737086 prefixEnd_737086 168213067422225947260093 := by
  unfold tailWord_737086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360466875958847638968889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17922490005113854074500741 3360466875958847638968889)
  ·
    refine ⟨2520350156969135729226667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3360466875958847638968889 2520350156969135729226667)
    ·
      refine ⟨3780525235453703593840001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2520350156969135729226667 3780525235453703593840001)
      ·
        refine ⟨2835393926590277695380001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3780525235453703593840001 2835393926590277695380001)
        ·
          refine ⟨2126545444942708271535001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2835393926590277695380001 2126545444942708271535001)
          ·
            refine ⟨1594909083707031203651251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2126545444942708271535001 1594909083707031203651251)
            ·
              refine ⟨2392363625560546805476877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594909083707031203651251 2392363625560546805476877)
              ·
                refine ⟨897136359585205052053829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2392363625560546805476877 897136359585205052053829)
                ·
                  refine ⟨168213067422225947260093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897136359585205052053829 168213067422225947260093)
                  ·
                    rfl

theorem cell21_737086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_737086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737086 prefixEnd_737086 := by exact prefixLift 737086
  have htrace : WordTrace (prefixWord ++ tailWord_737086) baseStart_737086 baseEnd_737086 := by
    simpa [prefixWord, tailWord_737086, baseEnd_737086] using wordTrace_append hprefix tailTrace_737086
  have hstable : (prefixWord ++ tailWord_737086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737086).length < 2 ^ (prefixWord ++ tailWord_737086).sum := by decide
  have hdescent : baseEnd_737086 < baseStart_737086 := by decide
  rcases family_descends (prefixWord ++ tailWord_737086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737097 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_737097 : Nat := 118140960795 + 737097 * 2 ^ 59
def prefixEnd_737097 : Nat := 4983230072969 + 3 ^ 40 * 737097 * 2
def baseEnd_737097 : Nat := 168215577772092372576737

theorem tailTrace_737097 : CollatzResearch.WordTrace tailWord_737097 prefixEnd_737097 168215577772092372576737 := by
  unfold tailWord_737097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26884136210630929990401545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17922757473753953326934363 26884136210630929990401545)
  ·
    refine ⟨20163102157973197492801159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26884136210630929990401545 20163102157973197492801159)
    ·
      refine ⟨30244653236959796239201739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20163102157973197492801159 30244653236959796239201739)
      ·
        refine ⟨45366979855439694358802609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30244653236959796239201739 45366979855439694358802609)
        ·
          refine ⟨34025234891579770769101957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45366979855439694358802609 34025234891579770769101957)
          ·
            refine ⟨6379731542171207019206617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34025234891579770769101957 6379731542171207019206617)
            ·
              refine ⟨4784798656628405264404963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379731542171207019206617 4784798656628405264404963)
              ·
                refine ⟨7177197984942607896607445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784798656628405264404963 7177197984942607896607445)
                ·
                  refine ⟨168215577772092372576737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7177197984942607896607445 168215577772092372576737)
                  ·
                    rfl

theorem cell21_737097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_737097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737097 prefixEnd_737097 := by exact prefixLift 737097
  have htrace : WordTrace (prefixWord ++ tailWord_737097) baseStart_737097 baseEnd_737097 := by
    simpa [prefixWord, tailWord_737097, baseEnd_737097] using wordTrace_append hprefix tailTrace_737097
  have hstable : (prefixWord ++ tailWord_737097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737097).length < 2 ^ (prefixWord ++ tailWord_737097).sum := by decide
  have hdescent : baseEnd_737097 < baseStart_737097 := by decide
  rcases family_descends (prefixWord ++ tailWord_737097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737173 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_737173 : Nat := 118140960795 + 737173 * 2 ^ 59
def prefixEnd_737173 : Nat := 4983230072969 + 3 ^ 40 * 737173 * 2
def baseEnd_737173 : Nat := 168232922007533129309915

theorem tailTrace_737173 : CollatzResearch.WordTrace tailWord_737173 prefixEnd_737173 168232922007533129309915 := by
  unfold tailWord_737173
  simp only [CollatzResearch.WordTrace]
  refine ⟨26886908158355594970168173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17924605438903729980112115 26886908158355594970168173)
  ·
    refine ⟨10082590559383348113813065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26886908158355594970168173 10082590559383348113813065)
    ·
      refine ⟨7561942919537511085359799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10082590559383348113813065 7561942919537511085359799)
      ·
        refine ⟨11342914379306266628039699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561942919537511085359799 11342914379306266628039699)
        ·
          refine ⟨17014371568959399942059549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11342914379306266628039699 17014371568959399942059549)
          ·
            refine ⟨6380389338359774978272331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17014371568959399942059549 6380389338359774978272331)
            ·
              refine ⟨9570584007539662467408497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380389338359774978272331 9570584007539662467408497)
              ·
                refine ⟨7177938005654746850556373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9570584007539662467408497 7177938005654746850556373)
                ·
                  refine ⟨168232922007533129309915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7177938005654746850556373 168232922007533129309915)
                  ·
                    rfl

theorem cell21_737173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_737173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737173 prefixEnd_737173 := by exact prefixLift 737173
  have htrace : WordTrace (prefixWord ++ tailWord_737173) baseStart_737173 baseEnd_737173 := by
    simpa [prefixWord, tailWord_737173, baseEnd_737173] using wordTrace_append hprefix tailTrace_737173
  have hstable : (prefixWord ++ tailWord_737173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737173).length < 2 ^ (prefixWord ++ tailWord_737173).sum := by decide
  have hdescent : baseEnd_737173 < baseStart_737173 := by decide
  rcases family_descends (prefixWord ++ tailWord_737173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737176 : List Nat := [2, 1, 2, 6, 1, 1, 8]
def baseStart_737176 : Nat := 118140960795 + 737176 * 2 ^ 59
def prefixEnd_737176 : Nat := 4983230072969 + 3 ^ 40 * 737176 * 2
def baseEnd_737176 : Nat := 18692622960933976751101

theorem tailTrace_737176 : CollatzResearch.WordTrace tailWord_737176 prefixEnd_737176 18692622960933976751101 := by
  unfold tailWord_737176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13443508788672363241263691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17924678384896484321684921 13443508788672363241263691)
  ·
    refine ⟨20165263183008544861895537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13443508788672363241263691 20165263183008544861895537)
    ·
      refine ⟨15123947387256408646421653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20165263183008544861895537 15123947387256408646421653)
      ·
        refine ⟨708935033777644155301015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15123947387256408646421653 708935033777644155301015)
        ·
          refine ⟨1063402550666466232951523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708935033777644155301015 1063402550666466232951523)
          ·
            refine ⟨1595103825999699349427285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063402550666466232951523 1595103825999699349427285)
            ·
              refine ⟨18692622960933976751101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1595103825999699349427285 18692622960933976751101)
              ·
                rfl

theorem cell21_737176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 8].length) (baseStart_737176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737176 prefixEnd_737176 := by exact prefixLift 737176
  have htrace : WordTrace (prefixWord ++ tailWord_737176) baseStart_737176 baseEnd_737176 := by
    simpa [prefixWord, tailWord_737176, baseEnd_737176] using wordTrace_append hprefix tailTrace_737176
  have hstable : (prefixWord ++ tailWord_737176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737176).length < 2 ^ (prefixWord ++ tailWord_737176).sum := by decide
  have hdescent : baseEnd_737176 < baseStart_737176 := by decide
  rcases family_descends (prefixWord ++ tailWord_737176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737224 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_737224 : Nat := 118140960795 + 737224 * 2 ^ 59
def prefixEnd_737224 : Nat := 4983230072969 + 3 ^ 40 * 737224 * 2
def baseEnd_737224 : Nat := 168244560902368373959811

theorem tailTrace_737224 : CollatzResearch.WordTrace tailWord_737224 prefixEnd_737224 168244560902368373959811 := by
  unfold tailWord_737224
  simp only [CollatzResearch.WordTrace]
  refine ⟨13444384140585415340137363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17925845520780553786849817 13444384140585415340137363)
  ·
    refine ⟨20166576210878123010206045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13444384140585415340137363 20166576210878123010206045)
    ·
      refine ⟨7562466079079296128827267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20166576210878123010206045 7562466079079296128827267)
      ·
        refine ⟨11343699118618944193240901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562466079079296128827267 11343699118618944193240901)
        ·
          refine ⟨2126943584741052036232669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11343699118618944193240901 2126943584741052036232669)
          ·
            refine ⟨797603844277894513587251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2126943584741052036232669 797603844277894513587251)
            ·
              refine ⟨1196405766416841770380877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797603844277894513587251 1196405766416841770380877)
              ·
                refine ⟨448652162406315663892829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196405766416841770380877 448652162406315663892829)
                ·
                  refine ⟨168244560902368373959811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448652162406315663892829 168244560902368373959811)
                  ·
                    rfl

theorem cell21_737224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_737224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737224 prefixEnd_737224 := by exact prefixLift 737224
  have htrace : WordTrace (prefixWord ++ tailWord_737224) baseStart_737224 baseEnd_737224 := by
    simpa [prefixWord, tailWord_737224, baseEnd_737224] using wordTrace_append hprefix tailTrace_737224
  have hstable : (prefixWord ++ tailWord_737224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737224).length < 2 ^ (prefixWord ++ tailWord_737224).sum := by decide
  have hdescent : baseEnd_737224 < baseStart_737224 := by decide
  rcases family_descends (prefixWord ++ tailWord_737224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737255 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 4]
def baseStart_737255 : Nat := 118140960795 + 737255 * 2 ^ 59
def prefixEnd_737255 : Nat := 4983230072969 + 3 ^ 40 * 737255 * 2
def baseEnd_737255 : Nat := 168251635524719208943081

theorem tailTrace_737255 : CollatzResearch.WordTrace tailWord_737255 prefixEnd_737255 168251635524719208943081 := by
  unfold tailWord_737255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889898944058522974653219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17926599296039015316435479 26889898944058522974653219)
  ·
    refine ⟨40334848416087784461979829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26889898944058522974653219 40334848416087784461979829)
    ·
      refine ⟨3781392039008229793310609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40334848416087784461979829 3781392039008229793310609)
      ·
        refine ⟨2836044029256172344982957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3781392039008229793310609 2836044029256172344982957)
        ·
          refine ⟨1063516510971064629368609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2836044029256172344982957 1063516510971064629368609)
          ·
            refine ⟨797637383228298472026457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063516510971064629368609 797637383228298472026457)
            ·
              refine ⟨598228037421223854019843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797637383228298472026457 598228037421223854019843)
              ·
                refine ⟨897342056131835781029765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598228037421223854019843 897342056131835781029765)
                ·
                  refine ⟨168251635524719208943081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897342056131835781029765 168251635524719208943081)
                  ·
                    rfl

theorem cell21_737255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4].length) (baseStart_737255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737255 prefixEnd_737255 := by exact prefixLift 737255
  have htrace : WordTrace (prefixWord ++ tailWord_737255) baseStart_737255 baseEnd_737255 := by
    simpa [prefixWord, tailWord_737255, baseEnd_737255] using wordTrace_append hprefix tailTrace_737255
  have hstable : (prefixWord ++ tailWord_737255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737255).length < 2 ^ (prefixWord ++ tailWord_737255).sum := by decide
  have hdescent : baseEnd_737255 < baseStart_737255 := by decide
  rcases family_descends (prefixWord ++ tailWord_737255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737286 : List Nat := [6, 2, 1, 2, 1, 9]
def baseStart_737286 : Nat := 118140960795 + 737286 * 2 ^ 59
def prefixEnd_737286 : Nat := 4983230072969 + 3 ^ 40 * 737286 * 2
def baseEnd_737286 : Nat := 6231804079521112738013

theorem tailTrace_737286 : CollatzResearch.WordTrace tailWord_737286 prefixEnd_737286 6231804079521112738013 := by
  unfold tailWord_737286
  simp only [CollatzResearch.WordTrace]
  refine ⟨840344675217069227157241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17927353071297476846021141 840344675217069227157241)
  ·
    refine ⟨630258506412801920367931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 840344675217069227157241 630258506412801920367931)
    ·
      refine ⟨945387759619202880551897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630258506412801920367931 945387759619202880551897)
      ·
        refine ⟨709040819714402160413923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945387759619202880551897 709040819714402160413923)
        ·
          refine ⟨1063561229571603240620885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709040819714402160413923 1063561229571603240620885)
          ·
            refine ⟨6231804079521112738013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1063561229571603240620885 6231804079521112738013)
            ·
              rfl

theorem cell21_737286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 9].length) (baseStart_737286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737286 prefixEnd_737286 := by exact prefixLift 737286
  have htrace : WordTrace (prefixWord ++ tailWord_737286) baseStart_737286 baseEnd_737286 := by
    simpa [prefixWord, tailWord_737286, baseEnd_737286] using wordTrace_append hprefix tailTrace_737286
  have hstable : (prefixWord ++ tailWord_737286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737286).length < 2 ^ (prefixWord ++ tailWord_737286).sum := by decide
  have hdescent : baseEnd_737286 < baseStart_737286 := by decide
  rcases family_descends (prefixWord ++ tailWord_737286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737339 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_737339 : Nat := 118140960795 + 737339 * 2 ^ 59
def prefixEnd_737339 : Nat := 4983230072969 + 3 ^ 40 * 737339 * 2
def baseEnd_737339 : Nat := 168270805469153729542909

theorem tailTrace_737339 : CollatzResearch.WordTrace tailWord_737339 prefixEnd_737339 168270805469153729542909 := by
  unfold tailWord_737339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26892962675754205320711071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17928641783836136880474047 26892962675754205320711071)
  ·
    refine ⟨40339444013631307981066607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26892962675754205320711071 40339444013631307981066607)
    ·
      refine ⟨60509166020446961971599911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40339444013631307981066607 60509166020446961971599911)
      ·
        refine ⟨90763749030670442957399867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60509166020446961971599911 90763749030670442957399867)
        ·
          refine ⟨136145623546005664436099801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90763749030670442957399867 136145623546005664436099801)
          ·
            refine ⟨102109217659504248327074851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136145623546005664436099801 102109217659504248327074851)
            ·
              refine ⟨153163826489256372490612277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102109217659504248327074851 153163826489256372490612277)
              ·
                refine ⟨14359108733367784920994901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153163826489256372490612277 14359108733367784920994901)
                ·
                  refine ⟨168270805469153729542909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14359108733367784920994901 168270805469153729542909)
                  ·
                    rfl

theorem cell21_737339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_737339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737339 prefixEnd_737339 := by exact prefixLift 737339
  have htrace : WordTrace (prefixWord ++ tailWord_737339) baseStart_737339 baseEnd_737339 := by
    simpa [prefixWord, tailWord_737339, baseEnd_737339] using wordTrace_append hprefix tailTrace_737339
  have hstable : (prefixWord ++ tailWord_737339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737339).length < 2 ^ (prefixWord ++ tailWord_737339).sum := by decide
  have hdescent : baseEnd_737339 < baseStart_737339 := by decide
  rcases family_descends (prefixWord ++ tailWord_737339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737370 : List Nat := [3, 1, 1, 2, 1, 1, 4, 8]
def baseStart_737370 : Nat := 118140960795 + 737370 * 2 ^ 59
def prefixEnd_737370 : Nat := 4983230072969 + 3 ^ 40 * 737370 * 2
def baseEnd_737370 : Nat := 56092626697168188175393

theorem tailTrace_737370 : CollatzResearch.WordTrace tailWord_737370 prefixEnd_737370 56092626697168188175393 := by
  unfold tailWord_737370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723523334660474403772391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17929395559094598410059709 6723523334660474403772391)
  ·
    refine ⟨10085285001990711605658587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723523334660474403772391 10085285001990711605658587)
    ·
      refine ⟨15127927502986067408487881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085285001990711605658587 15127927502986067408487881)
      ·
        refine ⟨11345945627239550556365911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15127927502986067408487881 11345945627239550556365911)
        ·
          refine ⟨17018918440859325834548867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11345945627239550556365911 17018918440859325834548867)
          ·
            refine ⟨25528377661288988751823301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17018918440859325834548867 25528377661288988751823301)
            ·
              refine ⟨4786570811491685390966869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25528377661288988751823301 4786570811491685390966869)
              ·
                refine ⟨56092626697168188175393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4786570811491685390966869 56092626697168188175393)
                ·
                  rfl

theorem cell21_737370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_737370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737370 prefixEnd_737370 := by exact prefixLift 737370
  have htrace : WordTrace (prefixWord ++ tailWord_737370) baseStart_737370 baseEnd_737370 := by
    simpa [prefixWord, tailWord_737370, baseEnd_737370] using wordTrace_append hprefix tailTrace_737370
  have hstable : (prefixWord ++ tailWord_737370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737370).length < 2 ^ (prefixWord ++ tailWord_737370).sum := by decide
  have hdescent : baseEnd_737370 < baseStart_737370 := by decide
  rcases family_descends (prefixWord ++ tailWord_737370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737418 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_737418 : Nat := 118140960795 + 737418 * 2 ^ 59
def prefixEnd_737418 : Nat := 4983230072969 + 3 ^ 40 * 737418 * 2
def baseEnd_737418 : Nat := 168288834345467147726081

theorem tailTrace_737418 : CollatzResearch.WordTrace tailWord_737418 prefixEnd_737418 168288834345467147726081 := by
  unfold tailWord_737418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723961010617000453209227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17930562694978667875224605 6723961010617000453209227)
  ·
    refine ⟨10085941515925500679813841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723961010617000453209227 10085941515925500679813841)
    ·
      refine ⟨7564456136944125509860381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10085941515925500679813841 7564456136944125509860381)
      ·
        refine ⟨2836671051354047066197643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7564456136944125509860381 2836671051354047066197643)
        ·
          refine ⟨4255006577031070599296465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836671051354047066197643 4255006577031070599296465)
          ·
            refine ⟨3191254932773302949472349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255006577031070599296465 3191254932773302949472349)
            ·
              refine ⟨1196720599789988606052131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3191254932773302949472349 1196720599789988606052131)
              ·
                refine ⟨1795080899684982909078197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196720599789988606052131 1795080899684982909078197)
                ·
                  refine ⟨168288834345467147726081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795080899684982909078197 168288834345467147726081)
                  ·
                    rfl

theorem cell21_737418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_737418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737418 prefixEnd_737418 := by exact prefixLift 737418
  have htrace : WordTrace (prefixWord ++ tailWord_737418) baseStart_737418 baseEnd_737418 := by
    simpa [prefixWord, tailWord_737418, baseEnd_737418] using wordTrace_append hprefix tailTrace_737418
  have hstable : (prefixWord ++ tailWord_737418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737418).length < 2 ^ (prefixWord ++ tailWord_737418).sum := by decide
  have hdescent : baseEnd_737418 < baseStart_737418 := by decide
  rcases family_descends (prefixWord ++ tailWord_737418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737511 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 3]
def baseStart_737511 : Nat := 118140960795 + 737511 * 2 ^ 59
def prefixEnd_737511 : Nat := 4983230072969 + 3 ^ 40 * 737511 * 2
def baseEnd_737511 : Nat := 168310058212519652675891

theorem tailTrace_737511 : CollatzResearch.WordTrace tailWord_737511 prefixEnd_737511 168310058212519652675891 := by
  unfold tailWord_737511
  simp only [CollatzResearch.WordTrace]
  refine ⟨26899236031131078695972387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17932824020754052463981591 26899236031131078695972387)
  ·
    refine ⟨40348854046696618043958581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26899236031131078695972387 40348854046696618043958581)
    ·
      refine ⟨3782705066877807941621117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40348854046696618043958581 3782705066877807941621117)
      ·
        refine ⟨1418514400079177978107919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3782705066877807941621117 1418514400079177978107919)
        ·
          refine ⟨2127771600118766967161879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418514400079177978107919 2127771600118766967161879)
          ·
            refine ⟨3191657400178150450742819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127771600118766967161879 3191657400178150450742819)
            ·
              refine ⟨4787486100267225676114229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191657400178150450742819 4787486100267225676114229)
              ·
                refine ⟨448826821900052407135709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4787486100267225676114229 448826821900052407135709)
                ·
                  refine ⟨168310058212519652675891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448826821900052407135709 168310058212519652675891)
                  ·
                    rfl

theorem cell21_737511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3].length) (baseStart_737511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737511 prefixEnd_737511 := by exact prefixLift 737511
  have htrace : WordTrace (prefixWord ++ tailWord_737511) baseStart_737511 baseEnd_737511 := by
    simpa [prefixWord, tailWord_737511, baseEnd_737511] using wordTrace_append hprefix tailTrace_737511
  have hstable : (prefixWord ++ tailWord_737511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737511).length < 2 ^ (prefixWord ++ tailWord_737511).sum := by decide
  have hdescent : baseEnd_737511 < baseStart_737511 := by decide
  rcases family_descends (prefixWord ++ tailWord_737511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737553 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_737553 : Nat := 118140960795 + 737553 * 2 ^ 59
def prefixEnd_737553 : Nat := 4983230072969 + 3 ^ 40 * 737553 * 2
def baseEnd_737553 : Nat := 168319643184736912975805

theorem tailTrace_737553 : CollatzResearch.WordTrace tailWord_737553 prefixEnd_737553 168319643184736912975805 := by
  unfold tailWord_737553
  simp only [CollatzResearch.WordTrace]
  refine ⟨26900767896978919869001313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17933845264652613246000875 26900767896978919869001313)
  ·
    refine ⟨20175575922734189901750985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26900767896978919869001313 20175575922734189901750985)
    ·
      refine ⟨15131681942050642426313239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20175575922734189901750985 15131681942050642426313239)
      ·
        refine ⟨22697522913075963639469859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131681942050642426313239 22697522913075963639469859)
        ·
          refine ⟨34046284369613945459204789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22697522913075963639469859 34046284369613945459204789)
          ·
            refine ⟨3191839159651307386800449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34046284369613945459204789 3191839159651307386800449)
            ·
              refine ⟨2393879369738480540100337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191839159651307386800449 2393879369738480540100337)
              ·
                refine ⟨1795409527303860405075253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393879369738480540100337 1795409527303860405075253)
                ·
                  refine ⟨168319643184736912975805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795409527303860405075253 168319643184736912975805)
                  ·
                    rfl

theorem cell21_737553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_737553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737553 prefixEnd_737553 := by exact prefixLift 737553
  have htrace : WordTrace (prefixWord ++ tailWord_737553) baseStart_737553 baseEnd_737553 := by
    simpa [prefixWord, tailWord_737553, baseEnd_737553] using wordTrace_append hprefix tailTrace_737553
  have hstable : (prefixWord ++ tailWord_737553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737553).length < 2 ^ (prefixWord ++ tailWord_737553).sum := by decide
  have hdescent : baseEnd_737553 < baseStart_737553 := by decide
  rcases family_descends (prefixWord ++ tailWord_737553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737587 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 3]
def baseStart_737587 : Nat := 118140960795 + 737587 * 2 ^ 59
def prefixEnd_737587 : Nat := 4983230072969 + 3 ^ 40 * 737587 * 2
def baseEnd_737587 : Nat := 168327402447960409409069

theorem tailTrace_737587 : CollatzResearch.WordTrace tailWord_737587 prefixEnd_737587 168327402447960409409069 := by
  unfold tailWord_737587
  simp only [CollatzResearch.WordTrace]
  refine ⟨26902007978855743675739015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17934671985903829117159343 26902007978855743675739015)
  ·
    refine ⟨40353011968283615513608523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26902007978855743675739015 40353011968283615513608523)
    ·
      refine ⟨60529517952425423270412785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40353011968283615513608523 60529517952425423270412785)
      ·
        refine ⟨45397138464319067452809589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60529517952425423270412785 45397138464319067452809589)
        ·
          refine ⟨4255981731029912573700899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45397138464319067452809589 4255981731029912573700899)
          ·
            refine ⟨6383972596544868860551349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255981731029912573700899 6383972596544868860551349)
            ·
              refine ⟨598497430926081455676689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6383972596544868860551349 598497430926081455676689)
              ·
                refine ⟨448873073194561091757517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598497430926081455676689 448873073194561091757517)
                ·
                  refine ⟨168327402447960409409069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448873073194561091757517 168327402447960409409069)
                  ·
                    rfl

theorem cell21_737587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3].length) (baseStart_737587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737587 prefixEnd_737587 := by exact prefixLift 737587
  have htrace : WordTrace (prefixWord ++ tailWord_737587) baseStart_737587 baseEnd_737587 := by
    simpa [prefixWord, tailWord_737587, baseEnd_737587] using wordTrace_append hprefix tailTrace_737587
  have hstable : (prefixWord ++ tailWord_737587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737587).length < 2 ^ (prefixWord ++ tailWord_737587).sum := by decide
  have hdescent : baseEnd_737587 < baseStart_737587 := by decide
  rcases family_descends (prefixWord ++ tailWord_737587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737694 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_737694 : Nat := 118140960795 + 737694 * 2 ^ 59
def prefixEnd_737694 : Nat := 4983230072969 + 3 ^ 40 * 737694 * 2
def baseEnd_737694 : Nat := 168351821305752001125517

theorem tailTrace_737694 : CollatzResearch.WordTrace tailWord_737694 prefixEnd_737694 168351821305752001125517 := by
  unfold tailWord_737694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363238823683512618735517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17937273726312067299922757 3363238823683512618735517)
  ·
    refine ⟨1261214558881317232025819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3363238823683512618735517 1261214558881317232025819)
    ·
      refine ⟨1891821838321975848038729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261214558881317232025819 1891821838321975848038729)
      ·
        refine ⟨1418866378741481886029047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1891821838321975848038729 1418866378741481886029047)
        ·
          refine ⟨2128299568112222829043571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418866378741481886029047 2128299568112222829043571)
          ·
            refine ⟨3192449352168334243565357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128299568112222829043571 3192449352168334243565357)
            ·
              refine ⟨1197168507063125341337009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3192449352168334243565357 1197168507063125341337009)
              ·
                refine ⟨897876380297344006002757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197168507063125341337009 897876380297344006002757)
                ·
                  refine ⟨168351821305752001125517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897876380297344006002757 168351821305752001125517)
                  ·
                    rfl

theorem cell21_737694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_737694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737694 prefixEnd_737694 := by exact prefixLift 737694
  have htrace : WordTrace (prefixWord ++ tailWord_737694) baseStart_737694 baseEnd_737694 := by
    simpa [prefixWord, tailWord_737694, baseEnd_737694] using wordTrace_append hprefix tailTrace_737694
  have hstable : (prefixWord ++ tailWord_737694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737694).length < 2 ^ (prefixWord ++ tailWord_737694).sum := by decide
  have hdescent : baseEnd_737694 < baseStart_737694 := by decide
  rcases family_descends (prefixWord ++ tailWord_737694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737770 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_737770 : Nat := 118140960795 + 737770 * 2 ^ 59
def prefixEnd_737770 : Nat := 4983230072969 + 3 ^ 40 * 737770 * 2
def baseEnd_737770 : Nat := 168369165541192757858695

theorem tailTrace_737770 : CollatzResearch.WordTrace tailWord_737770 prefixEnd_737770 168369165541192757858695 := by
  unfold tailWord_737770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727170634298191482412691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17939121691461843953100509 6727170634298191482412691)
  ·
    refine ⟨10090755951447287223619037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727170634298191482412691 10090755951447287223619037)
    ·
      refine ⟨3784033481792732708857139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10090755951447287223619037 3784033481792732708857139)
      ·
        refine ⟨5676050222689099063285709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784033481792732708857139 5676050222689099063285709)
        ·
          refine ⟨2128518833508412148732141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5676050222689099063285709 2128518833508412148732141)
          ·
            refine ⟨798194562565654555774553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2128518833508412148732141 798194562565654555774553)
            ·
              refine ⟨598645921924240916830915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798194562565654555774553 598645921924240916830915)
              ·
                refine ⟨897968882886361375246373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598645921924240916830915 897968882886361375246373)
                ·
                  refine ⟨168369165541192757858695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897968882886361375246373 168369165541192757858695)
                  ·
                    rfl

theorem cell21_737770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_737770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737770 prefixEnd_737770 := by exact prefixLift 737770
  have htrace : WordTrace (prefixWord ++ tailWord_737770) baseStart_737770 baseEnd_737770 := by
    simpa [prefixWord, tailWord_737770, baseEnd_737770] using wordTrace_append hprefix tailTrace_737770
  have hstable : (prefixWord ++ tailWord_737770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737770).length < 2 ^ (prefixWord ++ tailWord_737770).sum := by decide
  have hdescent : baseEnd_737770 < baseStart_737770 := by decide
  rcases family_descends (prefixWord ++ tailWord_737770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737840 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_737840 : Nat := 118140960795 + 737840 * 2 ^ 59
def prefixEnd_737840 : Nat := 4983230072969 + 3 ^ 40 * 737840 * 2
def baseEnd_737840 : Nat := 168385140494888191691885

theorem tailTrace_737840 : CollatzResearch.WordTrace tailWord_737840 prefixEnd_737840 168385140494888191691885 := by
  unfold tailWord_737840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455617823469583942349487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17940823764626111923132649 13455617823469583942349487)
  ·
    refine ⟨20183426735204375913524231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13455617823469583942349487 20183426735204375913524231)
    ·
      refine ⟨30275140102806563870286347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20183426735204375913524231 30275140102806563870286347)
      ·
        refine ⟨45412710154209845805429521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30275140102806563870286347 45412710154209845805429521)
        ·
          refine ⟨34059532615657384354072141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45412710154209845805429521 34059532615657384354072141)
          ·
            refine ⟨12772324730871519132777053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34059532615657384354072141 12772324730871519132777053)
            ·
              refine ⟨4789621774076819674791395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12772324730871519132777053 4789621774076819674791395)
              ·
                refine ⟨7184432661115229512187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789621774076819674791395 7184432661115229512187093)
                ·
                  refine ⟨168385140494888191691885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7184432661115229512187093 168385140494888191691885)
                  ·
                    rfl

theorem cell21_737840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_737840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737840 prefixEnd_737840 := by exact prefixLift 737840
  have htrace : WordTrace (prefixWord ++ tailWord_737840) baseStart_737840 baseEnd_737840 := by
    simpa [prefixWord, tailWord_737840, baseEnd_737840] using wordTrace_append hprefix tailTrace_737840
  have hstable : (prefixWord ++ tailWord_737840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737840).length < 2 ^ (prefixWord ++ tailWord_737840).sum := by decide
  have hdescent : baseEnd_737840 < baseStart_737840 := by decide
  rcases family_descends (prefixWord ++ tailWord_737840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737874 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_737874 : Nat := 118140960795 + 737874 * 2 ^ 59
def prefixEnd_737874 : Nat := 4983230072969 + 3 ^ 40 * 737874 * 2
def baseEnd_737874 : Nat := 168392899758111688125149

theorem tailTrace_737874 : CollatzResearch.WordTrace tailWord_737874 prefixEnd_737874 168392899758111688125149 := by
  unfold tailWord_737874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728118932203997922859169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17941650485877327794291117 6728118932203997922859169)
  ·
    refine ⟨5046089199152998442144377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6728118932203997922859169 5046089199152998442144377)
    ·
      refine ⟨3784566899364748831608283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5046089199152998442144377 3784566899364748831608283)
      ·
        refine ⟨5676850349047123247412425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784566899364748831608283 5676850349047123247412425)
        ·
          refine ⟨4257637761785342435559319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5676850349047123247412425 4257637761785342435559319)
          ·
            refine ⟨6386456642678013653338979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257637761785342435559319 6386456642678013653338979)
            ·
              refine ⟨9579684964017020480008469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386456642678013653338979 9579684964017020480008469)
              ·
                refine ⟨449047732688297835000397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9579684964017020480008469 449047732688297835000397)
                ·
                  refine ⟨168392899758111688125149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449047732688297835000397 168392899758111688125149)
                  ·
                    rfl

theorem cell21_737874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_737874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737874 prefixEnd_737874 := by exact prefixLift 737874
  have htrace : WordTrace (prefixWord ++ tailWord_737874) baseStart_737874 baseEnd_737874 := by
    simpa [prefixWord, tailWord_737874, baseEnd_737874] using wordTrace_append hprefix tailTrace_737874
  have hstable : (prefixWord ++ tailWord_737874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737874).length < 2 ^ (prefixWord ++ tailWord_737874).sum := by decide
  have hdescent : baseEnd_737874 < baseStart_737874 := by decide
  rcases family_descends (prefixWord ++ tailWord_737874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737916 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_737916 : Nat := 118140960795 + 737916 * 2 ^ 59
def prefixEnd_737916 : Nat := 4983230072969 + 3 ^ 40 * 737916 * 2
def baseEnd_737916 : Nat := 168402484730328948425063

theorem tailTrace_737916 : CollatzResearch.WordTrace tailWord_737916 prefixEnd_737916 168402484730328948425063 := by
  unfold tailWord_737916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457003797331916432232801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17942671729775888576310401 13457003797331916432232801)
  ·
    refine ⟨10092752847998937324174601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13457003797331916432232801 10092752847998937324174601)
    ·
      refine ⟨7569564635999202993130951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10092752847998937324174601 7569564635999202993130951)
      ·
        refine ⟨11354346953998804489696427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569564635999202993130951 11354346953998804489696427)
        ·
          refine ⟨17031520430998206734544641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11354346953998804489696427 17031520430998206734544641)
          ·
            refine ⟨12773640323248655050908481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17031520430998206734544641 12773640323248655050908481)
            ·
              refine ⟨9580230242436491288181361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12773640323248655050908481 9580230242436491288181361)
              ·
                refine ⟨7185172681827368466136021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9580230242436491288181361 7185172681827368466136021)
                ·
                  refine ⟨168402484730328948425063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7185172681827368466136021 168402484730328948425063)
                  ·
                    rfl

theorem cell21_737916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_737916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_737916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_737916 prefixEnd_737916 := by exact prefixLift 737916
  have htrace : WordTrace (prefixWord ++ tailWord_737916) baseStart_737916 baseEnd_737916 := by
    simpa [prefixWord, tailWord_737916, baseEnd_737916] using wordTrace_append hprefix tailTrace_737916
  have hstable : (prefixWord ++ tailWord_737916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737916).length < 2 ^ (prefixWord ++ tailWord_737916).sum := by decide
  have hdescent : baseEnd_737916 < baseStart_737916 := by decide
  rcases family_descends (prefixWord ++ tailWord_737916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738012 : List Nat := [2, 2, 5, 1, 1, 2, 3, 5]
def baseStart_738012 : Nat := 118140960795 + 738012 * 2 ^ 59
def prefixEnd_738012 : Nat := 4983230072969 + 3 ^ 40 * 738012 * 2
def baseEnd_738012 : Nat := 56141464412751371608289

theorem tailTrace_738012 : CollatzResearch.WordTrace tailWord_738012 prefixEnd_738012 56141464412751371608289 := by
  unfold tailWord_738012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458754501158020629980145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17945006001544027506640193 13458754501158020629980145)
  ·
    refine ⟨10094065875868515472485109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13458754501158020629980145 10094065875868515472485109)
    ·
      refine ⟨946318675862673325545479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10094065875868515472485109 946318675862673325545479)
      ·
        refine ⟨1419478013794009988318219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946318675862673325545479 1419478013794009988318219)
        ·
          refine ⟨2129217020691014982477329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419478013794009988318219 2129217020691014982477329)
          ·
            refine ⟨1596912765518261236857997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129217020691014982477329 1596912765518261236857997)
            ·
              refine ⟨598842287069347963821749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596912765518261236857997 598842287069347963821749)
              ·
                refine ⟨56141464412751371608289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 598842287069347963821749 56141464412751371608289)
                ·
                  rfl

theorem cell21_738012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_738012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738012 prefixEnd_738012 := by exact prefixLift 738012
  have htrace : WordTrace (prefixWord ++ tailWord_738012) baseStart_738012 baseEnd_738012 := by
    simpa [prefixWord, tailWord_738012, baseEnd_738012] using wordTrace_append hprefix tailTrace_738012
  have hstable : (prefixWord ++ tailWord_738012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738012).length < 2 ^ (prefixWord ++ tailWord_738012).sum := by decide
  have hdescent : baseEnd_738012 < baseStart_738012 := by decide
  rcases family_descends (prefixWord ++ tailWord_738012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738077 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 3]
def baseStart_738077 : Nat := 118140960795 + 738077 * 2 ^ 59
def prefixEnd_738077 : Nat := 4983230072969 + 3 ^ 40 * 738077 * 2
def baseEnd_738077 : Nat := 168439227123828446241401

theorem tailTrace_738077 : CollatzResearch.WordTrace tailWord_738077 prefixEnd_738077 168439227123828446241401 := by
  unfold tailWord_738077
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919879747080557361076485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17946586498053704907384323 26919879747080557361076485)
  ·
    refine ⟨5047477452577604505201841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26919879747080557361076485 5047477452577604505201841)
    ·
      refine ⟨3785608089433203378901381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5047477452577604505201841 3785608089433203378901381)
      ·
        refine ⟨709801516768725633544009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3785608089433203378901381 709801516768725633544009)
        ·
          refine ⟨532351137576544225158007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709801516768725633544009 532351137576544225158007)
          ·
            refine ⟨798526706364816337737011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532351137576544225158007 798526706364816337737011)
            ·
              refine ⟨1197790059547224506605517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798526706364816337737011 1197790059547224506605517)
              ·
                refine ⟨449171272330209189977069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197790059547224506605517 449171272330209189977069)
                ·
                  refine ⟨168439227123828446241401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449171272330209189977069 168439227123828446241401)
                  ·
                    rfl

theorem cell21_738077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_738077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738077 prefixEnd_738077 := by exact prefixLift 738077
  have htrace : WordTrace (prefixWord ++ tailWord_738077) baseStart_738077 baseEnd_738077 := by
    simpa [prefixWord, tailWord_738077, baseEnd_738077] using wordTrace_append hprefix tailTrace_738077
  have hstable : (prefixWord ++ tailWord_738077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738077).length < 2 ^ (prefixWord ++ tailWord_738077).sum := by decide
  have hdescent : baseEnd_738077 < baseStart_738077 := by decide
  rcases family_descends (prefixWord ++ tailWord_738077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738099 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_738099 : Nat := 118140960795 + 738099 * 2 ^ 59
def prefixEnd_738099 : Nat := 4983230072969 + 3 ^ 40 * 738099 * 2
def baseEnd_738099 : Nat := 168444247823561296874689

theorem tailTrace_738099 : CollatzResearch.WordTrace tailWord_738099 prefixEnd_738099 168444247823561296874689 := by
  unfold tailWord_738099
  simp only [CollatzResearch.WordTrace]
  refine ⟨26920682153000855118377351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17947121435333903412251567 26920682153000855118377351)
  ·
    refine ⟨40381023229501282677566027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26920682153000855118377351 40381023229501282677566027)
    ·
      refine ⟨60571534844251924016349041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40381023229501282677566027 60571534844251924016349041)
      ·
        refine ⟨45428651133188943012261781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60571534844251924016349041 45428651133188943012261781)
        ·
          refine ⟨2129468021868231703699771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45428651133188943012261781 2129468021868231703699771)
          ·
            refine ⟨3194202032802347555549657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129468021868231703699771 3194202032802347555549657)
            ·
              refine ⟨2395651524601760666662243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194202032802347555549657 2395651524601760666662243)
              ·
                refine ⟨3593477286902640999993365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395651524601760666662243 3593477286902640999993365)
                ·
                  refine ⟨168444247823561296874689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3593477286902640999993365 168444247823561296874689)
                  ·
                    rfl

theorem cell21_738099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_738099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738099 prefixEnd_738099 := by exact prefixLift 738099
  have htrace : WordTrace (prefixWord ++ tailWord_738099) baseStart_738099 baseEnd_738099 := by
    simpa [prefixWord, tailWord_738099, baseEnd_738099] using wordTrace_append hprefix tailTrace_738099
  have hstable : (prefixWord ++ tailWord_738099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738099).length < 2 ^ (prefixWord ++ tailWord_738099).sum := by decide
  have hdescent : baseEnd_738099 < baseStart_738099 := by decide
  rcases family_descends (prefixWord ++ tailWord_738099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738175 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_738175 : Nat := 118140960795 + 738175 * 2 ^ 59
def prefixEnd_738175 : Nat := 4983230072969 + 3 ^ 40 * 738175 * 2
def baseEnd_738175 : Nat := 168461592059002053607867

theorem tailTrace_738175 : CollatzResearch.WordTrace tailWord_738175 prefixEnd_738175 168461592059002053607867 := by
  unfold tailWord_738175
  simp only [CollatzResearch.WordTrace]
  refine ⟨26923454100725520098143979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17948969400483680065429319 26923454100725520098143979)
  ·
    refine ⟨40385181151088280147215969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26923454100725520098143979 40385181151088280147215969)
    ·
      refine ⟨30288885863316210110411977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40385181151088280147215969 30288885863316210110411977)
      ·
        refine ⟨22716664397487157582808983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30288885863316210110411977 22716664397487157582808983)
        ·
          refine ⟨34074996596230736374213475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22716664397487157582808983 34074996596230736374213475)
          ·
            refine ⟨51112494894346104561320213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34074996596230736374213475 51112494894346104561320213)
            ·
              refine ⟨2395898198172473651311885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51112494894346104561320213 2395898198172473651311885)
              ·
                refine ⟨898461824314677619241957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2395898198172473651311885 898461824314677619241957)
                ·
                  refine ⟨168461592059002053607867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898461824314677619241957 168461592059002053607867)
                  ·
                    rfl

theorem cell21_738175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_738175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738175 prefixEnd_738175 := by exact prefixLift 738175
  have htrace : WordTrace (prefixWord ++ tailWord_738175) baseStart_738175 baseEnd_738175 := by
    simpa [prefixWord, tailWord_738175, baseEnd_738175] using wordTrace_append hprefix tailTrace_738175
  have hstable : (prefixWord ++ tailWord_738175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738175).length < 2 ^ (prefixWord ++ tailWord_738175).sum := by decide
  have hdescent : baseEnd_738175 < baseStart_738175 := by decide
  rcases family_descends (prefixWord ++ tailWord_738175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738209 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 4]
def baseStart_738209 : Nat := 118140960795 + 738209 * 2 ^ 59
def prefixEnd_738209 : Nat := 4983230072969 + 3 ^ 40 * 738209 * 2
def baseEnd_738209 : Nat := 168469351322225550041131

theorem tailTrace_738209 : CollatzResearch.WordTrace tailWord_738209 prefixEnd_738209 168469351322225550041131 := by
  unfold tailWord_738209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26924694182602343904881681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17949796121734895936587787 26924694182602343904881681)
  ·
    refine ⟨20193520636951757928661261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26924694182602343904881681 20193520636951757928661261)
    ·
      refine ⟨7572570238856909223247973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20193520636951757928661261 7572570238856909223247973)
      ·
        refine ⟨1419856919785670479358995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7572570238856909223247973 1419856919785670479358995)
        ·
          refine ⟨2129785379678505719038493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419856919785670479358995 2129785379678505719038493)
          ·
            refine ⟨798669517379439644639435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2129785379678505719038493 798669517379439644639435)
            ·
              refine ⟨1198004276069159466959153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798669517379439644639435 1198004276069159466959153)
              ·
                refine ⟨898503207051869600219365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198004276069159466959153 898503207051869600219365)
                ·
                  refine ⟨168469351322225550041131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898503207051869600219365 168469351322225550041131)
                  ·
                    rfl

theorem cell21_738209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_738209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738209 prefixEnd_738209 := by exact prefixLift 738209
  have htrace : WordTrace (prefixWord ++ tailWord_738209) baseStart_738209 baseEnd_738209 := by
    simpa [prefixWord, tailWord_738209, baseEnd_738209] using wordTrace_append hprefix tailTrace_738209
  have hstable : (prefixWord ++ tailWord_738209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738209).length < 2 ^ (prefixWord ++ tailWord_738209).sum := by decide
  have hdescent : baseEnd_738209 < baseStart_738209 := by decide
  rcases family_descends (prefixWord ++ tailWord_738209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738254 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_738254 : Nat := 118140960795 + 738254 * 2 ^ 59
def prefixEnd_738254 : Nat := 4983230072969 + 3 ^ 40 * 738254 * 2
def baseEnd_738254 : Nat := 168479620935315471791039

theorem tailTrace_738254 : CollatzResearch.WordTrace tailWord_738254 prefixEnd_738254 168479620935315471791039 := by
  unfold tailWord_738254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365791933429914573783727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17950890311626211060179877 3365791933429914573783727)
  ·
    refine ⟨5048687900144871860675591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365791933429914573783727 5048687900144871860675591)
    ·
      refine ⟨7573031850217307791013387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048687900144871860675591 7573031850217307791013387)
      ·
        refine ⟨11359547775325961686520081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573031850217307791013387 11359547775325961686520081)
        ·
          refine ⟨8519660831494471264890061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11359547775325961686520081 8519660831494471264890061)
          ·
            refine ⟨3194872811810426724333773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8519660831494471264890061 3194872811810426724333773)
            ·
              refine ⟨1198077304428910021625165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3194872811810426724333773 1198077304428910021625165)
              ·
                refine ⟨449278989160841258109437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198077304428910021625165 449278989160841258109437)
                ·
                  refine ⟨168479620935315471791039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449278989160841258109437 168479620935315471791039)
                  ·
                    rfl

theorem cell21_738254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_738254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738254 prefixEnd_738254 := by exact prefixLift 738254
  have htrace : WordTrace (prefixWord ++ tailWord_738254) baseStart_738254 baseEnd_738254 := by
    simpa [prefixWord, tailWord_738254, baseEnd_738254] using wordTrace_append hprefix tailTrace_738254
  have hstable : (prefixWord ++ tailWord_738254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738254).length < 2 ^ (prefixWord ++ tailWord_738254).sum := by decide
  have hdescent : baseEnd_738254 < baseStart_738254 := by decide
  rcases family_descends (prefixWord ++ tailWord_738254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738265 : List Nat := [1, 2, 1, 2, 5, 1, 9]
def baseStart_738265 : Nat := 118140960795 + 738265 * 2 ^ 59
def prefixEnd_738265 : Nat := 4983230072969 + 3 ^ 40 * 738265 * 2
def baseEnd_738265 : Nat := 18720236809464655234187

theorem tailTrace_738265 : CollatzResearch.WordTrace tailWord_738265 prefixEnd_738265 18720236809464655234187 := by
  unfold tailWord_738265
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926736670399465468920249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17951157780266310312613499 26926736670399465468920249)
  ·
    refine ⟨20195052502799599101690187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26926736670399465468920249 20195052502799599101690187)
    ·
      refine ⟨30292578754199398652535281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195052502799599101690187 30292578754199398652535281)
      ·
        refine ⟨22719434065649548989401461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30292578754199398652535281 22719434065649548989401461)
        ·
          refine ⟨2129946943654645217756387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22719434065649548989401461 2129946943654645217756387)
          ·
            refine ⟨3194920415481967826634581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129946943654645217756387 3194920415481967826634581)
            ·
              refine ⟨18720236809464655234187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3194920415481967826634581 18720236809464655234187)
              ·
                rfl

theorem cell21_738265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 9].length) (baseStart_738265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738265 prefixEnd_738265 := by exact prefixLift 738265
  have htrace : WordTrace (prefixWord ++ tailWord_738265) baseStart_738265 baseEnd_738265 := by
    simpa [prefixWord, tailWord_738265, baseEnd_738265] using wordTrace_append hprefix tailTrace_738265
  have hstable : (prefixWord ++ tailWord_738265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738265).length < 2 ^ (prefixWord ++ tailWord_738265).sum := by decide
  have hdescent : baseEnd_738265 < baseStart_738265 := by decide
  rcases family_descends (prefixWord ++ tailWord_738265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738271 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 3]
def baseStart_738271 : Nat := 118140960795 + 738271 * 2 ^ 59
def prefixEnd_738271 : Nat := 4983230072969 + 3 ^ 40 * 738271 * 2
def baseEnd_738271 : Nat := 168483500566927220007671

theorem tailTrace_738271 : CollatzResearch.WordTrace tailWord_738271 prefixEnd_738271 168483500566927220007671 := by
  unfold tailWord_738271
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926955508377728493638667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17951303672251818995759111 26926955508377728493638667)
  ·
    refine ⟨40390433262566592740458001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26926955508377728493638667 40390433262566592740458001)
    ·
      refine ⟨30292824946924944555343501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40390433262566592740458001 30292824946924944555343501)
      ·
        refine ⟨11359809355096854208253813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30292824946924944555343501 11359809355096854208253813)
        ·
          refine ⟨1064982127040330082023795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11359809355096854208253813 1064982127040330082023795)
          ·
            refine ⟨1597473190560495123035693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064982127040330082023795 1597473190560495123035693)
            ·
              refine ⟨599052446460185671138385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1597473190560495123035693 599052446460185671138385)
              ·
                refine ⟨449289334845139253353789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599052446460185671138385 449289334845139253353789)
                ·
                  refine ⟨168483500566927220007671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449289334845139253353789 168483500566927220007671)
                  ·
                    rfl

theorem cell21_738271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3].length) (baseStart_738271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738271 prefixEnd_738271 := by exact prefixLift 738271
  have htrace : WordTrace (prefixWord ++ tailWord_738271) baseStart_738271 baseEnd_738271 := by
    simpa [prefixWord, tailWord_738271, baseEnd_738271] using wordTrace_append hprefix tailTrace_738271
  have hstable : (prefixWord ++ tailWord_738271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738271).length < 2 ^ (prefixWord ++ tailWord_738271).sum := by decide
  have hdescent : baseEnd_738271 < baseStart_738271 := by decide
  rcases family_descends (prefixWord ++ tailWord_738271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738282 : List Nat := [3, 1, 3, 1, 2, 3, 2, 6]
def baseStart_738282 : Nat := 118140960795 + 738282 * 2 ^ 59
def prefixEnd_738282 : Nat := 4983230072969 + 3 ^ 40 * 738282 * 2
def baseEnd_738282 : Nat := 56162003638931215108105

theorem tailTrace_738282 : CollatzResearch.WordTrace tailWord_738282 prefixEnd_738282 56162003638931215108105 := by
  unfold tailWord_738282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731839177834469343072275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17951571140891918248192733 6731839177834469343072275)
  ·
    refine ⟨10097758766751704014608413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6731839177834469343072275 10097758766751704014608413)
    ·
      refine ⟨3786659537531889005478155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10097758766751704014608413 3786659537531889005478155)
      ·
        refine ⟨5679989306297833508217233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786659537531889005478155 5679989306297833508217233)
        ·
          refine ⟨4259991979723375131162925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679989306297833508217233 4259991979723375131162925)
          ·
            refine ⟨1597496992396265674186097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4259991979723375131162925 1597496992396265674186097)
            ·
              refine ⟨1198122744297199255639573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597496992396265674186097 1198122744297199255639573)
              ·
                refine ⟨56162003638931215108105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198122744297199255639573 56162003638931215108105)
                ·
                  rfl

theorem cell21_738282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_738282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738282 prefixEnd_738282 := by exact prefixLift 738282
  have htrace : WordTrace (prefixWord ++ tailWord_738282) baseStart_738282 baseEnd_738282 := by
    simpa [prefixWord, tailWord_738282, baseEnd_738282] using wordTrace_append hprefix tailTrace_738282
  have hstable : (prefixWord ++ tailWord_738282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738282).length < 2 ^ (prefixWord ++ tailWord_738282).sum := by decide
  have hdescent : baseEnd_738282 < baseStart_738282 := by decide
  rcases family_descends (prefixWord ++ tailWord_738282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738322 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_738322 : Nat := 118140960795 + 738322 * 2 ^ 59
def prefixEnd_738322 : Nat := 4983230072969 + 3 ^ 40 * 738322 * 2
def baseEnd_738322 : Nat := 168495139461762464657567

theorem tailTrace_738322 : CollatzResearch.WordTrace tailWord_738322 prefixEnd_738322 168495139461762464657567 := by
  unfold tailWord_738322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732203907798241050936305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17952543754128642802496813 6732203907798241050936305)
  ·
    refine ⟨5049152930848680788202229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6732203907798241050936305 5049152930848680788202229)
    ·
      refine ⟨473358087267063823893959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5049152930848680788202229 473358087267063823893959)
      ·
        refine ⟨710037130900595735840939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473358087267063823893959 710037130900595735840939)
        ·
          refine ⟨1065055696350893603761409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710037130900595735840939 1065055696350893603761409)
          ·
            refine ⟨798791772263170202821057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065055696350893603761409 798791772263170202821057)
            ·
              refine ⟨599093829197377652115793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798791772263170202821057 599093829197377652115793)
              ·
                refine ⟨449320371898033239086845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599093829197377652115793 449320371898033239086845)
                ·
                  refine ⟨168495139461762464657567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449320371898033239086845 168495139461762464657567)
                  ·
                    rfl

theorem cell21_738322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_738322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738322 prefixEnd_738322 := by exact prefixLift 738322
  have htrace : WordTrace (prefixWord ++ tailWord_738322) baseStart_738322 baseEnd_738322 := by
    simpa [prefixWord, tailWord_738322, baseEnd_738322] using wordTrace_append hprefix tailTrace_738322
  have hstable : (prefixWord ++ tailWord_738322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738322).length < 2 ^ (prefixWord ++ tailWord_738322).sum := by decide
  have hdescent : baseEnd_738322 < baseStart_738322 := by decide
  rcases family_descends (prefixWord ++ tailWord_738322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738389 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 3]
def baseStart_738389 : Nat := 118140960795 + 738389 * 2 ^ 59
def prefixEnd_738389 : Nat := 4983230072969 + 3 ^ 40 * 738389 * 2
def baseEnd_738389 : Nat := 168510429774585237040763

theorem tailTrace_738389 : CollatzResearch.WordTrace tailWord_738389 prefixEnd_738389 168510429774585237040763 := by
  unfold tailWord_738389
  simp only [CollatzResearch.WordTrace]
  refine ⟨26931259321950234646434221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17954172881300156430956147 26931259321950234646434221)
  ·
    refine ⟨10099222245731337992412833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26931259321950234646434221 10099222245731337992412833)
    ·
      refine ⟨7574416684298503494309625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10099222245731337992412833 7574416684298503494309625)
      ·
        refine ⟨5680812513223877620732219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7574416684298503494309625 5680812513223877620732219)
        ·
          refine ⟨8521218769835816431098329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680812513223877620732219 8521218769835816431098329)
          ·
            refine ⟨6390914077376862323323747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8521218769835816431098329 6390914077376862323323747)
            ·
              refine ⟨9586371116065293484985621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390914077376862323323747 9586371116065293484985621)
              ·
                refine ⟨449361146065560632108701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9586371116065293484985621 449361146065560632108701)
                ·
                  refine ⟨168510429774585237040763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449361146065560632108701 168510429774585237040763)
                  ·
                    rfl

theorem cell21_738389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_738389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738389 prefixEnd_738389 := by exact prefixLift 738389
  have htrace : WordTrace (prefixWord ++ tailWord_738389) baseStart_738389 baseEnd_738389 := by
    simpa [prefixWord, tailWord_738389, baseEnd_738389] using wordTrace_append hprefix tailTrace_738389
  have hstable : (prefixWord ++ tailWord_738389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738389).length < 2 ^ (prefixWord ++ tailWord_738389).sum := by decide
  have hdescent : baseEnd_738389 < baseStart_738389 := by decide
  rcases family_descends (prefixWord ++ tailWord_738389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738496 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_738496 : Nat := 118140960795 + 738496 * 2 ^ 59
def prefixEnd_738496 : Nat := 4983230072969 + 3 ^ 40 * 738496 * 2
def baseEnd_738496 : Nat := 168534848632376828757211

theorem tailTrace_738496 : CollatzResearch.WordTrace tailWord_738496 prefixEnd_738496 168534848632376828757211 := by
  unfold tailWord_738496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467580966281295960289671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17956774621708394613719561 13467580966281295960289671)
  ·
    refine ⟨20201371449421943940434507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13467580966281295960289671 20201371449421943940434507)
    ·
      refine ⟨30302057174132915910651761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20201371449421943940434507 30302057174132915910651761)
      ·
        refine ⟨22726542880599686932988821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30302057174132915910651761 22726542880599686932988821)
        ·
          refine ⟨1065306697528110324983851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22726542880599686932988821 1065306697528110324983851)
          ·
            refine ⟨1597960046292165487475777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065306697528110324983851 1597960046292165487475777)
            ·
              refine ⟨1198470034719124115606833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597960046292165487475777 1198470034719124115606833)
              ·
                refine ⟨898852526039343086705125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198470034719124115606833 898852526039343086705125)
                ·
                  refine ⟨168534848632376828757211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898852526039343086705125 168534848632376828757211)
                  ·
                    rfl

theorem cell21_738496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_738496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738496 prefixEnd_738496 := by exact prefixLift 738496
  have htrace : WordTrace (prefixWord ++ tailWord_738496) baseStart_738496 baseEnd_738496 := by
    simpa [prefixWord, tailWord_738496, baseEnd_738496] using wordTrace_append hprefix tailTrace_738496
  have hstable : (prefixWord ++ tailWord_738496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738496).length < 2 ^ (prefixWord ++ tailWord_738496).sum := by decide
  have hdescent : baseEnd_738496 < baseStart_738496 := by decide
  rcases family_descends (prefixWord ++ tailWord_738496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738502 : List Nat := [6, 1, 2, 2, 2, 1, 1, 6]
def baseStart_738502 : Nat := 118140960795 + 738502 * 2 ^ 59
def prefixEnd_738502 : Nat := 4983230072969 + 3 ^ 40 * 738502 * 2
def baseEnd_738502 : Nat := 56178739304707383885733

theorem tailTrace_738502 : CollatzResearch.WordTrace tailWord_738502 prefixEnd_738502 56178739304707383885733 := by
  unfold tailWord_738502
  simp only [CollatzResearch.WordTrace]
  refine ⟨841730649079401717040555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17956920513693903296865173 841730649079401717040555)
  ·
    refine ⟨1262595973619102575560833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841730649079401717040555 1262595973619102575560833)
    ·
      refine ⟨946946980214326931670625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262595973619102575560833 946946980214326931670625)
      ·
        refine ⟨710210235160745198752969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 946946980214326931670625 710210235160745198752969)
        ·
          refine ⟨532657676370558899064727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710210235160745198752969 532657676370558899064727)
          ·
            refine ⟨798986514555838348597091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532657676370558899064727 798986514555838348597091)
            ·
              refine ⟨1198479771833757522895637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798986514555838348597091 1198479771833757522895637)
              ·
                refine ⟨56178739304707383885733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198479771833757522895637 56178739304707383885733)
                ·
                  rfl

theorem cell21_738502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_738502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738502 prefixEnd_738502 := by exact prefixLift 738502
  have htrace : WordTrace (prefixWord ++ tailWord_738502) baseStart_738502 baseEnd_738502 := by
    simpa [prefixWord, tailWord_738502, baseEnd_738502] using wordTrace_append hprefix tailTrace_738502
  have hstable : (prefixWord ++ tailWord_738502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738502).length < 2 ^ (prefixWord ++ tailWord_738502).sum := by decide
  have hdescent : baseEnd_738502 < baseStart_738502 := by decide
  rcases family_descends (prefixWord ++ tailWord_738502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738558 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_738558 : Nat := 118140960795 + 738558 * 2 ^ 59
def prefixEnd_738558 : Nat := 4983230072969 + 3 ^ 40 * 738558 * 2
def baseEnd_738558 : Nat := 168548997877078498723751

theorem tailTrace_738558 : CollatzResearch.WordTrace tailWord_738558 prefixEnd_738558 168548997877078498723751 := by
  unfold tailWord_738558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367177907292247063667041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17958282172225317672890885 3367177907292247063667041)
  ·
    refine ⟨2525383430469185297750281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3367177907292247063667041 2525383430469185297750281)
    ·
      refine ⟨1894037572851888973312711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2525383430469185297750281 1894037572851888973312711)
      ·
        refine ⟨2841056359277833459969067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894037572851888973312711 2841056359277833459969067)
        ·
          refine ⟨4261584538916750189953601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841056359277833459969067 4261584538916750189953601)
          ·
            refine ⟨3196188404187562642465201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261584538916750189953601 3196188404187562642465201)
            ·
              refine ⟨2397141303140671981848901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3196188404187562642465201 2397141303140671981848901)
              ·
                refine ⟨449463994338875996596669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2397141303140671981848901 449463994338875996596669)
                ·
                  refine ⟨168548997877078498723751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449463994338875996596669 168548997877078498723751)
                  ·
                    rfl

theorem cell21_738558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_738558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738558 prefixEnd_738558 := by exact prefixLift 738558
  have htrace : WordTrace (prefixWord ++ tailWord_738558) baseStart_738558 baseEnd_738558 := by
    simpa [prefixWord, tailWord_738558, baseEnd_738558] using wordTrace_append hprefix tailTrace_738558
  have hstable : (prefixWord ++ tailWord_738558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738558).length < 2 ^ (prefixWord ++ tailWord_738558).sum := by decide
  have hdescent : baseEnd_738558 < baseStart_738558 := by decide
  rcases family_descends (prefixWord ++ tailWord_738558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738572 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_738572 : Nat := 118140960795 + 738572 * 2 ^ 59
def prefixEnd_738572 : Nat := 4983230072969 + 3 ^ 40 * 738572 * 2
def baseEnd_738572 : Nat := 168552192867817585490389

theorem tailTrace_738572 : CollatzResearch.WordTrace tailWord_738572 prefixEnd_738572 168552192867817585490389 := by
  unfold tailWord_738572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468966940143628450172985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17958622586858171266897313 13468966940143628450172985)
  ·
    refine ⟨10101725205107721337629739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13468966940143628450172985 10101725205107721337629739)
    ·
      refine ⟨15152587807661582006444609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101725205107721337629739 15152587807661582006444609)
      ·
        refine ⟨11364440855746186504833457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15152587807661582006444609 11364440855746186504833457)
        ·
          refine ⟨8523330641809639878625093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11364440855746186504833457 8523330641809639878625093)
          ·
            refine ⟨1598124495339307477242205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8523330641809639878625093 1598124495339307477242205)
            ·
              refine ⟨599296685752240303965827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1598124495339307477242205 599296685752240303965827)
              ·
                refine ⟨898945028628360455948741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599296685752240303965827 898945028628360455948741)
                ·
                  refine ⟨168552192867817585490389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898945028628360455948741 168552192867817585490389)
                  ·
                    rfl

theorem cell21_738572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_738572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738572 prefixEnd_738572 := by exact prefixLift 738572
  have htrace : WordTrace (prefixWord ++ tailWord_738572) baseStart_738572 baseEnd_738572 := by
    simpa [prefixWord, tailWord_738572, baseEnd_738572] using wordTrace_append hprefix tailTrace_738572
  have hstable : (prefixWord ++ tailWord_738572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738572).length < 2 ^ (prefixWord ++ tailWord_738572).sum := by decide
  have hdescent : baseEnd_738572 < baseStart_738572 := by decide
  rcases family_descends (prefixWord ++ tailWord_738572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738586 : List Nat := [3, 1, 1, 3, 3, 1, 4, 5]
def baseStart_738586 : Nat := 118140960795 + 738586 * 2 ^ 59
def prefixEnd_738586 : Nat := 4983230072969 + 3 ^ 40 * 738586 * 2
def baseEnd_738586 : Nat := 56185129286185557419009

theorem tailTrace_738586 : CollatzResearch.WordTrace tailWord_738586 prefixEnd_738586 56185129286185557419009 := by
  unfold tailWord_738586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734611125559134322838903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17958963001491024860903741 6734611125559134322838903)
  ·
    refine ⟨10101916688338701484258355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6734611125559134322838903 10101916688338701484258355)
    ·
      refine ⟨15152875032508052226387533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101916688338701484258355 15152875032508052226387533)
      ·
        refine ⟨5682328137190519584895325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15152875032508052226387533 5682328137190519584895325)
        ·
          refine ⟨2130873051446444844335747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5682328137190519584895325 2130873051446444844335747)
          ·
            refine ⟨3196309577169667266503621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130873051446444844335747 3196309577169667266503621)
            ·
              refine ⟨599308045719312612469429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3196309577169667266503621 599308045719312612469429)
              ·
                refine ⟨56185129286185557419009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 599308045719312612469429 56185129286185557419009)
                ·
                  rfl

theorem cell21_738586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_738586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738586 prefixEnd_738586 := by exact prefixLift 738586
  have htrace : WordTrace (prefixWord ++ tailWord_738586) baseStart_738586 baseEnd_738586 := by
    simpa [prefixWord, tailWord_738586, baseEnd_738586] using wordTrace_append hprefix tailTrace_738586
  have hstable : (prefixWord ++ tailWord_738586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738586).length < 2 ^ (prefixWord ++ tailWord_738586).sum := by decide
  have hdescent : baseEnd_738586 < baseStart_738586 := by decide
  rcases family_descends (prefixWord ++ tailWord_738586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738631 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_738631 : Nat := 118140960795 + 738631 * 2 ^ 59
def prefixEnd_738631 : Nat := 4983230072969 + 3 ^ 40 * 738631 * 2
def baseEnd_738631 : Nat := 168565657471646594006935

theorem tailTrace_738631 : CollatzResearch.WordTrace tailWord_738631 prefixEnd_738631 168565657471646594006935 := by
  unfold tailWord_738631
  simp only [CollatzResearch.WordTrace]
  refine ⟨26940085787073509976743747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17960057191382339984495831 26940085787073509976743747)
  ·
    refine ⟨40410128680610264965115621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26940085787073509976743747 40410128680610264965115621)
    ·
      refine ⟨7576899127614424680959179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40410128680610264965115621 7576899127614424680959179)
      ·
        refine ⟨11365348691421637021438769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576899127614424680959179 11365348691421637021438769)
        ·
          refine ⟨8524011518566227766079077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11365348691421637021438769 8524011518566227766079077)
          ·
            refine ⟨1598252159731167706139827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8524011518566227766079077 1598252159731167706139827)
            ·
              refine ⟨2397378239596751559209741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598252159731167706139827 2397378239596751559209741)
              ·
                refine ⟨899016839848781834703653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2397378239596751559209741 899016839848781834703653)
                ·
                  refine ⟨168565657471646594006935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899016839848781834703653 168565657471646594006935)
                  ·
                    rfl

theorem cell21_738631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_738631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738631 prefixEnd_738631 := by exact prefixLift 738631
  have htrace : WordTrace (prefixWord ++ tailWord_738631) baseStart_738631 baseEnd_738631 := by
    simpa [prefixWord, tailWord_738631, baseEnd_738631] using wordTrace_append hprefix tailTrace_738631
  have hstable : (prefixWord ++ tailWord_738631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738631).length < 2 ^ (prefixWord ++ tailWord_738631).sum := by decide
  have hdescent : baseEnd_738631 < baseStart_738631 := by decide
  rcases family_descends (prefixWord ++ tailWord_738631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738645 : List Nat := [1, 3, 2, 2, 3, 1, 2, 7]
def baseStart_738645 : Nat := 118140960795 + 738645 * 2 ^ 59
def prefixEnd_738645 : Nat := 4983230072969 + 3 ^ 40 * 738645 * 2
def baseEnd_738645 : Nat := 56189617487461893591191

theorem tailTrace_738645 : CollatzResearch.WordTrace tailWord_738645 prefixEnd_738645 56189617487461893591191 := by
  unfold tailWord_738645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26940596409022790367753389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17960397606015193578502259 26940596409022790367753389)
  ·
    refine ⟨10102723653383546387907521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26940596409022790367753389 10102723653383546387907521)
    ·
      refine ⟨7577042740037659790930641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10102723653383546387907521 7577042740037659790930641)
      ·
        refine ⟨5682782055028244843197981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577042740037659790930641 5682782055028244843197981)
        ·
          refine ⟨2131043270635591816199243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5682782055028244843197981 2131043270635591816199243)
          ·
            refine ⟨3196564905953387724298865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131043270635591816199243 3196564905953387724298865)
            ·
              refine ⟨2397423679465040793224149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3196564905953387724298865 2397423679465040793224149)
              ·
                refine ⟨56189617487461893591191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2397423679465040793224149 56189617487461893591191)
                ·
                  rfl

theorem cell21_738645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_738645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738645 prefixEnd_738645 := by exact prefixLift 738645
  have htrace : WordTrace (prefixWord ++ tailWord_738645) baseStart_738645 baseEnd_738645 := by
    simpa [prefixWord, tailWord_738645, baseEnd_738645] using wordTrace_append hprefix tailTrace_738645
  have hstable : (prefixWord ++ tailWord_738645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738645).length < 2 ^ (prefixWord ++ tailWord_738645).sum := by decide
  have hdescent : baseEnd_738645 < baseStart_738645 := by decide
  rcases family_descends (prefixWord ++ tailWord_738645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738766 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_738766 : Nat := 118140960795 + 738766 * 2 ^ 59
def prefixEnd_738766 : Nat := 4983230072969 + 3 ^ 40 * 738766 * 2
def baseEnd_738766 : Nat := 168596466310916359256659

theorem tailTrace_738766 : CollatzResearch.WordTrace tailWord_738766 prefixEnd_738766 168596466310916359256659 := by
  unfold tailWord_738766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368126205198053504113519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17963339761056285355272101 3368126205198053504113519)
  ·
    refine ⟨5052189307797080256170279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368126205198053504113519 5052189307797080256170279)
    ·
      refine ⟨7578283961695620384255419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052189307797080256170279 7578283961695620384255419)
      ·
        refine ⟨11367425942543430576383129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578283961695620384255419 11367425942543430576383129)
        ·
          refine ⟨8525569456907572932287347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11367425942543430576383129 8525569456907572932287347)
          ·
            refine ⟨12788354185361359398431021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8525569456907572932287347 12788354185361359398431021)
            ·
              refine ⟨4795632819510509774411633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12788354185361359398431021 4795632819510509774411633)
              ·
                refine ⟨3596724614632882330808725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795632819510509774411633 3596724614632882330808725)
                ·
                  refine ⟨168596466310916359256659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3596724614632882330808725 168596466310916359256659)
                  ·
                    rfl

theorem cell21_738766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_738766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738766 prefixEnd_738766 := by exact prefixLift 738766
  have htrace : WordTrace (prefixWord ++ tailWord_738766) baseStart_738766 baseEnd_738766 := by
    simpa [prefixWord, tailWord_738766, baseEnd_738766] using wordTrace_append hprefix tailTrace_738766
  have hstable : (prefixWord ++ tailWord_738766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738766).length < 2 ^ (prefixWord ++ tailWord_738766).sum := by decide
  have hdescent : baseEnd_738766 < baseStart_738766 := by decide
  rcases family_descends (prefixWord ++ tailWord_738766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738800 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_738800 : Nat := 118140960795 + 738800 * 2 ^ 59
def prefixEnd_738800 : Nat := 4983230072969 + 3 ^ 40 * 738800 * 2
def baseEnd_738800 : Nat := 168604225574139855689923

theorem tailTrace_738800 : CollatzResearch.WordTrace tailWord_738800 prefixEnd_738800 168604225574139855689923 := by
  unfold tailWord_738800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473124861730625919822927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17964166482307501226430569 13473124861730625919822927)
  ·
    refine ⟨20209687292595938879734391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13473124861730625919822927 20209687292595938879734391)
    ·
      refine ⟨30314530938893908319601587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20209687292595938879734391 30314530938893908319601587)
      ·
        refine ⟨45471796408340862479402381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30314530938893908319601587 45471796408340862479402381)
        ·
          refine ⟨17051923653127823429775893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45471796408340862479402381 17051923653127823429775893)
          ·
            refine ⟨799308921240366723270745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17051923653127823429775893 799308921240366723270745)
            ·
              refine ⟨599481690930275042453059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799308921240366723270745 599481690930275042453059)
              ·
                refine ⟨899222536395412563679589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599481690930275042453059 899222536395412563679589)
                ·
                  refine ⟨168604225574139855689923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899222536395412563679589 168604225574139855689923)
                  ·
                    rfl

theorem cell21_738800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_738800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738800 prefixEnd_738800 := by exact prefixLift 738800
  have htrace : WordTrace (prefixWord ++ tailWord_738800) baseStart_738800 baseEnd_738800 := by
    simpa [prefixWord, tailWord_738800, baseEnd_738800] using wordTrace_append hprefix tailTrace_738800
  have hstable : (prefixWord ++ tailWord_738800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738800).length < 2 ^ (prefixWord ++ tailWord_738800).sum := by decide
  have hdescent : baseEnd_738800 < baseStart_738800 := by decide
  rcases family_descends (prefixWord ++ tailWord_738800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738845 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 3]
def baseStart_738845 : Nat := 118140960795 + 738845 * 2 ^ 59
def prefixEnd_738845 : Nat := 4983230072969 + 3 ^ 40 * 738845 * 2
def baseEnd_738845 : Nat := 168614495187229777439831

theorem tailTrace_738845 : CollatzResearch.WordTrace tailWord_738845 prefixEnd_738845 168614495187229777439831 := by
  unfold tailWord_738845
  simp only [CollatzResearch.WordTrace]
  refine ⟨26947891008298224525033989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17965260672198816350022659 26947891008298224525033989)
  ·
    refine ⟨5052729564055917098443873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26947891008298224525033989 5052729564055917098443873)
    ·
      refine ⟨3789547173041937823832905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5052729564055917098443873 3789547173041937823832905)
      ·
        refine ⟨2842160379781453367874679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789547173041937823832905 2842160379781453367874679)
        ·
          refine ⟨4263240569672180051812019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842160379781453367874679 4263240569672180051812019)
          ·
            refine ⟨6394860854508270077718029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263240569672180051812019 6394860854508270077718029)
            ·
              refine ⟨2398072820440601279144261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6394860854508270077718029 2398072820440601279144261)
              ·
                refine ⟨449638653832612739839549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2398072820440601279144261 449638653832612739839549)
                ·
                  refine ⟨168614495187229777439831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449638653832612739839549 168614495187229777439831)
                  ·
                    rfl

theorem cell21_738845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_738845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738845 prefixEnd_738845 := by exact prefixLift 738845
  have htrace : WordTrace (prefixWord ++ tailWord_738845) baseStart_738845 baseEnd_738845 := by
    simpa [prefixWord, tailWord_738845, baseEnd_738845] using wordTrace_append hprefix tailTrace_738845
  have hstable : (prefixWord ++ tailWord_738845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738845).length < 2 ^ (prefixWord ++ tailWord_738845).sum := by decide
  have hdescent : baseEnd_738845 < baseStart_738845 := by decide
  rcases family_descends (prefixWord ++ tailWord_738845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738893 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 4]
def baseStart_738893 : Nat := 118140960795 + 738893 * 2 ^ 59
def prefixEnd_738893 : Nat := 4983230072969 + 3 ^ 40 * 738893 * 2
def baseEnd_738893 : Nat := 168625449441192360639733

theorem tailTrace_738893 : CollatzResearch.WordTrace tailWord_738893 prefixEnd_738893 168625449441192360639733 := by
  unfold tailWord_738893
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949641712124328722781333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17966427808082885815187555 26949641712124328722781333)
  ·
    refine ⟨1263264455255827908880375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26949641712124328722781333 1263264455255827908880375)
    ·
      refine ⟨1894896682883741863320563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263264455255827908880375 1894896682883741863320563)
      ·
        refine ⟨2842345024325612794980845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894896682883741863320563 2842345024325612794980845)
        ·
          refine ⟨1065879384122104798117817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2842345024325612794980845 1065879384122104798117817)
          ·
            refine ⟨799409538091578598588363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065879384122104798117817 799409538091578598588363)
            ·
              refine ⟨1199114307137367897882545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799409538091578598588363 1199114307137367897882545)
              ·
                refine ⟨899335730353025923411909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199114307137367897882545 899335730353025923411909)
                ·
                  refine ⟨168625449441192360639733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899335730353025923411909 168625449441192360639733)
                  ·
                    rfl

theorem cell21_738893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_738893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_738893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_738893 prefixEnd_738893 := by exact prefixLift 738893
  have htrace : WordTrace (prefixWord ++ tailWord_738893) baseStart_738893 baseEnd_738893 := by
    simpa [prefixWord, tailWord_738893, baseEnd_738893] using wordTrace_append hprefix tailTrace_738893
  have hstable : (prefixWord ++ tailWord_738893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738893).length < 2 ^ (prefixWord ++ tailWord_738893).sum := by decide
  have hdescent : baseEnd_738893 < baseStart_738893 := by decide
  rcases family_descends (prefixWord ++ tailWord_738893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739025 : List Nat := [1, 2, 2, 1, 2, 6, 1, 6]
def baseStart_739025 : Nat := 118140960795 + 739025 * 2 ^ 59
def prefixEnd_739025 : Nat := 4983230072969 + 3 ^ 40 * 739025 * 2
def baseEnd_739025 : Nat := 56218524546529821479821

theorem tailTrace_739025 : CollatzResearch.WordTrace tailWord_739025 prefixEnd_739025 56218524546529821479821 := by
  unfold tailWord_739025
  simp only [CollatzResearch.WordTrace]
  refine ⟨26954456147646115266586529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17969637431764076844391019 26954456147646115266586529)
  ·
    refine ⟨20215842110734586449939897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26954456147646115266586529 20215842110734586449939897)
    ·
      refine ⟨15161881583050939837454923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215842110734586449939897 15161881583050939837454923)
      ·
        refine ⟨22742822374576409756182385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15161881583050939837454923 22742822374576409756182385)
        ·
          refine ⟨17057116780932307317136789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22742822374576409756182385 17057116780932307317136789)
          ·
            refine ⟨799552349106201905490787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17057116780932307317136789 799552349106201905490787)
            ·
              refine ⟨1199328523659302858236181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799552349106201905490787 1199328523659302858236181)
              ·
                refine ⟨56218524546529821479821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1199328523659302858236181 56218524546529821479821)
                ·
                  rfl

theorem cell21_739025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 6].length) (baseStart_739025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739025 prefixEnd_739025 := by exact prefixLift 739025
  have htrace : WordTrace (prefixWord ++ tailWord_739025) baseStart_739025 baseEnd_739025 := by
    simpa [prefixWord, tailWord_739025, baseEnd_739025] using wordTrace_append hprefix tailTrace_739025
  have hstable : (prefixWord ++ tailWord_739025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739025).length < 2 ^ (prefixWord ++ tailWord_739025).sum := by decide
  have hdescent : baseEnd_739025 < baseStart_739025 := by decide
  rcases family_descends (prefixWord ++ tailWord_739025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739039 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_739039 : Nat := 118140960795 + 739039 * 2 ^ 59
def prefixEnd_739039 : Nat := 4983230072969 + 3 ^ 40 * 739039 * 2
def baseEnd_739039 : Nat := 168658768630328551206101

theorem tailTrace_739039 : CollatzResearch.WordTrace tailWord_739039 prefixEnd_739039 168658768630328551206101 := by
  unfold tailWord_739039
  simp only [CollatzResearch.WordTrace]
  refine ⟨26954966769595395657596171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17969977846396930438397447 26954966769595395657596171)
  ·
    refine ⟨40432450154393093486394257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26954966769595395657596171 40432450154393093486394257)
    ·
      refine ⟨30324337615794820114795693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40432450154393093486394257 30324337615794820114795693)
      ·
        refine ⟨11371626605923057543048385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30324337615794820114795693 11371626605923057543048385)
        ·
          refine ⟨8528719954442293157286289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11371626605923057543048385 8528719954442293157286289)
          ·
            refine ⟨6396539965831719867964717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528719954442293157286289 6396539965831719867964717)
            ·
              refine ⟨2398702487186894950486769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6396539965831719867964717 2398702487186894950486769)
              ·
                refine ⟨1799026865390171212865077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398702487186894950486769 1799026865390171212865077)
                ·
                  refine ⟨168658768630328551206101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799026865390171212865077 168658768630328551206101)
                  ·
                    rfl

theorem cell21_739039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_739039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739039 prefixEnd_739039 := by exact prefixLift 739039
  have htrace : WordTrace (prefixWord ++ tailWord_739039) baseStart_739039 baseEnd_739039 := by
    simpa [prefixWord, tailWord_739039, baseEnd_739039] using wordTrace_append hprefix tailTrace_739039
  have hstable : (prefixWord ++ tailWord_739039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739039).length < 2 ^ (prefixWord ++ tailWord_739039).sum := by decide
  have hdescent : baseEnd_739039 < baseStart_739039 := by decide
  rcases family_descends (prefixWord ++ tailWord_739039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739118 : List Nat := [4, 1, 3, 2, 2, 2, 7]
def baseStart_739118 : Nat := 118140960795 + 739118 * 2 ^ 59
def prefixEnd_739118 : Nat := 4983230072969 + 3 ^ 40 * 739118 * 2
def baseEnd_739118 : Nat := 18741866389626885487697

theorem tailTrace_739118 : CollatzResearch.WordTrace tailWord_739118 prefixEnd_739118 18741866389626885487697 := by
  unfold tailWord_739118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369731017038649018715251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17971898757539461433148005 3369731017038649018715251)
  ·
    refine ⟨5054596525557973528072877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369731017038649018715251 5054596525557973528072877)
    ·
      refine ⟨1895473697084240073027329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5054596525557973528072877 1895473697084240073027329)
      ·
        refine ⟨1421605272813180054770497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895473697084240073027329 1421605272813180054770497)
        ·
          refine ⟨1066203954609885041077873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421605272813180054770497 1066203954609885041077873)
          ·
            refine ⟨799652965957413780808405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066203954609885041077873 799652965957413780808405)
            ·
              refine ⟨18741866389626885487697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 799652965957413780808405 18741866389626885487697)
              ·
                rfl

theorem cell21_739118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 7].length) (baseStart_739118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739118 prefixEnd_739118 := by exact prefixLift 739118
  have htrace : WordTrace (prefixWord ++ tailWord_739118) baseStart_739118 baseEnd_739118 := by
    simpa [prefixWord, tailWord_739118, baseEnd_739118] using wordTrace_append hprefix tailTrace_739118
  have hstable : (prefixWord ++ tailWord_739118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739118).length < 2 ^ (prefixWord ++ tailWord_739118).sum := by decide
  have hdescent : baseEnd_739118 < baseStart_739118 := by decide
  rcases family_descends (prefixWord ++ tailWord_739118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739132 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_739132 : Nat := 118140960795 + 739132 * 2 ^ 59
def prefixEnd_739132 : Nat := 4983230072969 + 3 ^ 40 * 739132 * 2
def baseEnd_739132 : Nat := 168679992497381056155911

theorem tailTrace_739132 : CollatzResearch.WordTrace tailWord_739132 prefixEnd_739132 168679992497381056155911 := by
  unfold tailWord_739132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13479179379129236270365825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17972239172172315027154433 13479179379129236270365825)
  ·
    refine ⟨10109384534346927202774369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13479179379129236270365825 10109384534346927202774369)
    ·
      refine ⟨7582038400760195402080777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10109384534346927202774369 7582038400760195402080777)
      ·
        refine ⟨5686528800570146551560583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7582038400760195402080777 5686528800570146551560583)
        ·
          refine ⟨8529793200855219827340875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686528800570146551560583 8529793200855219827340875)
          ·
            refine ⟨12794689801282829741011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529793200855219827340875 12794689801282829741011313)
            ·
              refine ⟨9596017350962122305758485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794689801282829741011313 9596017350962122305758485)
              ·
                refine ⟨449813313326349483082429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9596017350962122305758485 449813313326349483082429)
                ·
                  refine ⟨168679992497381056155911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449813313326349483082429 168679992497381056155911)
                  ·
                    rfl

theorem cell21_739132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_739132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739132 prefixEnd_739132 := by exact prefixLift 739132
  have htrace : WordTrace (prefixWord ++ tailWord_739132) baseStart_739132 baseEnd_739132 := by
    simpa [prefixWord, tailWord_739132, baseEnd_739132] using wordTrace_append hprefix tailTrace_739132
  have hstable : (prefixWord ++ tailWord_739132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739132).length < 2 ^ (prefixWord ++ tailWord_739132).sum := by decide
  have hdescent : baseEnd_739132 < baseStart_739132 := by decide
  rcases family_descends (prefixWord ++ tailWord_739132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739146 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_739146 : Nat := 118140960795 + 739146 * 2 ^ 59
def prefixEnd_739146 : Nat := 4983230072969 + 3 ^ 40 * 739146 * 2
def baseEnd_739146 : Nat := 168683187488120142922549

theorem tailTrace_739146 : CollatzResearch.WordTrace tailWord_739146 prefixEnd_739146 168683187488120142922549 := by
  unfold tailWord_739146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739717345051938232935323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17972579586805168621160861 6739717345051938232935323)
  ·
    refine ⟨10109576017577907349402985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6739717345051938232935323 10109576017577907349402985)
    ·
      refine ⟨7582182013183430512052239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10109576017577907349402985 7582182013183430512052239)
      ·
        refine ⟨11373273019775145768078359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582182013183430512052239 11373273019775145768078359)
        ·
          refine ⟨17059909529662718652117539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11373273019775145768078359 17059909529662718652117539)
          ·
            refine ⟨25589864294494077978176309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17059909529662718652117539 25589864294494077978176309)
            ·
              refine ⟨2399049777608819810454029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25589864294494077978176309 2399049777608819810454029)
              ·
                refine ⟨899643666603307428920261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2399049777608819810454029 899643666603307428920261)
                ·
                  refine ⟨168683187488120142922549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899643666603307428920261 168683187488120142922549)
                  ·
                    rfl

theorem cell21_739146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_739146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739146 prefixEnd_739146 := by exact prefixLift 739146
  have htrace : WordTrace (prefixWord ++ tailWord_739146) baseStart_739146 baseEnd_739146 := by
    simpa [prefixWord, tailWord_739146, baseEnd_739146] using wordTrace_append hprefix tailTrace_739146
  have hstable : (prefixWord ++ tailWord_739146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739146).length < 2 ^ (prefixWord ++ tailWord_739146).sum := by decide
  have hdescent : baseEnd_739146 < baseStart_739146 := by decide
  rcases family_descends (prefixWord ++ tailWord_739146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739208 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_739208 : Nat := 118140960795 + 739208 * 2 ^ 59
def prefixEnd_739208 : Nat := 4983230072969 + 3 ^ 40 * 739208 * 2
def baseEnd_739208 : Nat := 168697336732821812889089

theorem tailTrace_739208 : CollatzResearch.WordTrace tailWord_739208 prefixEnd_739208 168697336732821812889089 := by
  unfold tailWord_739208
  simp only [CollatzResearch.WordTrace]
  refine ⟨13480565352991568760249139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17974087137322091680332185 13480565352991568760249139)
  ·
    refine ⟨20220848029487353140373709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13480565352991568760249139 20220848029487353140373709)
    ·
      refine ⟨7582818011057757427640141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20220848029487353140373709 7582818011057757427640141)
      ·
        refine ⟨2843556754146659035365053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7582818011057757427640141 2843556754146659035365053)
        ·
          refine ⟨1066333782804997138261895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2843556754146659035365053 1066333782804997138261895)
          ·
            refine ⟨1599500674207495707392843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066333782804997138261895 1599500674207495707392843)
            ·
              refine ⟨2399251011311243561089265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599500674207495707392843 2399251011311243561089265)
              ·
                refine ⟨1799438258483432670816949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399251011311243561089265 1799438258483432670816949)
                ·
                  refine ⟨168697336732821812889089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799438258483432670816949 168697336732821812889089)
                  ·
                    rfl

theorem cell21_739208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_739208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739208 prefixEnd_739208 := by exact prefixLift 739208
  have htrace : WordTrace (prefixWord ++ tailWord_739208) baseStart_739208 baseEnd_739208 := by
    simpa [prefixWord, tailWord_739208, baseEnd_739208] using wordTrace_append hprefix tailTrace_739208
  have hstable : (prefixWord ++ tailWord_739208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739208).length < 2 ^ (prefixWord ++ tailWord_739208).sum := by decide
  have hdescent : baseEnd_739208 < baseStart_739208 := by decide
  rcases family_descends (prefixWord ++ tailWord_739208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739236 : List Nat := [2, 3, 1, 2, 1, 4, 8]
def baseStart_739236 : Nat := 118140960795 + 739236 * 2 ^ 59
def prefixEnd_739236 : Nat := 4983230072969 + 3 ^ 40 * 739236 * 2
def baseEnd_739236 : Nat := 18744858523811109602485

theorem tailTrace_739236 : CollatzResearch.WordTrace tailWord_739236 prefixEnd_739236 18744858523811109602485 := by
  unfold tailWord_739236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481075974940849151258781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17974767966587798868345041 13481075974940849151258781)
  ·
    refine ⟨5055403490602818431722043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13481075974940849151258781 5055403490602818431722043)
    ·
      refine ⟨7583105235904227647583065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055403490602818431722043 7583105235904227647583065)
      ·
        refine ⟨5687328926928170735687299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7583105235904227647583065 5687328926928170735687299)
        ·
          refine ⟨8530993390392256103530949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5687328926928170735687299 8530993390392256103530949)
          ·
            refine ⟨1599561260698548019412053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8530993390392256103530949 1599561260698548019412053)
            ·
              refine ⟨18744858523811109602485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1599561260698548019412053 18744858523811109602485)
              ·
                rfl

theorem cell21_739236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 8].length) (baseStart_739236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739236 prefixEnd_739236 := by exact prefixLift 739236
  have htrace : WordTrace (prefixWord ++ tailWord_739236) baseStart_739236 baseEnd_739236 := by
    simpa [prefixWord, tailWord_739236, baseEnd_739236] using wordTrace_append hprefix tailTrace_739236
  have hstable : (prefixWord ++ tailWord_739236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739236).length < 2 ^ (prefixWord ++ tailWord_739236).sum := by decide
  have hdescent : baseEnd_739236 < baseStart_739236 := by decide
  rcases family_descends (prefixWord ++ tailWord_739236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
