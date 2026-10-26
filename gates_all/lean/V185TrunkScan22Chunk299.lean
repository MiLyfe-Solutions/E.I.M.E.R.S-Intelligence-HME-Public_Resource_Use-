import V185TrunkScan22Chunk298

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2666675 : List Nat := [1, 1, 1, 2, 3, 2, 1, 11]
def baseStart_2666675 : Nat := 118140960795 + 2666675 * 2 ^ 59
def prefixEnd_2666675 : Nat := 4983230072969 + 3 ^ 40 * 2666675 * 2
def baseEnd_2666675 : Nat := 101428594394700692999903

theorem tailTrace_2666675 : CollatzResearch.WordTrace tailWord_2666675 prefixEnd_2666675 101428594394700692999903 := by
  unfold tailWord_2666675
  simp only [CollatzResearch.WordTrace]
  refine ⟨97261627614099381676329479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64841085076066254450886319 97261627614099381676329479)
  ·
    refine ⟨145892441421149072514494219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97261627614099381676329479 145892441421149072514494219)
    ·
      refine ⟨218838662131723608771741329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145892441421149072514494219 218838662131723608771741329)
      ·
        refine ⟨164128996598792706578805997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218838662131723608771741329 164128996598792706578805997)
        ·
          refine ⟨61548373724547264967052249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164128996598792706578805997 61548373724547264967052249)
          ·
            refine ⟨46161280293410448725289187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61548373724547264967052249 46161280293410448725289187)
            ·
              refine ⟨69241920440115673087933781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46161280293410448725289187 69241920440115673087933781)
              ·
                refine ⟨101428594394700692999903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69241920440115673087933781 101428594394700692999903)
                ·
                  rfl

theorem cell22_2666675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 11].length) (baseStart_2666675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666675 prefixEnd_2666675 := by exact prefixLift 2666675
  have htrace : WordTrace (prefixWord ++ tailWord_2666675) baseStart_2666675 baseEnd_2666675 := by
    simpa [prefixWord, tailWord_2666675, baseEnd_2666675] using wordTrace_append hprefix tailTrace_2666675
  have hstable : (prefixWord ++ tailWord_2666675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666675).length < 2 ^ (prefixWord ++ tailWord_2666675).sum := by decide
  have hdescent : baseEnd_2666675 < baseStart_2666675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666679 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 1, 5]
def baseStart_2666679 : Nat := 118140960795 + 2666679 * 2 ^ 59
def prefixEnd_2666679 : Nat := 4983230072969 + 3 ^ 40 * 2666679 * 2
def baseEnd_2666679 : Nat := 912858718834051559899115

theorem tailTrace_2666679 : CollatzResearch.WordTrace tailWord_2666679 prefixEnd_2666679 912858718834051559899115 := by
  unfold tailWord_2666679
  simp only [CollatzResearch.WordTrace]
  refine ⟨97261773506084890359475091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64841182337389926906316727 97261773506084890359475091)
  ·
    refine ⟨145892660259127335539212637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97261773506084890359475091 145892660259127335539212637)
    ·
      refine ⟨54709747597172750827204739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145892660259127335539212637 54709747597172750827204739)
      ·
        refine ⟨82064621395759126240807109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54709747597172750827204739 82064621395759126240807109)
        ·
          refine ⟨15387116511704836170151333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82064621395759126240807109 15387116511704836170151333)
          ·
            refine ⟨2885084345944656781903375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15387116511704836170151333 2885084345944656781903375)
            ·
              refine ⟨4327626518916985172855063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885084345944656781903375 4327626518916985172855063)
              ·
                refine ⟨6491439778375477759282595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327626518916985172855063 6491439778375477759282595)
                ·
                  refine ⟨9737159667563216638923893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491439778375477759282595 9737159667563216638923893)
                  ·
                    refine ⟨912858718834051559899115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9737159667563216638923893 912858718834051559899115)
                    ·
                      rfl

theorem cell22_2666679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_2666679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666679 prefixEnd_2666679 := by exact prefixLift 2666679
  have htrace : WordTrace (prefixWord ++ tailWord_2666679) baseStart_2666679 baseEnd_2666679 := by
    simpa [prefixWord, tailWord_2666679, baseEnd_2666679] using wordTrace_append hprefix tailTrace_2666679
  have hstable : (prefixWord ++ tailWord_2666679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666679).length < 2 ^ (prefixWord ++ tailWord_2666679).sum := by decide
  have hdescent : baseEnd_2666679 < baseStart_2666679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666709 : List Nat := [1, 3, 2, 4, 2, 2, 8]
def baseStart_2666709 : Nat := 118140960795 + 2666709 * 2 ^ 59
def prefixEnd_2666709 : Nat := 4983230072969 + 3 ^ 40 * 2666709 * 2
def baseEnd_2666709 : Nat := 33809962535079314135149

theorem tailTrace_2666709 : CollatzResearch.WordTrace tailWord_2666709 prefixEnd_2666709 33809962535079314135149 := by
  unfold tailWord_2666709
  simp only [CollatzResearch.WordTrace]
  refine ⟨97262867695976205483067181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64841911797317470322044787 97262867695976205483067181)
  ·
    refine ⟨36473575385991077056150193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97262867695976205483067181 36473575385991077056150193)
    ·
      refine ⟨27355181539493307792112645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36473575385991077056150193 27355181539493307792112645)
      ·
        refine ⟨5129096538654995211021121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27355181539493307792112645 5129096538654995211021121)
        ·
          refine ⟨3846822403991246408265841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5129096538654995211021121 3846822403991246408265841)
          ·
            refine ⟨2885116802993434806199381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3846822403991246408265841 2885116802993434806199381)
            ·
              refine ⟨33809962535079314135149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2885116802993434806199381 33809962535079314135149)
              ·
                rfl

theorem cell22_2666709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 8].length) (baseStart_2666709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666709 prefixEnd_2666709 := by exact prefixLift 2666709
  have htrace : WordTrace (prefixWord ++ tailWord_2666709) baseStart_2666709 baseEnd_2666709 := by
    simpa [prefixWord, tailWord_2666709, baseEnd_2666709] using wordTrace_append hprefix tailTrace_2666709
  have hstable : (prefixWord ++ tailWord_2666709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666709).length < 2 ^ (prefixWord ++ tailWord_2666709).sum := by decide
  have hdescent : baseEnd_2666709 < baseStart_2666709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666775 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 1, 3]
def baseStart_2666775 : Nat := 118140960795 + 2666775 * 2 ^ 59
def prefixEnd_2666775 : Nat := 4983230072969 + 3 ^ 40 * 2666775 * 2
def baseEnd_2666775 : Nat := 912891581595939309498821

theorem tailTrace_2666775 : CollatzResearch.WordTrace tailWord_2666775 prefixEnd_2666775 912891581595939309498821 := by
  unfold tailWord_2666775
  simp only [CollatzResearch.WordTrace]
  refine ⟨97265274913737098754969779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64843516609158065836646519 97265274913737098754969779)
  ·
    refine ⟨145897912370605648132454669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97265274913737098754969779 145897912370605648132454669)
    ·
      refine ⟨54711717138977118049670501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145897912370605648132454669 54711717138977118049670501)
      ·
        refine ⟨10258446963558209634313219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54711717138977118049670501 10258446963558209634313219)
        ·
          refine ⟨15387670445337314451469829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10258446963558209634313219 15387670445337314451469829)
          ·
            refine ⟨2885188208500746459650593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15387670445337314451469829 2885188208500746459650593)
            ·
              refine ⟨2163891156375559844737945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885188208500746459650593 2163891156375559844737945)
              ·
                refine ⟨1622918367281669883553459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163891156375559844737945 1622918367281669883553459)
                ·
                  refine ⟨2434377550922504825330189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622918367281669883553459 2434377550922504825330189)
                  ·
                    refine ⟨912891581595939309498821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434377550922504825330189 912891581595939309498821)
                    ·
                      rfl

theorem cell22_2666775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_2666775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666775 prefixEnd_2666775 := by exact prefixLift 2666775
  have htrace : WordTrace (prefixWord ++ tailWord_2666775) baseStart_2666775 baseEnd_2666775 := by
    simpa [prefixWord, tailWord_2666775, baseEnd_2666775] using wordTrace_append hprefix tailTrace_2666775
  have hstable : (prefixWord ++ tailWord_2666775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666775).length < 2 ^ (prefixWord ++ tailWord_2666775).sum := by decide
  have hdescent : baseEnd_2666775 < baseStart_2666775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666784 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_2666784 : Nat := 118140960795 + 2666784 * 2 ^ 59
def prefixEnd_2666784 : Nat := 4983230072969 + 3 ^ 40 * 2666784 * 2
def baseEnd_2666784 : Nat := 912894662479866286023793

theorem tailTrace_2666784 : CollatzResearch.WordTrace tailWord_2666784 prefixEnd_2666784 912894662479866286023793 := by
  unfold tailWord_2666784
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632801585352246646023703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64843735447136328861364937 48632801585352246646023703)
  ·
    refine ⟨72949202378028369969035555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48632801585352246646023703 72949202378028369969035555)
    ·
      refine ⟨109423803567042554953553333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72949202378028369969035555 109423803567042554953553333)
      ·
        refine ⟨10258481584410239526895625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109423803567042554953553333 10258481584410239526895625)
        ·
          refine ⟨7693861188307679645171719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10258481584410239526895625 7693861188307679645171719)
          ·
            refine ⟨11540791782461519467757579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693861188307679645171719 11540791782461519467757579)
            ·
              refine ⟨17311187673692279201636369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11540791782461519467757579 17311187673692279201636369)
              ·
                refine ⟨12983390755269209401227277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17311187673692279201636369 12983390755269209401227277)
                ·
                  refine ⟨4868771533225953525460229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12983390755269209401227277 4868771533225953525460229)
                  ·
                    refine ⟨912894662479866286023793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4868771533225953525460229 912894662479866286023793)
                    ·
                      rfl

theorem cell22_2666784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_2666784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666784 prefixEnd_2666784 := by exact prefixLift 2666784
  have htrace : WordTrace (prefixWord ++ tailWord_2666784) baseStart_2666784 baseEnd_2666784 := by
    simpa [prefixWord, tailWord_2666784, baseEnd_2666784] using wordTrace_append hprefix tailTrace_2666784
  have hstable : (prefixWord ++ tailWord_2666784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666784).length < 2 ^ (prefixWord ++ tailWord_2666784).sum := by decide
  have hdescent : baseEnd_2666784 < baseStart_2666784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666848 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_2666848 : Nat := 118140960795 + 2666848 * 2 ^ 59
def prefixEnd_2666848 : Nat := 4983230072969 + 3 ^ 40 * 2666848 * 2
def baseEnd_2666848 : Nat := 912916570987791452423597

theorem tailTrace_2666848 : CollatzResearch.WordTrace tailWord_2666848 prefixEnd_2666848 912916570987791452423597 := by
  unfold tailWord_2666848
  simp only [CollatzResearch.WordTrace]
  refine ⟨48633968721236316111188599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64845291628315088148251465 48633968721236316111188599)
  ·
    refine ⟨72950953081854474166782899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48633968721236316111188599 72950953081854474166782899)
    ·
      refine ⟨109426429622781711250174349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72950953081854474166782899 109426429622781711250174349)
      ·
        refine ⟨41034911108543141718815381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109426429622781711250174349 41034911108543141718815381)
        ·
          refine ⟨1923511458212959768069471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41034911108543141718815381 1923511458212959768069471)
          ·
            refine ⟨2885267187319439652104207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923511458212959768069471 2885267187319439652104207)
            ·
              refine ⟨4327900780979159478156311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885267187319439652104207 4327900780979159478156311)
              ·
                refine ⟨6491851171468739217234467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327900780979159478156311 6491851171468739217234467)
                ·
                  refine ⟨9737776757203108825851701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491851171468739217234467 9737776757203108825851701)
                  ·
                    refine ⟨912916570987791452423597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9737776757203108825851701 912916570987791452423597)
                    ·
                      rfl

theorem cell22_2666848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_2666848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666848 prefixEnd_2666848 := by exact prefixLift 2666848
  have htrace : WordTrace (prefixWord ++ tailWord_2666848) baseStart_2666848 baseEnd_2666848 := by
    simpa [prefixWord, tailWord_2666848, baseEnd_2666848] using wordTrace_append hprefix tailTrace_2666848
  have hstable : (prefixWord ++ tailWord_2666848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666848).length < 2 ^ (prefixWord ++ tailWord_2666848).sum := by decide
  have hdescent : baseEnd_2666848 < baseStart_2666848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666889 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 7]
def baseStart_2666889 : Nat := 118140960795 + 2666889 * 2 ^ 59
def prefixEnd_2666889 : Nat := 4983230072969 + 3 ^ 40 * 2666889 * 2
def baseEnd_2666889 : Nat := 304310202041893670716157

theorem tailTrace_2666889 : CollatzResearch.WordTrace tailWord_2666889 prefixEnd_2666889 304310202041893670716157 := by
  unfold tailWord_2666889
  simp only [CollatzResearch.WordTrace]
  refine ⟨97269432835324096224619721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64846288556882730816413147 97269432835324096224619721)
  ·
    refine ⟨72952074626493072168464791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97269432835324096224619721 72952074626493072168464791)
    ·
      refine ⟨109428111939739608252697187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72952074626493072168464791 109428111939739608252697187)
      ·
        refine ⟨164142167909609412379045781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109428111939739608252697187 164142167909609412379045781)
        ·
          refine ⟨7694164120762941205267771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164142167909609412379045781 7694164120762941205267771)
          ·
            refine ⟨11541246181144411807901657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7694164120762941205267771 11541246181144411807901657)
            ·
              refine ⟨8655934635858308855926243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11541246181144411807901657 8655934635858308855926243)
              ·
                refine ⟨12983901953787463283889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8655934635858308855926243 12983901953787463283889365)
                ·
                  refine ⟨304310202041893670716157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12983901953787463283889365 304310202041893670716157)
                  ·
                    rfl

theorem cell22_2666889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_2666889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666889 prefixEnd_2666889 := by exact prefixLift 2666889
  have htrace : WordTrace (prefixWord ++ tailWord_2666889) baseStart_2666889 baseEnd_2666889 := by
    simpa [prefixWord, tailWord_2666889, baseEnd_2666889] using wordTrace_append hprefix tailTrace_2666889
  have hstable : (prefixWord ++ tailWord_2666889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666889).length < 2 ^ (prefixWord ++ tailWord_2666889).sum := by decide
  have hdescent : baseEnd_2666889 < baseStart_2666889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666906 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_2666906 : Nat := 118140960795 + 2666906 * 2 ^ 59
def prefixEnd_2666906 : Nat := 4983230072969 + 3 ^ 40 * 2666906 * 2
def baseEnd_2666906 : Nat := 304312141857699544824473

theorem tailTrace_2666906 : CollatzResearch.WordTrace tailWord_2666906 prefixEnd_2666906 304312141857699544824473 := by
  unfold tailWord_2666906
  simp only [CollatzResearch.WordTrace]
  refine ⟨24317513219065627031997143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64846701917508338751992381 24317513219065627031997143)
  ·
    refine ⟨36476269828598440547995715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24317513219065627031997143 36476269828598440547995715)
    ·
      refine ⟨54714404742897660821993573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36476269828598440547995715 54714404742897660821993573)
      ·
        refine ⟨10258950889293311404123795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54714404742897660821993573 10258950889293311404123795)
        ·
          refine ⟨15388426333939967106185693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10258950889293311404123795 15388426333939967106185693)
          ·
            refine ⟨5770659875227487664819635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15388426333939967106185693 5770659875227487664819635)
            ·
              refine ⟨8655989812841231497229453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5770659875227487664819635 8655989812841231497229453)
              ·
                refine ⟨3245996179815461811461045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8655989812841231497229453 3245996179815461811461045)
                ·
                  refine ⟨304312141857699544824473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3245996179815461811461045 304312141857699544824473)
                  ·
                    rfl

theorem cell22_2666906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_2666906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666906 prefixEnd_2666906 := by exact prefixLift 2666906
  have htrace : WordTrace (prefixWord ++ tailWord_2666906) baseStart_2666906 baseEnd_2666906 := by
    simpa [prefixWord, tailWord_2666906, baseEnd_2666906] using wordTrace_append hprefix tailTrace_2666906
  have hstable : (prefixWord ++ tailWord_2666906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666906).length < 2 ^ (prefixWord ++ tailWord_2666906).sum := by decide
  have hdescent : baseEnd_2666906 < baseStart_2666906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667045 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_2667045 : Nat := 118140960795 + 2667045 * 2 ^ 59
def prefixEnd_2667045 : Nat := 4983230072969 + 3 ^ 40 * 2667045 * 2
def baseEnd_2667045 : Nat := 912984008113748605247993

theorem tailTrace_2667045 : CollatzResearch.WordTrace tailWord_2667045 prefixEnd_2667045 912984008113748605247993 := by
  unfold tailWord_2667045
  simp only [CollatzResearch.WordTrace]
  refine ⟨97275122622758934867298589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64850081748505956578199059 97275122622758934867298589)
  ·
    refine ⟨36478170983534600575236971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97275122622758934867298589 36478170983534600575236971)
    ·
      refine ⟨54717256475301900862855457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36478170983534600575236971 54717256475301900862855457)
      ·
        refine ⟨41037942356476425647141593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54717256475301900862855457 41037942356476425647141593)
        ·
          refine ⟨30778456767357319235356195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41037942356476425647141593 30778456767357319235356195)
          ·
            refine ⟨46167685151035978853034293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30778456767357319235356195 46167685151035978853034293)
            ·
              refine ⟨4328220482909623017471965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46167685151035978853034293 4328220482909623017471965)
              ·
                refine ⟨1623082681091108631551987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328220482909623017471965 1623082681091108631551987)
                ·
                  refine ⟨2434624021636662947327981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623082681091108631551987 2434624021636662947327981)
                  ·
                    refine ⟨912984008113748605247993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434624021636662947327981 912984008113748605247993)
                    ·
                      rfl

theorem cell22_2667045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_2667045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667045 prefixEnd_2667045 := by exact prefixLift 2667045
  have htrace : WordTrace (prefixWord ++ tailWord_2667045) baseStart_2667045 baseEnd_2667045 := by
    simpa [prefixWord, tailWord_2667045, baseEnd_2667045] using wordTrace_append hprefix tailTrace_2667045
  have hstable : (prefixWord ++ tailWord_2667045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667045).length < 2 ^ (prefixWord ++ tailWord_2667045).sum := by decide
  have hdescent : baseEnd_2667045 < baseStart_2667045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667062 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2667062 : Nat := 118140960795 + 2667062 * 2 ^ 59
def prefixEnd_2667062 : Nat := 4983230072969 + 3 ^ 40 * 2667062 * 2
def baseEnd_2667062 : Nat := 912989827561166227572941

theorem tailTrace_2667062 : CollatzResearch.WordTrace tailWord_2667062 prefixEnd_2667062 912989827561166227572941 := by
  unfold tailWord_2667062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6079733916481084173166715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64850495109131564513778293 6079733916481084173166715)
  ·
    refine ⟨9119600874721626259750073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6079733916481084173166715 9119600874721626259750073)
    ·
      refine ⟨6839700656041219694812555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9119600874721626259750073 6839700656041219694812555)
      ·
        refine ⟨10259550984061829542218833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839700656041219694812555 10259550984061829542218833)
        ·
          refine ⟨7694663238046372156664125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10259550984061829542218833 7694663238046372156664125)
          ·
            refine ⟨2885498714267389558749047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7694663238046372156664125 2885498714267389558749047)
            ·
              refine ⟨4328248071401084338123571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885498714267389558749047 4328248071401084338123571)
              ·
                refine ⟨6492372107101626507185357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328248071401084338123571 6492372107101626507185357)
                ·
                  refine ⟨2434639540163109940194509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6492372107101626507185357 2434639540163109940194509)
                  ·
                    refine ⟨912989827561166227572941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434639540163109940194509 912989827561166227572941)
                    ·
                      rfl

theorem cell22_2667062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2667062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667062 prefixEnd_2667062 := by exact prefixLift 2667062
  have htrace : WordTrace (prefixWord ++ tailWord_2667062) baseStart_2667062 baseEnd_2667062 := by
    simpa [prefixWord, tailWord_2667062, baseEnd_2667062] using wordTrace_append hprefix tailTrace_2667062
  have hstable : (prefixWord ++ tailWord_2667062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667062).length < 2 ^ (prefixWord ++ tailWord_2667062).sum := by decide
  have hdescent : baseEnd_2667062 < baseStart_2667062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667071 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_2667071 : Nat := 118140960795 + 2667071 * 2 ^ 59
def prefixEnd_2667071 : Nat := 4983230072969 + 3 ^ 40 * 2667071 * 2
def baseEnd_2667071 : Nat := 912992908445093204097913

theorem tailTrace_2667071 : CollatzResearch.WordTrace tailWord_2667071 prefixEnd_2667071 912992908445093204097913 := by
  unfold tailWord_2667071
  simp only [CollatzResearch.WordTrace]
  refine ⟨97276070920664741307745067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64850713947109827538496711 97276070920664741307745067)
  ·
    refine ⟨145914106380997111961617601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97276070920664741307745067 145914106380997111961617601)
    ·
      refine ⟨109435579785747833971213201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145914106380997111961617601 109435579785747833971213201)
      ·
        refine ⟨82076684839310875478409901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109435579785747833971213201 82076684839310875478409901)
        ·
          refine ⟨30778756814741578304403713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82076684839310875478409901 30778756814741578304403713)
          ·
            refine ⟨23084067611056183728302785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30778756814741578304403713 23084067611056183728302785)
            ·
              refine ⟨17313050708292137796227089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23084067611056183728302785 17313050708292137796227089)
              ·
                refine ⟨12984788031219103347170317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17313050708292137796227089 12984788031219103347170317)
                ·
                  refine ⟨4869295511707163755188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12984788031219103347170317 4869295511707163755188869)
                  ·
                    refine ⟨912992908445093204097913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869295511707163755188869 912992908445093204097913)
                    ·
                      rfl

theorem cell22_2667071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_2667071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667071 prefixEnd_2667071 := by exact prefixLift 2667071
  have htrace : WordTrace (prefixWord ++ tailWord_2667071) baseStart_2667071 baseEnd_2667071 := by
    simpa [prefixWord, tailWord_2667071, baseEnd_2667071] using wordTrace_append hprefix tailTrace_2667071
  have hstable : (prefixWord ++ tailWord_2667071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667071).length < 2 ^ (prefixWord ++ tailWord_2667071).sum := by decide
  have hdescent : baseEnd_2667071 < baseStart_2667071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667086 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_2667086 : Nat := 118140960795 + 2667086 * 2 ^ 59
def prefixEnd_2667086 : Nat := 4983230072969 + 3 ^ 40 * 2667086 * 2
def baseEnd_2667086 : Nat := 304332681083879388324289

theorem tailTrace_2667086 : CollatzResearch.WordTrace tailWord_2667086 prefixEnd_2667086 304332681083879388324289 := by
  unfold tailWord_2667086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159577251951299858692639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64851078677073599246360741 12159577251951299858692639)
  ·
    refine ⟨18239365877926949788038959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12159577251951299858692639 18239365877926949788038959)
    ·
      refine ⟨27359048816890424682058439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18239365877926949788038959 27359048816890424682058439)
      ·
        refine ⟨41038573225335637023087659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27359048816890424682058439 41038573225335637023087659)
        ·
          refine ⟨61557859838003455534631489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41038573225335637023087659 61557859838003455534631489)
          ·
            refine ⟨46168394878502591650973617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61557859838003455534631489 46168394878502591650973617)
            ·
              refine ⟨34626296158876943738230213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46168394878502591650973617 34626296158876943738230213)
              ·
                refine ⟨6492430529789426950918165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34626296158876943738230213 6492430529789426950918165)
                ·
                  refine ⟨304332681083879388324289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6492430529789426950918165 304332681083879388324289)
                  ·
                    rfl

theorem cell22_2667086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_2667086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667086 prefixEnd_2667086 := by exact prefixLift 2667086
  have htrace : WordTrace (prefixWord ++ tailWord_2667086) baseStart_2667086 baseEnd_2667086 := by
    simpa [prefixWord, tailWord_2667086, baseEnd_2667086] using wordTrace_append hprefix tailTrace_2667086
  have hstable : (prefixWord ++ tailWord_2667086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667086).length < 2 ^ (prefixWord ++ tailWord_2667086).sum := by decide
  have hdescent : baseEnd_2667086 < baseStart_2667086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667105 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2667105 : Nat := 118140960795 + 2667105 * 2 ^ 59
def prefixEnd_2667105 : Nat := 4983230072969 + 3 ^ 40 * 2667105 * 2
def baseEnd_2667105 : Nat := 913004547339928448747809

theorem tailTrace_2667105 : CollatzResearch.WordTrace tailWord_2667105 prefixEnd_2667105 913004547339928448747809 := by
  unfold tailWord_2667105
  simp only [CollatzResearch.WordTrace]
  refine ⟨97277311002541565114482769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64851540668361043409655179 97277311002541565114482769)
  ·
    refine ⟨72957983251906173835862077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97277311002541565114482769 72957983251906173835862077)
    ·
      refine ⟨27359243719464815188448279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72957983251906173835862077 27359243719464815188448279)
      ·
        refine ⟨41038865579197222782672419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27359243719464815188448279 41038865579197222782672419)
        ·
          refine ⟨61558298368795834174008629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41038865579197222782672419 61558298368795834174008629)
          ·
            refine ⟨5771090472074609453813309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61558298368795834174008629 5771090472074609453813309)
            ·
              refine ⟨2164158927027978545179991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5771090472074609453813309 2164158927027978545179991)
              ·
                refine ⟨3246238390541967817769987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164158927027978545179991 3246238390541967817769987)
                ·
                  refine ⟨4869357585812951726654981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246238390541967817769987 4869357585812951726654981)
                  ·
                    refine ⟨913004547339928448747809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4869357585812951726654981 913004547339928448747809)
                    ·
                      rfl

theorem cell22_2667105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2667105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667105 prefixEnd_2667105 := by exact prefixLift 2667105
  have htrace : WordTrace (prefixWord ++ tailWord_2667105) baseStart_2667105 baseEnd_2667105 := by
    simpa [prefixWord, tailWord_2667105, baseEnd_2667105] using wordTrace_append hprefix tailTrace_2667105
  have hstable : (prefixWord ++ tailWord_2667105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667105).length < 2 ^ (prefixWord ++ tailWord_2667105).sum := by decide
  have hdescent : baseEnd_2667105 < baseStart_2667105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667120 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_2667120 : Nat := 118140960795 + 2667120 * 2 ^ 59
def prefixEnd_2667120 : Nat := 4983230072969 + 3 ^ 40 * 2667120 * 2
def baseEnd_2667120 : Nat := 304336560715491136540921

theorem tailTrace_2667120 : CollatzResearch.WordTrace tailWord_2667120 prefixEnd_2667120 304336560715491136540921 := by
  unfold tailWord_2667120
  simp only [CollatzResearch.WordTrace]
  refine ⟨48638929048743611338139407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64851905398324815117519209 48638929048743611338139407)
  ·
    refine ⟨72958393573115417007209111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48638929048743611338139407 72958393573115417007209111)
    ·
      refine ⟨109437590359673125510813667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72958393573115417007209111 109437590359673125510813667)
      ·
        refine ⟨164156385539509688266220501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109437590359673125510813667 164156385539509688266220501)
        ·
          refine ⟨3847415286082258318739543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 164156385539509688266220501 3847415286082258318739543)
          ·
            refine ⟨5771122929123387478109315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847415286082258318739543 5771122929123387478109315)
            ·
              refine ⟨8656684393685081217163973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771122929123387478109315 8656684393685081217163973)
              ·
                refine ⟨1623128323815952728218245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8656684393685081217163973 1623128323815952728218245)
                ·
                  refine ⟨304336560715491136540921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623128323815952728218245 304336560715491136540921)
                  ·
                    rfl

theorem cell22_2667120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_2667120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667120 prefixEnd_2667120 := by exact prefixLift 2667120
  have htrace : WordTrace (prefixWord ++ tailWord_2667120) baseStart_2667120 baseEnd_2667120 := by
    simpa [prefixWord, tailWord_2667120, baseEnd_2667120] using wordTrace_append hprefix tailTrace_2667120
  have hstable : (prefixWord ++ tailWord_2667120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667120).length < 2 ^ (prefixWord ++ tailWord_2667120).sum := by decide
  have hdescent : baseEnd_2667120 < baseStart_2667120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667169 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2667169 : Nat := 118140960795 + 2667169 * 2 ^ 59
def prefixEnd_2667169 : Nat := 4983230072969 + 3 ^ 40 * 2667169 * 2
def baseEnd_2667169 : Nat := 913026455847853615147613

theorem tailTrace_2667169 : CollatzResearch.WordTrace tailWord_2667169 prefixEnd_2667169 913026455847853615147613 := by
  unfold tailWord_2667169
  simp only [CollatzResearch.WordTrace]
  refine ⟨97279645274309704044812561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64853096849539802696541707 97279645274309704044812561)
  ·
    refine ⟨72959733955732278033609421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97279645274309704044812561 72959733955732278033609421)
    ·
      refine ⟨27359900233399604262603533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72959733955732278033609421 27359900233399604262603533)
      ·
        refine ⟨10259962587524851598476325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27359900233399604262603533 10259962587524851598476325)
        ·
          refine ⟨1923742985160909674714311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10259962587524851598476325 1923742985160909674714311)
          ·
            refine ⟨2885614477741364512071467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923742985160909674714311 2885614477741364512071467)
            ·
              refine ⟨4328421716612046768107201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885614477741364512071467 4328421716612046768107201)
              ·
                refine ⟨3246316287459035076080401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4328421716612046768107201 3246316287459035076080401)
                ·
                  refine ⟨2434737215594276307060301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3246316287459035076080401 2434737215594276307060301)
                  ·
                    refine ⟨913026455847853615147613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434737215594276307060301 913026455847853615147613)
                    ·
                      rfl

theorem cell22_2667169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2667169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667169 prefixEnd_2667169 := by exact prefixLift 2667169
  have htrace : WordTrace (prefixWord ++ tailWord_2667169) baseStart_2667169 baseEnd_2667169 := by
    simpa [prefixWord, tailWord_2667169, baseEnd_2667169] using wordTrace_append hprefix tailTrace_2667169
  have hstable : (prefixWord ++ tailWord_2667169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667169).length < 2 ^ (prefixWord ++ tailWord_2667169).sum := by decide
  have hdescent : baseEnd_2667169 < baseStart_2667169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667214 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2667214 : Nat := 118140960795 + 2667214 * 2 ^ 59
def prefixEnd_2667214 : Nat := 4983230072969 + 3 ^ 40 * 2667214 * 2
def baseEnd_2667214 : Nat := 913041860267488497772475

theorem tailTrace_2667214 : CollatzResearch.WordTrace tailWord_2667214 prefixEnd_2667214 913041860267488497772475 := by
  unfold tailWord_2667214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160160819893334591275087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64854191039431117820133797 12160160819893334591275087)
  ·
    refine ⟨18240241229840001886912631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12160160819893334591275087 18240241229840001886912631)
    ·
      refine ⟨27360361844760002830368947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18240241229840001886912631 27360361844760002830368947)
      ·
        refine ⟨41040542767140004245553421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27360361844760002830368947 41040542767140004245553421)
        ·
          refine ⟨15390203537677501592082533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41040542767140004245553421 15390203537677501592082533)
          ·
            refine ⟨2885663163314531548515475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15390203537677501592082533 2885663163314531548515475)
            ·
              refine ⟨4328494744971797322773213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885663163314531548515475 4328494744971797322773213)
              ·
                refine ⟨1623185529364423996039955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328494744971797322773213 1623185529364423996039955)
                ·
                  refine ⟨2434778294046635994059933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623185529364423996039955 2434778294046635994059933)
                  ·
                    refine ⟨913041860267488497772475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434778294046635994059933 913041860267488497772475)
                    ·
                      rfl

theorem cell22_2667214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2667214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667214 prefixEnd_2667214 := by exact prefixLift 2667214
  have htrace : WordTrace (prefixWord ++ tailWord_2667214) baseStart_2667214 baseEnd_2667214 := by
    simpa [prefixWord, tailWord_2667214, baseEnd_2667214] using wordTrace_append hprefix tailTrace_2667214
  have hstable : (prefixWord ++ tailWord_2667214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667214).length < 2 ^ (prefixWord ++ tailWord_2667214).sum := by decide
  have hdescent : baseEnd_2667214 < baseStart_2667214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667313 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2667313 : Nat := 118140960795 + 2667313 * 2 ^ 59
def prefixEnd_2667313 : Nat := 4983230072969 + 3 ^ 40 * 2667313 * 2
def baseEnd_2667313 : Nat := 913075749990685239547171

theorem tailTrace_2667313 : CollatzResearch.WordTrace tailWord_2667313 prefixEnd_2667313 913075749990685239547171 := by
  unfold tailWord_2667313
  simp only [CollatzResearch.WordTrace]
  refine ⟨97284897385788016638054593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64856598257192011092036395 97284897385788016638054593)
  ·
    refine ⟨72963673039341012478540945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97284897385788016638054593 72963673039341012478540945)
    ·
      refine ⟨54722754779505759358905709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72963673039341012478540945 54722754779505759358905709)
      ·
        refine ⟨20521033042314659759589641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54722754779505759358905709 20521033042314659759589641)
        ·
          refine ⟨15390774781735994819692231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20521033042314659759589641 15390774781735994819692231)
          ·
            refine ⟨23086162172603992229538347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15390774781735994819692231 23086162172603992229538347)
            ·
              refine ⟨34629243258905988344307521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23086162172603992229538347 34629243258905988344307521)
              ·
                refine ⟨25971932444179491258230641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34629243258905988344307521 25971932444179491258230641)
                ·
                  refine ⟨19478949333134618443672981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25971932444179491258230641 19478949333134618443672981)
                  ·
                    refine ⟨913075749990685239547171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19478949333134618443672981 913075749990685239547171)
                    ·
                      rfl

theorem cell22_2667313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2667313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667313 prefixEnd_2667313 := by exact prefixLift 2667313
  have htrace : WordTrace (prefixWord ++ tailWord_2667313) baseStart_2667313 baseEnd_2667313 := by
    simpa [prefixWord, tailWord_2667313, baseEnd_2667313] using wordTrace_append hprefix tailTrace_2667313
  have hstable : (prefixWord ++ tailWord_2667313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667313).length < 2 ^ (prefixWord ++ tailWord_2667313).sum := by decide
  have hdescent : baseEnd_2667313 < baseStart_2667313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667315 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 5, 3]
def baseStart_2667315 : Nat := 118140960795 + 2667315 * 2 ^ 59
def prefixEnd_2667315 : Nat := 4983230072969 + 3 ^ 40 * 2667315 * 2
def baseEnd_2667315 : Nat := 913076434631557900997165

theorem tailTrace_2667315 : CollatzResearch.WordTrace tailWord_2667315 prefixEnd_2667315 913076434631557900997165 := by
  unfold tailWord_2667315
  simp only [CollatzResearch.WordTrace]
  refine ⟨97284970331780770979627399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64856646887853847319751599 97284970331780770979627399)
  ·
    refine ⟨145927455497671156469441099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97284970331780770979627399 145927455497671156469441099)
    ·
      refine ⟨218891183246506734704161649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145927455497671156469441099 218891183246506734704161649)
      ·
        refine ⟨164168387434880051028121237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218891183246506734704161649 164168387434880051028121237)
        ·
          refine ⟨7695393161010002391943183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164168387434880051028121237 7695393161010002391943183)
          ·
            refine ⟨11543089741515003587914775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695393161010002391943183 11543089741515003587914775)
            ·
              refine ⟨17314634612272505381872163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543089741515003587914775 17314634612272505381872163)
              ·
                refine ⟨25971951918408758072808245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17314634612272505381872163 25971951918408758072808245)
                ·
                  refine ⟨2434870492350821069325773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25971951918408758072808245 2434870492350821069325773)
                  ·
                    refine ⟨913076434631557900997165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434870492350821069325773 913076434631557900997165)
                    ·
                      rfl

theorem cell22_2667315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3].length) (baseStart_2667315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667315 prefixEnd_2667315 := by exact prefixLift 2667315
  have htrace : WordTrace (prefixWord ++ tailWord_2667315) baseStart_2667315 baseEnd_2667315 := by
    simpa [prefixWord, tailWord_2667315, baseEnd_2667315] using wordTrace_append hprefix tailTrace_2667315
  have hstable : (prefixWord ++ tailWord_2667315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667315).length < 2 ^ (prefixWord ++ tailWord_2667315).sum := by decide
  have hdescent : baseEnd_2667315 < baseStart_2667315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667345 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 7]
def baseStart_2667345 : Nat := 118140960795 + 2667345 * 2 ^ 59
def prefixEnd_2667345 : Nat := 4983230072969 + 3 ^ 40 * 2667345 * 2
def baseEnd_2667345 : Nat := 304362234748215940915691

theorem tailTrace_2667345 : CollatzResearch.WordTrace tailWord_2667345 prefixEnd_2667345 304362234748215940915691 := by
  unfold tailWord_2667345
  simp only [CollatzResearch.WordTrace]
  refine ⟨97286064521672086103219489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64857376347781390735479659 97286064521672086103219489)
  ·
    refine ⟨72964548391254064577414617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97286064521672086103219489 72964548391254064577414617)
    ·
      refine ⟨54723411293440548433060963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72964548391254064577414617 54723411293440548433060963)
      ·
        refine ⟨82085116940160822649591445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54723411293440548433060963 82085116940160822649591445)
        ·
          refine ⟨3847739856570038561699599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82085116940160822649591445 3847739856570038561699599)
          ·
            refine ⟨5771609784855057842549399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847739856570038561699599 5771609784855057842549399)
            ·
              refine ⟨8657414677282586763824099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771609784855057842549399 8657414677282586763824099)
              ·
                refine ⟨12986122015923880145736149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8657414677282586763824099 12986122015923880145736149)
                ·
                  refine ⟨304362234748215940915691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12986122015923880145736149 304362234748215940915691)
                  ·
                    rfl

theorem cell22_2667345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_2667345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667345 prefixEnd_2667345 := by exact prefixLift 2667345
  have htrace : WordTrace (prefixWord ++ tailWord_2667345) baseStart_2667345 baseEnd_2667345 := by
    simpa [prefixWord, tailWord_2667345, baseEnd_2667345] using wordTrace_append hprefix tailTrace_2667345
  have hstable : (prefixWord ++ tailWord_2667345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667345).length < 2 ^ (prefixWord ++ tailWord_2667345).sum := by decide
  have hdescent : baseEnd_2667345 < baseStart_2667345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667544 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_2667544 : Nat := 118140960795 + 2667544 * 2 ^ 59
def prefixEnd_2667544 : Nat := 4983230072969 + 3 ^ 40 * 2667544 * 2
def baseEnd_2667544 : Nat := 913154826011477637021463

theorem tailTrace_2667544 : CollatzResearch.WordTrace tailWord_2667544 prefixEnd_2667544 913154826011477637021463 := by
  unfold tailWord_2667544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48646661323975571544856843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64862215098634095393142457 48646661323975571544856843)
  ·
    refine ⟨72969991985963357317285265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48646661323975571544856843 72969991985963357317285265)
    ·
      refine ⟨54727493989472517987963949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72969991985963357317285265 54727493989472517987963949)
      ·
        refine ⟨20522810246052194245486481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54727493989472517987963949 20522810246052194245486481)
        ·
          refine ⟨15392107684539145684114861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20522810246052194245486481 15392107684539145684114861)
          ·
            refine ⟨5772040381702179631543073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15392107684539145684114861 5772040381702179631543073)
            ·
              refine ⟨4329030286276634723657305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5772040381702179631543073 4329030286276634723657305)
              ·
                refine ⟨3246772714707476042742979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329030286276634723657305 3246772714707476042742979)
                ·
                  refine ⟨4870159072061214064114469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246772714707476042742979 4870159072061214064114469)
                  ·
                    refine ⟨913154826011477637021463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870159072061214064114469 913154826011477637021463)
                    ·
                      rfl

theorem cell22_2667544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_2667544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667544 prefixEnd_2667544 := by exact prefixLift 2667544
  have htrace : WordTrace (prefixWord ++ tailWord_2667544) baseStart_2667544 baseEnd_2667544 := by
    simpa [prefixWord, tailWord_2667544, baseEnd_2667544] using wordTrace_append hprefix tailTrace_2667544
  have hstable : (prefixWord ++ tailWord_2667544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667544).length < 2 ^ (prefixWord ++ tailWord_2667544).sum := by decide
  have hdescent : baseEnd_2667544 < baseStart_2667544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667557 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_2667557 : Nat := 118140960795 + 2667557 * 2 ^ 59
def prefixEnd_2667557 : Nat := 4983230072969 + 3 ^ 40 * 2667557 * 2
def baseEnd_2667557 : Nat := 913159276177149936446423

theorem tailTrace_2667557 : CollatzResearch.WordTrace tailWord_2667557 prefixEnd_2667557 913159276177149936446423 := by
  unfold tailWord_2667557
  simp only [CollatzResearch.WordTrace]
  refine ⟨97293796796904046309936925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64862531197936030873291283 97293796796904046309936925)
  ·
    refine ⟨36485173798839017366226347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97293796796904046309936925 36485173798839017366226347)
    ·
      refine ⟨54727760698258526049339521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36485173798839017366226347 54727760698258526049339521)
      ·
        refine ⟨41045820523693894537004641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54727760698258526049339521 41045820523693894537004641)
        ·
          refine ⟨30784365392770420902753481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41045820523693894537004641 30784365392770420902753481)
          ·
            refine ⟨23088274044577815677065111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30784365392770420902753481 23088274044577815677065111)
            ·
              refine ⟨34632411066866723515597667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23088274044577815677065111 34632411066866723515597667)
              ·
                refine ⟨51948616600300085273396501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34632411066866723515597667 51948616600300085273396501)
                ·
                  refine ⟨2435091403139066497190461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51948616600300085273396501 2435091403139066497190461)
                  ·
                    refine ⟨913159276177149936446423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435091403139066497190461 913159276177149936446423)
                    ·
                      rfl

theorem cell22_2667557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_2667557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667557 prefixEnd_2667557 := by exact prefixLift 2667557
  have htrace : WordTrace (prefixWord ++ tailWord_2667557) baseStart_2667557 baseEnd_2667557 := by
    simpa [prefixWord, tailWord_2667557, baseEnd_2667557] using wordTrace_append hprefix tailTrace_2667557
  have hstable : (prefixWord ++ tailWord_2667557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667557).length < 2 ^ (prefixWord ++ tailWord_2667557).sum := by decide
  have hdescent : baseEnd_2667557 < baseStart_2667557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667576 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_2667576 : Nat := 118140960795 + 2667576 * 2 ^ 59
def prefixEnd_2667576 : Nat := 4983230072969 + 3 ^ 40 * 2667576 * 2
def baseEnd_2667576 : Nat := 304388593421813406740455

theorem tailTrace_2667576 : CollatzResearch.WordTrace tailWord_2667576 prefixEnd_2667576 304388593421813406740455 := by
  unfold tailWord_2667576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48647244891917606277439291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64862993189223475036585721 48647244891917606277439291)
  ·
    refine ⟨72970867337876409416158937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48647244891917606277439291 72970867337876409416158937)
    ·
      refine ⟨54728150503407307062119203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72970867337876409416158937 54728150503407307062119203)
      ·
        refine ⟨82092225755110960593178805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54728150503407307062119203 82092225755110960593178805)
        ·
          refine ⟨7696146164541652555610513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82092225755110960593178805 7696146164541652555610513)
          ·
            refine ⟨5772109623406239416707885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7696146164541652555610513 5772109623406239416707885)
            ·
              refine ⟨2164541108777339781265457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5772109623406239416707885 2164541108777339781265457)
              ·
                refine ⟨1623405831583004835949093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2164541108777339781265457 1623405831583004835949093)
                ·
                  refine ⟨304388593421813406740455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623405831583004835949093 304388593421813406740455)
                  ·
                    rfl

theorem cell22_2667576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_2667576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667576 prefixEnd_2667576 := by exact prefixLift 2667576
  have htrace : WordTrace (prefixWord ++ tailWord_2667576) baseStart_2667576 baseEnd_2667576 := by
    simpa [prefixWord, tailWord_2667576, baseEnd_2667576] using wordTrace_append hprefix tailTrace_2667576
  have hstable : (prefixWord ++ tailWord_2667576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667576).length < 2 ^ (prefixWord ++ tailWord_2667576).sum := by decide
  have hdescent : baseEnd_2667576 < baseStart_2667576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667591 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 2, 3]
def baseStart_2667591 : Nat := 118140960795 + 2667591 * 2 ^ 59
def prefixEnd_2667591 : Nat := 4983230072969 + 3 ^ 40 * 2667591 * 2
def baseEnd_2667591 : Nat := 913170915071985181096319

theorem tailTrace_2667591 : CollatzResearch.WordTrace tailWord_2667591 prefixEnd_2667591 913170915071985181096319 := by
  unfold tailWord_2667591
  simp only [CollatzResearch.WordTrace]
  refine ⟨97295036878780870116674627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64863357919187246744449751 97295036878780870116674627)
  ·
    refine ⟨145942555318171305175011941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97295036878780870116674627 145942555318171305175011941)
    ·
      refine ⟨27364229122157119720314739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145942555318171305175011941 27364229122157119720314739)
      ·
        refine ⟨41046343683235679580472109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27364229122157119720314739 41046343683235679580472109)
        ·
          refine ⟨15392378881213379842677041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41046343683235679580472109 15392378881213379842677041)
          ·
            refine ⟨11544284160910034882007781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15392378881213379842677041 11544284160910034882007781)
            ·
              refine ⟨2164553280170631540376459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11544284160910034882007781 2164553280170631540376459)
              ·
                refine ⟨3246829920255947310564689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164553280170631540376459 3246829920255947310564689)
                ·
                  refine ⟨2435122440191960482923517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3246829920255947310564689 2435122440191960482923517)
                  ·
                    refine ⟨913170915071985181096319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435122440191960482923517 913170915071985181096319)
                    ·
                      rfl

theorem cell22_2667591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_2667591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667591 prefixEnd_2667591 := by exact prefixLift 2667591
  have htrace : WordTrace (prefixWord ++ tailWord_2667591) baseStart_2667591 baseEnd_2667591 := by
    simpa [prefixWord, tailWord_2667591, baseEnd_2667591] using wordTrace_append hprefix tailTrace_2667591
  have hstable : (prefixWord ++ tailWord_2667591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667591).length < 2 ^ (prefixWord ++ tailWord_2667591).sum := by decide
  have hdescent : baseEnd_2667591 < baseStart_2667591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667649 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 5]
def baseStart_2667649 : Nat := 118140960795 + 2667649 * 2 ^ 59
def prefixEnd_2667649 : Nat := 4983230072969 + 3 ^ 40 * 2667649 * 2
def baseEnd_2667649 : Nat := 304396923219097454382047

theorem tailTrace_2667649 : CollatzResearch.WordTrace tailWord_2667649 prefixEnd_2667649 304396923219097454382047 := by
  unfold tailWord_2667649
  simp only [CollatzResearch.WordTrace]
  refine ⟨97297152312570746022286001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64864768208380497348190667 97297152312570746022286001)
  ·
    refine ⟨72972864234428059516714501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97297152312570746022286001 72972864234428059516714501)
    ·
      refine ⟨13682412043955261159383969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72972864234428059516714501 13682412043955261159383969)
      ·
        refine ⟨10261809032966445869537977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13682412043955261159383969 10261809032966445869537977)
        ·
          refine ⟨7696356774724834402153483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10261809032966445869537977 7696356774724834402153483)
          ·
            refine ⟨11544535162087251603230225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7696356774724834402153483 11544535162087251603230225)
            ·
              refine ⟨8658401371565438702422669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11544535162087251603230225 8658401371565438702422669)
              ·
                refine ⟨3246900514337039513408501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8658401371565438702422669 3246900514337039513408501)
                ·
                  refine ⟨304396923219097454382047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3246900514337039513408501 304396923219097454382047)
                  ·
                    rfl

theorem cell22_2667649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_2667649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667649 prefixEnd_2667649 := by exact prefixLift 2667649
  have htrace : WordTrace (prefixWord ++ tailWord_2667649) baseStart_2667649 baseEnd_2667649 := by
    simpa [prefixWord, tailWord_2667649, baseEnd_2667649] using wordTrace_append hprefix tailTrace_2667649
  have hstable : (prefixWord ++ tailWord_2667649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667649).length < 2 ^ (prefixWord ++ tailWord_2667649).sum := by decide
  have hdescent : baseEnd_2667649 < baseStart_2667649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667677 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2667677 : Nat := 118140960795 + 2667677 * 2 ^ 59
def prefixEnd_2667677 : Nat := 4983230072969 + 3 ^ 40 * 2667677 * 2
def baseEnd_2667677 : Nat := 304400118209836541148685

theorem tailTrace_2667677 : CollatzResearch.WordTrace tailWord_2667677 prefixEnd_2667677 304400118209836541148685 := by
  unfold tailWord_2667677
  simp only [CollatzResearch.WordTrace]
  refine ⟨97298173556469306804305285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64865449037646204536203523 97298173556469306804305285)
  ·
    refine ⟨18243407541837995025807241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97298173556469306804305285 18243407541837995025807241)
    ·
      refine ⟨13682555656378496269355431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18243407541837995025807241 13682555656378496269355431)
      ·
        refine ⟨20523833484567744404033147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13682555656378496269355431 20523833484567744404033147)
        ·
          refine ⟨30785750226851616606049721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20523833484567744404033147 30785750226851616606049721)
          ·
            refine ⟨23089312670138712454537291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30785750226851616606049721 23089312670138712454537291)
            ·
              refine ⟨34633969005208068681805937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23089312670138712454537291 34633969005208068681805937)
              ·
                refine ⟨25975476753906051511354453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34633969005208068681805937 25975476753906051511354453)
                ·
                  refine ⟨304400118209836541148685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25975476753906051511354453 304400118209836541148685)
                  ·
                    rfl

theorem cell22_2667677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2667677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667677 prefixEnd_2667677 := by exact prefixLift 2667677
  have htrace : WordTrace (prefixWord ++ tailWord_2667677) baseStart_2667677 baseEnd_2667677 := by
    simpa [prefixWord, tailWord_2667677, baseEnd_2667677] using wordTrace_append hprefix tailTrace_2667677
  have hstable : (prefixWord ++ tailWord_2667677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667677).length < 2 ^ (prefixWord ++ tailWord_2667677).sum := by decide
  have hdescent : baseEnd_2667677 < baseStart_2667677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_2667707 : Nat := 118140960795 + 2667707 * 2 ^ 59
def prefixEnd_2667707 : Nat := 4983230072969 + 3 ^ 40 * 2667707 * 2
def baseEnd_2667707 : Nat := 913210624242599545195963

theorem tailTrace_2667707 : CollatzResearch.WordTrace tailWord_2667707 prefixEnd_2667707 913210624242599545195963 := by
  unfold tailWord_2667707
  simp only [CollatzResearch.WordTrace]
  refine ⟨97299267746360621927897375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64866178497573747951931583 97299267746360621927897375)
  ·
    refine ⟨145948901619540932891846063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97299267746360621927897375 145948901619540932891846063)
    ·
      refine ⟨218923352429311399337769095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145948901619540932891846063 218923352429311399337769095)
      ·
        refine ⟨328385028643967099006653643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218923352429311399337769095 328385028643967099006653643)
        ·
          refine ⟨492577542965950648509980465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328385028643967099006653643 492577542965950648509980465)
          ·
            refine ⟨369433157224462986382485349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492577542965950648509980465 369433157224462986382485349)
            ·
              refine ⟨69268716979586809946716003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369433157224462986382485349 69268716979586809946716003)
              ·
                refine ⟨103903075469380214920074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69268716979586809946716003 103903075469380214920074005)
                ·
                  refine ⟨4870456662627197574378469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103903075469380214920074005 4870456662627197574378469)
                  ·
                    refine ⟨913210624242599545195963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870456662627197574378469 913210624242599545195963)
                    ·
                      rfl

theorem cell22_2667707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_2667707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667707 prefixEnd_2667707 := by exact prefixLift 2667707
  have htrace : WordTrace (prefixWord ++ tailWord_2667707) baseStart_2667707 baseEnd_2667707 := by
    simpa [prefixWord, tailWord_2667707, baseEnd_2667707] using wordTrace_append hprefix tailTrace_2667707
  have hstable : (prefixWord ++ tailWord_2667707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667707).length < 2 ^ (prefixWord ++ tailWord_2667707).sum := by decide
  have hdescent : baseEnd_2667707 < baseStart_2667707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667709 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2667709 : Nat := 118140960795 + 2667709 * 2 ^ 59
def prefixEnd_2667709 : Nat := 4983230072969 + 3 ^ 40 * 2667709 * 2
def baseEnd_2667709 : Nat := 913211308883472206645957

theorem tailTrace_2667709 : CollatzResearch.WordTrace tailWord_2667709 prefixEnd_2667709 913211308883472206645957 := by
  unfold tailWord_2667709
  simp only [CollatzResearch.WordTrace]
  refine ⟨97299340692353376269470181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64866227128235584179646787 97299340692353376269470181)
  ·
    refine ⟨18243626379816258050525659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97299340692353376269470181 18243626379816258050525659)
    ·
      refine ⟨27365439569724387075788489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18243626379816258050525659 27365439569724387075788489)
      ·
        refine ⟨20524079677293290306841367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27365439569724387075788489 20524079677293290306841367)
        ·
          refine ⟨30786119515939935460262051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20524079677293290306841367 30786119515939935460262051)
          ·
            refine ⟨46179179273909903190393077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30786119515939935460262051 46179179273909903190393077)
            ·
              refine ⟨4329298056929053424099351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46179179273909903190393077 4329298056929053424099351)
              ·
                refine ⟨6493947085393580136149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329298056929053424099351 6493947085393580136149027)
                ·
                  refine ⟨9740920628090370204223541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493947085393580136149027 9740920628090370204223541)
                  ·
                    refine ⟨913211308883472206645957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9740920628090370204223541 913211308883472206645957)
                    ·
                      rfl

theorem cell22_2667709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2667709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667709 prefixEnd_2667709 := by exact prefixLift 2667709
  have htrace : WordTrace (prefixWord ++ tailWord_2667709) baseStart_2667709 baseEnd_2667709 := by
    simpa [prefixWord, tailWord_2667709, baseEnd_2667709] using wordTrace_append hprefix tailTrace_2667709
  have hstable : (prefixWord ++ tailWord_2667709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667709).length < 2 ^ (prefixWord ++ tailWord_2667709).sum := by decide
  have hdescent : baseEnd_2667709 < baseStart_2667709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667713 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2667713 : Nat := 118140960795 + 2667713 * 2 ^ 59
def prefixEnd_2667713 : Nat := 4983230072969 + 3 ^ 40 * 2667713 * 2
def baseEnd_2667713 : Nat := 913212678165217529545945

theorem tailTrace_2667713 : CollatzResearch.WordTrace tailWord_2667713 prefixEnd_2667713 913212678165217529545945 := by
  unfold tailWord_2667713
  simp only [CollatzResearch.WordTrace]
  refine ⟨97299486584338884952615793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64866324389559256635077195 97299486584338884952615793)
  ·
    refine ⟨72974614938254163714461845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97299486584338884952615793 72974614938254163714461845)
    ·
      refine ⟨3420685075230663924115399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72974614938254163714461845 3420685075230663924115399)
      ·
        refine ⟨5131027612845995886173099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3420685075230663924115399 5131027612845995886173099)
        ·
          refine ⟨7696541419268993829259649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5131027612845995886173099 7696541419268993829259649)
          ·
            refine ⟨5772406064451745371944737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7696541419268993829259649 5772406064451745371944737)
            ·
              refine ⟨4329304548338809028958553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5772406064451745371944737 4329304548338809028958553)
              ·
                refine ⟨3246978411254106771718915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329304548338809028958553 3246978411254106771718915)
                ·
                  refine ⟨4870467616881160157578373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246978411254106771718915 4870467616881160157578373)
                  ·
                    refine ⟨913212678165217529545945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870467616881160157578373 913212678165217529545945)
                    ·
                      rfl

theorem cell22_2667713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2667713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667713 prefixEnd_2667713 := by exact prefixLift 2667713
  have htrace : WordTrace (prefixWord ++ tailWord_2667713) baseStart_2667713 baseEnd_2667713 := by
    simpa [prefixWord, tailWord_2667713, baseEnd_2667713] using wordTrace_append hprefix tailTrace_2667713
  have hstable : (prefixWord ++ tailWord_2667713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667713).length < 2 ^ (prefixWord ++ tailWord_2667713).sum := by decide
  have hdescent : baseEnd_2667713 < baseStart_2667713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667764 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2667764 : Nat := 118140960795 + 2667764 * 2 ^ 59
def prefixEnd_2667764 : Nat := 4983230072969 + 3 ^ 40 * 2667764 * 2
def baseEnd_2667764 : Nat := 913230136507470396520789

theorem tailTrace_2667764 : CollatzResearch.WordTrace tailWord_2667764 prefixEnd_2667764 913230136507470396520789 := by
  unfold tailWord_2667764
  simp only [CollatzResearch.WordTrace]
  refine ⟨48650673353577060331361173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64867564471436080441814897 48650673353577060331361173)
  ·
    refine ⟨2280500313448924703032555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48650673353577060331361173 2280500313448924703032555)
    ·
      refine ⟨3420750470173387054548833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280500313448924703032555 3420750470173387054548833)
      ·
        refine ⟨2565562852630040290911625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3420750470173387054548833 2565562852630040290911625)
        ·
          refine ⟨1924172139472530218183719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565562852630040290911625 1924172139472530218183719)
          ·
            refine ⟨2886258209208795327275579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924172139472530218183719 2886258209208795327275579)
            ·
              refine ⟨4329387313813192990913369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886258209208795327275579 4329387313813192990913369)
              ·
                refine ⟨3247040485359894743185027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329387313813192990913369 3247040485359894743185027)
                ·
                  refine ⟨4870560728039842114777541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247040485359894743185027 4870560728039842114777541)
                  ·
                    refine ⟨913230136507470396520789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870560728039842114777541 913230136507470396520789)
                    ·
                      rfl

theorem cell22_2667764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2667764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667764 prefixEnd_2667764 := by exact prefixLift 2667764
  have htrace : WordTrace (prefixWord ++ tailWord_2667764) baseStart_2667764 baseEnd_2667764 := by
    simpa [prefixWord, tailWord_2667764, baseEnd_2667764] using wordTrace_append hprefix tailTrace_2667764
  have hstable : (prefixWord ++ tailWord_2667764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667764).length < 2 ^ (prefixWord ++ tailWord_2667764).sum := by decide
  have hdescent : baseEnd_2667764 < baseStart_2667764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667799 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2667799 : Nat := 118140960795 + 2667799 * 2 ^ 59
def prefixEnd_2667799 : Nat := 4983230072969 + 3 ^ 40 * 2667799 * 2
def baseEnd_2667799 : Nat := 913242117722741971895681

theorem tailTrace_2667799 : CollatzResearch.WordTrace tailWord_2667799 prefixEnd_2667799 913242117722741971895681 := by
  unfold tailWord_2667799
  simp only [CollatzResearch.WordTrace]
  refine ⟨97302623262027321640246451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64868415508018214426830967 97302623262027321640246451)
  ·
    refine ⟨145953934893040982460369677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97302623262027321640246451 145953934893040982460369677)
    ·
      refine ⟨54732725584890368422638629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145953934893040982460369677 54732725584890368422638629)
      ·
        refine ⟨10262386047166944079244743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54732725584890368422638629 10262386047166944079244743)
        ·
          refine ⟨15393579070750416118867115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10262386047166944079244743 15393579070750416118867115)
          ·
            refine ⟨23090368606125624178300673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15393579070750416118867115 23090368606125624178300673)
            ·
              refine ⟨17317776454594218133725505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23090368606125624178300673 17317776454594218133725505)
              ·
                refine ⟨12988332340945663600294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17317776454594218133725505 12988332340945663600294129)
                ·
                  refine ⟨9741249255709247700220597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12988332340945663600294129 9741249255709247700220597)
                  ·
                    refine ⟨913242117722741971895681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9741249255709247700220597 913242117722741971895681)
                    ·
                      rfl

theorem cell22_2667799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2667799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667799 prefixEnd_2667799 := by exact prefixLift 2667799
  have htrace : WordTrace (prefixWord ++ tailWord_2667799) baseStart_2667799 baseEnd_2667799 := by
    simpa [prefixWord, tailWord_2667799, baseEnd_2667799] using wordTrace_append hprefix tailTrace_2667799
  have hstable : (prefixWord ++ tailWord_2667799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667799).length < 2 ^ (prefixWord ++ tailWord_2667799).sum := by decide
  have hdescent : baseEnd_2667799 < baseStart_2667799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667805 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2667805 : Nat := 118140960795 + 2667805 * 2 ^ 59
def prefixEnd_2667805 : Nat := 4983230072969 + 3 ^ 40 * 2667805 * 2
def baseEnd_2667805 : Nat := 913244171645359956245663

theorem tailTrace_2667805 : CollatzResearch.WordTrace tailWord_2667805 prefixEnd_2667805 913244171645359956245663 := by
  unfold tailWord_2667805
  simp only [CollatzResearch.WordTrace]
  refine ⟨97302842100005584664964869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64868561400003723109976579 97302842100005584664964869)
  ·
    refine ⟨18244282893751047124680913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97302842100005584664964869 18244282893751047124680913)
    ·
      refine ⟨13683212170313285343510685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18244282893751047124680913 13683212170313285343510685)
      ·
        refine ⟨5131204563867482003816507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13683212170313285343510685 5131204563867482003816507)
        ·
          refine ⟨7696806845801223005724761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5131204563867482003816507 7696806845801223005724761)
          ·
            refine ⟨5772605134350917254293571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7696806845801223005724761 5772605134350917254293571)
            ·
              refine ⟨8658907701526375881440357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772605134350917254293571 8658907701526375881440357)
              ·
                refine ⟨1623545194036195477770067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8658907701526375881440357 1623545194036195477770067)
                ·
                  refine ⟨2435317791054293216655101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623545194036195477770067 2435317791054293216655101)
                  ·
                    refine ⟨913244171645359956245663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435317791054293216655101 913244171645359956245663)
                    ·
                      rfl

theorem cell22_2667805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2667805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667805 prefixEnd_2667805 := by exact prefixLift 2667805
  have htrace : WordTrace (prefixWord ++ tailWord_2667805) baseStart_2667805 baseEnd_2667805 := by
    simpa [prefixWord, tailWord_2667805, baseEnd_2667805] using wordTrace_append hprefix tailTrace_2667805
  have hstable : (prefixWord ++ tailWord_2667805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667805).length < 2 ^ (prefixWord ++ tailWord_2667805).sum := by decide
  have hdescent : baseEnd_2667805 < baseStart_2667805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667816 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2667816 : Nat := 118140960795 + 2667816 * 2 ^ 59
def prefixEnd_2667816 : Nat := 4983230072969 + 3 ^ 40 * 2667816 * 2
def baseEnd_2667816 : Nat := 913247937170159594220629

theorem tailTrace_2667816 : CollatzResearch.WordTrace tailWord_2667816 prefixEnd_2667816 913247937170159594220629 := by
  unfold tailWord_2667816
  simp only [CollatzResearch.WordTrace]
  refine ⟨48651621651482866771807651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64868828868643822362410201 48651621651482866771807651)
  ·
    refine ⟨72977432477224300157711477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48651621651482866771807651 72977432477224300157711477)
    ·
      refine ⟨6841634294739778139785451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72977432477224300157711477 6841634294739778139785451)
      ·
        refine ⟨10262451442109667209678177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6841634294739778139785451 10262451442109667209678177)
        ·
          refine ⟨7696838581582250407258633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10262451442109667209678177 7696838581582250407258633)
          ·
            refine ⟨5772628936186687805443975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7696838581582250407258633 5772628936186687805443975)
            ·
              refine ⟨8658943404280031708165963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772628936186687805443975 8658943404280031708165963)
              ·
                refine ⟨12988415106420047562248945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8658943404280031708165963 12988415106420047562248945)
                ·
                  refine ⟨9741311329815035671686709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12988415106420047562248945 9741311329815035671686709)
                  ·
                    refine ⟨913247937170159594220629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9741311329815035671686709 913247937170159594220629)
                    ·
                      rfl

theorem cell22_2667816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2667816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667816 prefixEnd_2667816 := by exact prefixLift 2667816
  have htrace : WordTrace (prefixWord ++ tailWord_2667816) baseStart_2667816 baseEnd_2667816 := by
    simpa [prefixWord, tailWord_2667816, baseEnd_2667816] using wordTrace_append hprefix tailTrace_2667816
  have hstable : (prefixWord ++ tailWord_2667816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667816).length < 2 ^ (prefixWord ++ tailWord_2667816).sum := by decide
  have hdescent : baseEnd_2667816 < baseStart_2667816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667829 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 8]
def baseStart_2667829 : Nat := 118140960795 + 2667829 * 2 ^ 59
def prefixEnd_2667829 : Nat := 4983230072969 + 3 ^ 40 * 2667829 * 2
def baseEnd_2667829 : Nat := 304417462445277297881863

theorem tailTrace_2667829 : CollatzResearch.WordTrace tailWord_2667829 prefixEnd_2667829 304417462445277297881863 := by
  unfold tailWord_2667829
  simp only [CollatzResearch.WordTrace]
  refine ⟨97303717451918636763838541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64869144967945757842559027 97303717451918636763838541)
  ·
    refine ⟨36488894044469488786439453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97303717451918636763838541 36488894044469488786439453)
    ·
      refine ⟨13683335266676058294914795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36488894044469488786439453 13683335266676058294914795)
      ·
        refine ⟨20525002900014087442372193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13683335266676058294914795 20525002900014087442372193)
        ·
          refine ⟨15393752175010565581779145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20525002900014087442372193 15393752175010565581779145)
          ·
            refine ⟨11545314131257924186334359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15393752175010565581779145 11545314131257924186334359)
            ·
              refine ⟨17317971196886886279501539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11545314131257924186334359 17317971196886886279501539)
              ·
                refine ⟨25976956795330329419252309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17317971196886886279501539 25976956795330329419252309)
                ·
                  refine ⟨304417462445277297881863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25976956795330329419252309 304417462445277297881863)
                  ·
                    rfl

theorem cell22_2667829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_2667829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667829 prefixEnd_2667829 := by exact prefixLift 2667829
  have htrace : WordTrace (prefixWord ++ tailWord_2667829) baseStart_2667829 baseEnd_2667829 := by
    simpa [prefixWord, tailWord_2667829, baseEnd_2667829] using wordTrace_append hprefix tailTrace_2667829
  have hstable : (prefixWord ++ tailWord_2667829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667829).length < 2 ^ (prefixWord ++ tailWord_2667829).sum := by decide
  have hdescent : baseEnd_2667829 < baseStart_2667829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667859 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_2667859 : Nat := 118140960795 + 2667859 * 2 ^ 59
def prefixEnd_2667859 : Nat := 4983230072969 + 3 ^ 40 * 2667859 * 2
def baseEnd_2667859 : Nat := 913262656948921815395497

theorem tailTrace_2667859 : CollatzResearch.WordTrace tailWord_2667859 prefixEnd_2667859 913262656948921815395497 := by
  unfold tailWord_2667859
  simp only [CollatzResearch.WordTrace]
  refine ⟨97304811641809951887430631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64869874427873301258287087 97304811641809951887430631)
  ·
    refine ⟨145957217462714927831145947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97304811641809951887430631 145957217462714927831145947)
    ·
      refine ⟨218935826194072391746718921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145957217462714927831145947 218935826194072391746718921)
      ·
        refine ⟨164201869645554293810039191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218935826194072391746718921 164201869645554293810039191)
        ·
          refine ⟨246302804468331440715058787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164201869645554293810039191 246302804468331440715058787)
          ·
            refine ⟨369454206702497161072588181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246302804468331440715058787 369454206702497161072588181)
            ·
              refine ⟨17318165939179554425277571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 369454206702497161072588181 17318165939179554425277571)
              ·
                refine ⟨25977248908769331637916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17318165939179554425277571 25977248908769331637916357)
                ·
                  refine ⟨4870734170394249682109317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25977248908769331637916357 4870734170394249682109317)
                  ·
                    refine ⟨913262656948921815395497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4870734170394249682109317 913262656948921815395497)
                    ·
                      rfl

theorem cell22_2667859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_2667859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667859 prefixEnd_2667859 := by exact prefixLift 2667859
  have htrace : WordTrace (prefixWord ++ tailWord_2667859) baseStart_2667859 baseEnd_2667859 := by
    simpa [prefixWord, tailWord_2667859, baseEnd_2667859] using wordTrace_append hprefix tailTrace_2667859
  have hstable : (prefixWord ++ tailWord_2667859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667859).length < 2 ^ (prefixWord ++ tailWord_2667859).sum := by decide
  have hdescent : baseEnd_2667859 < baseStart_2667859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667936 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_2667936 : Nat := 118140960795 + 2667936 * 2 ^ 59
def prefixEnd_2667936 : Nat := 4983230072969 + 3 ^ 40 * 2667936 * 2
def baseEnd_2667936 : Nat := 304429671874173093740087

theorem tailTrace_2667936 : CollatzResearch.WordTrace tailWord_2667936 prefixEnd_2667936 304429671874173093740087 := by
  unfold tailWord_2667936
  simp only [CollatzResearch.WordTrace]
  refine ⟨48653810031265497018991831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64871746708353996025322441 48653810031265497018991831)
  ·
    refine ⟨72980715046898245528487747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48653810031265497018991831 72980715046898245528487747)
    ·
      refine ⟨109471072570347368292731621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72980715046898245528487747 109471072570347368292731621)
      ·
        refine ⟨20525826106940131554887179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109471072570347368292731621 20525826106940131554887179)
        ·
          refine ⟨30788739160410197332330769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20525826106940131554887179 30788739160410197332330769)
          ·
            refine ⟨23091554370307647999248077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30788739160410197332330769 23091554370307647999248077)
            ·
              refine ⟨8659332888865367999718029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23091554370307647999248077 8659332888865367999718029)
              ·
                refine ⟨3247249833324512999894261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8659332888865367999718029 3247249833324512999894261)
                ·
                  refine ⟨304429671874173093740087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3247249833324512999894261 304429671874173093740087)
                  ·
                    rfl

theorem cell22_2667936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_2667936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2667936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2667936 prefixEnd_2667936 := by exact prefixLift 2667936
  have htrace : WordTrace (prefixWord ++ tailWord_2667936) baseStart_2667936 baseEnd_2667936 := by
    simpa [prefixWord, tailWord_2667936, baseEnd_2667936] using wordTrace_append hprefix tailTrace_2667936
  have hstable : (prefixWord ++ tailWord_2667936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667936).length < 2 ^ (prefixWord ++ tailWord_2667936).sum := by decide
  have hdescent : baseEnd_2667936 < baseStart_2667936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668011 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_2668011 : Nat := 118140960795 + 2668011 * 2 ^ 59
def prefixEnd_2668011 : Nat := 4983230072969 + 3 ^ 40 * 2668011 * 2
def baseEnd_2668011 : Nat := 913314689655244085595031

theorem tailTrace_2668011 : CollatzResearch.WordTrace tailWord_2668011 prefixEnd_2668011 913314689655244085595031 := by
  unfold tailWord_2668011
  simp only [CollatzResearch.WordTrace]
  refine ⟨97310355537259281846963887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64873570358172854564642591 97310355537259281846963887)
  ·
    refine ⟨145965533305888922770445831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97310355537259281846963887 145965533305888922770445831)
    ·
      refine ⟨218948299958833384155668747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145965533305888922770445831 218948299958833384155668747)
      ·
        refine ⟨328422449938250076233503121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218948299958833384155668747 328422449938250076233503121)
        ·
          refine ⟨246316837453687557175127341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328422449938250076233503121 246316837453687557175127341)
          ·
            refine ⟨92368814045132833940672753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246316837453687557175127341 92368814045132833940672753)
            ·
              refine ⟨69276610533849625455504565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92368814045132833940672753 69276610533849625455504565)
              ·
                refine ⟨6494682237548402386453553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69276610533849625455504565 6494682237548402386453553)
                ·
                  refine ⟨4871011678161301789840165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6494682237548402386453553 4871011678161301789840165)
                  ·
                    refine ⟨913314689655244085595031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871011678161301789840165 913314689655244085595031)
                    ·
                      rfl

theorem cell22_2668011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_2668011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668011 prefixEnd_2668011 := by exact prefixLift 2668011
  have htrace : WordTrace (prefixWord ++ tailWord_2668011) baseStart_2668011 baseEnd_2668011 := by
    simpa [prefixWord, tailWord_2668011, baseEnd_2668011] using wordTrace_append hprefix tailTrace_2668011
  have hstable : (prefixWord ++ tailWord_2668011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668011).length < 2 ^ (prefixWord ++ tailWord_2668011).sum := by decide
  have hdescent : baseEnd_2668011 < baseStart_2668011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668092 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_2668092 : Nat := 118140960795 + 2668092 * 2 ^ 59
def prefixEnd_2668092 : Nat := 4983230072969 + 3 ^ 40 * 2668092 * 2
def baseEnd_2668092 : Nat := 913342417610586874319783

theorem tailTrace_2668092 : CollatzResearch.WordTrace tailWord_2668092 prefixEnd_2668092 913342417610586874319783 := by
  unfold tailWord_2668092
  simp only [CollatzResearch.WordTrace]
  refine ⟨48656654924982916340331265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64875539899977221787108353 48656654924982916340331265)
  ·
    refine ⟨36492491193737187255248449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48656654924982916340331265 36492491193737187255248449)
    ·
      refine ⟨27369368395302890441436337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36492491193737187255248449 27369368395302890441436337)
      ·
        refine ⟨20527026296477167831077253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27369368395302890441436337 20527026296477167831077253)
        ·
          refine ⟨3848817430589468968326985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20527026296477167831077253 3848817430589468968326985)
          ·
            refine ⟨2886613072942101726245239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3848817430589468968326985 2886613072942101726245239)
            ·
              refine ⟨4329919609413152589367859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886613072942101726245239 4329919609413152589367859)
              ·
                refine ⟨6494879414119728884051789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329919609413152589367859 6494879414119728884051789)
                ·
                  refine ⟨2435579780294898331519421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6494879414119728884051789 2435579780294898331519421)
                  ·
                    refine ⟨913342417610586874319783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435579780294898331519421 913342417610586874319783)
                    ·
                      rfl

theorem cell22_2668092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_2668092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668092 prefixEnd_2668092 := by exact prefixLift 2668092
  have htrace : WordTrace (prefixWord ++ tailWord_2668092) baseStart_2668092 baseEnd_2668092 := by
    simpa [prefixWord, tailWord_2668092, baseEnd_2668092] using wordTrace_append hprefix tailTrace_2668092
  have hstable : (prefixWord ++ tailWord_2668092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668092).length < 2 ^ (prefixWord ++ tailWord_2668092).sum := by decide
  have hdescent : baseEnd_2668092 < baseStart_2668092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668165 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2668165 : Nat := 118140960795 + 2668165 * 2 ^ 59
def prefixEnd_2668165 : Nat := 4983230072969 + 3 ^ 40 * 2668165 * 2
def baseEnd_2668165 : Nat := 913367407002439017244559

theorem tailTrace_2668165 : CollatzResearch.WordTrace tailWord_2668165 prefixEnd_2668165 913367407002439017244559 := by
  unfold tailWord_2668165
  simp only [CollatzResearch.WordTrace]
  refine ⟨97315972378701366148069949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64877314919134244098713299 97315972378701366148069949)
  ·
    refine ⟨36493489642013012305526231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97315972378701366148069949 36493489642013012305526231)
    ·
      refine ⟨54740234463019518458289347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36493489642013012305526231 54740234463019518458289347)
      ·
        refine ⟨82110351694529277687434021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54740234463019518458289347 82110351694529277687434021)
        ·
          refine ⟨15395690942724239566393879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82110351694529277687434021 15395690942724239566393879)
          ·
            refine ⟨23093536414086359349590819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15395690942724239566393879 23093536414086359349590819)
            ·
              refine ⟨34640304621129539024386229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23093536414086359349590819 34640304621129539024386229)
              ·
                refine ⟨3247528558230894283536209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34640304621129539024386229 3247528558230894283536209)
                ·
                  refine ⟨2435646418673170712652157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247528558230894283536209 2435646418673170712652157)
                  ·
                    refine ⟨913367407002439017244559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435646418673170712652157 913367407002439017244559)
                    ·
                      rfl

theorem cell22_2668165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2668165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668165 prefixEnd_2668165 := by exact prefixLift 2668165
  have htrace : WordTrace (prefixWord ++ tailWord_2668165) baseStart_2668165 baseEnd_2668165 := by
    simpa [prefixWord, tailWord_2668165, baseEnd_2668165] using wordTrace_append hprefix tailTrace_2668165
  have hstable : (prefixWord ++ tailWord_2668165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668165).length < 2 ^ (prefixWord ++ tailWord_2668165).sum := by decide
  have hdescent : baseEnd_2668165 < baseStart_2668165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668210 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_2668210 : Nat := 118140960795 + 2668210 * 2 ^ 59
def prefixEnd_2668210 : Nat := 4983230072969 + 3 ^ 40 * 2668210 * 2
def baseEnd_2668210 : Nat := 913382811422073899869421

theorem tailTrace_2668210 : CollatzResearch.WordTrace tailWord_2668210 prefixEnd_2668210 913382811422073899869421 := by
  unfold tailWord_2668210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329403415884584708364521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64878409109025559222305389 24329403415884584708364521)
  ·
    refine ⟨18247052561913438531273391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24329403415884584708364521 18247052561913438531273391)
    ·
      refine ⟨27370578842870157796910087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18247052561913438531273391 27370578842870157796910087)
      ·
        refine ⟨41055868264305236695365131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27370578842870157796910087 41055868264305236695365131)
        ·
          refine ⟨61583802396457855043047697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41055868264305236695365131 61583802396457855043047697)
          ·
            refine ⟨46187851797343391282285773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61583802396457855043047697 46187851797343391282285773)
            ·
              refine ⟨17320444424003771730857165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46187851797343391282285773 17320444424003771730857165)
              ·
                refine ⟨6495166659001414399071437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17320444424003771730857165 6495166659001414399071437)
                ·
                  refine ⟨2435687497125530399651789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6495166659001414399071437 2435687497125530399651789)
                  ·
                    refine ⟨913382811422073899869421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435687497125530399651789 913382811422073899869421)
                    ·
                      rfl

theorem cell22_2668210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_2668210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668210 prefixEnd_2668210 := by exact prefixLift 2668210
  have htrace : WordTrace (prefixWord ++ tailWord_2668210) baseStart_2668210 baseEnd_2668210 := by
    simpa [prefixWord, tailWord_2668210, baseEnd_2668210] using wordTrace_append hprefix tailTrace_2668210
  have hstable : (prefixWord ++ tailWord_2668210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668210).length < 2 ^ (prefixWord ++ tailWord_2668210).sum := by decide
  have hdescent : baseEnd_2668210 < baseStart_2668210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668270 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2668270 : Nat := 118140960795 + 2668270 * 2 ^ 59
def prefixEnd_2668270 : Nat := 4983230072969 + 3 ^ 40 * 2668270 * 2
def baseEnd_2668270 : Nat := 913403350648253743369237

theorem tailTrace_2668270 : CollatzResearch.WordTrace tailWord_2668270 prefixEnd_2668270 913403350648253743369237 := by
  unfold tailWord_2668270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12164975255415121135080283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64879868028880646053761509 12164975255415121135080283)
  ·
    refine ⟨18247462883122681702620425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12164975255415121135080283 18247462883122681702620425)
    ·
      refine ⟨13685597162342011276965319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18247462883122681702620425 13685597162342011276965319)
      ·
        refine ⟨20528395743513016915447979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13685597162342011276965319 20528395743513016915447979)
        ·
          refine ⟨30792593615269525373171969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20528395743513016915447979 30792593615269525373171969)
          ·
            refine ⟨23094445211452144029878977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30792593615269525373171969 23094445211452144029878977)
            ·
              refine ⟨17320833908589108022409233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23094445211452144029878977 17320833908589108022409233)
              ·
                refine ⟨12990625431441831016806925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17320833908589108022409233 12990625431441831016806925)
                ·
                  refine ⟨4871484536790686631302597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12990625431441831016806925 4871484536790686631302597)
                  ·
                    refine ⟨913403350648253743369237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871484536790686631302597 913403350648253743369237)
                    ·
                      rfl

theorem cell22_2668270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2668270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668270 prefixEnd_2668270 := by exact prefixLift 2668270
  have htrace : WordTrace (prefixWord ++ tailWord_2668270) baseStart_2668270 baseEnd_2668270 := by
    simpa [prefixWord, tailWord_2668270, baseEnd_2668270] using wordTrace_append hprefix tailTrace_2668270
  have hstable : (prefixWord ++ tailWord_2668270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668270).length < 2 ^ (prefixWord ++ tailWord_2668270).sum := by decide
  have hdescent : baseEnd_2668270 < baseStart_2668270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668300 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_2668300 : Nat := 118140960795 + 2668300 * 2 ^ 59
def prefixEnd_2668300 : Nat := 4983230072969 + 3 ^ 40 * 2668300 * 2
def baseEnd_2668300 : Nat := 913413620261343665119145

theorem tailTrace_2668300 : CollatzResearch.WordTrace tailWord_2668300 prefixEnd_2668300 913413620261343665119145 := by
  unfold tailWord_2668300
  simp only [CollatzResearch.WordTrace]
  refine ⟨48660448116606142102117177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64880597488808189469489569 48660448116606142102117177)
  ·
    refine ⟨36495336087454606576587883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48660448116606142102117177 36495336087454606576587883)
    ·
      refine ⟨54743004131181909864881825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36495336087454606576587883 54743004131181909864881825)
      ·
        refine ⟨41057253098386432398661369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54743004131181909864881825 41057253098386432398661369)
        ·
          refine ⟨30792939823789824298996027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41057253098386432398661369 30792939823789824298996027)
          ·
            refine ⟨46189409735684736448494041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30792939823789824298996027 46189409735684736448494041)
            ·
              refine ⟨34642057301763552336370531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46189409735684736448494041 34642057301763552336370531)
              ·
                refine ⟨51963085952645328504555797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34642057301763552336370531 51963085952645328504555797)
                ·
                  refine ⟨2435769654030249773651053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51963085952645328504555797 2435769654030249773651053)
                  ·
                    refine ⟨913413620261343665119145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435769654030249773651053 913413620261343665119145)
                    ·
                      rfl

theorem cell22_2668300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_2668300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668300 prefixEnd_2668300 := by exact prefixLift 2668300
  have htrace : WordTrace (prefixWord ++ tailWord_2668300) baseStart_2668300 baseEnd_2668300 := by
    simpa [prefixWord, tailWord_2668300, baseEnd_2668300] using wordTrace_append hprefix tailTrace_2668300
  have hstable : (prefixWord ++ tailWord_2668300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668300).length < 2 ^ (prefixWord ++ tailWord_2668300).sum := by decide
  have hdescent : baseEnd_2668300 < baseStart_2668300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668334 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2668334 : Nat := 118140960795 + 2668334 * 2 ^ 59
def prefixEnd_2668334 : Nat := 4983230072969 + 3 ^ 40 * 2668334 * 2
def baseEnd_2668334 : Nat := 913425259156178909769041

theorem tailTrace_2668334 : CollatzResearch.WordTrace tailWord_2668334 prefixEnd_2668334 913425259156178909769041 := by
  unfold tailWord_2668334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165267039386138501371507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64881424210059405340648037 12165267039386138501371507)
  ·
    refine ⟨18247900559079207752057261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12165267039386138501371507 18247900559079207752057261)
    ·
      refine ⟨6842962709654702907021473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18247900559079207752057261 6842962709654702907021473)
      ·
        refine ⟨5132222032241027180266105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6842962709654702907021473 5132222032241027180266105)
        ·
          refine ⟨3849166524180770385199579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5132222032241027180266105 3849166524180770385199579)
          ·
            refine ⟨5773749786271155577799369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849166524180770385199579 5773749786271155577799369)
            ·
              refine ⟨4330312339703366683349527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5773749786271155577799369 4330312339703366683349527)
              ·
                refine ⟨6495468509555050025024291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330312339703366683349527 6495468509555050025024291)
                ·
                  refine ⟨9743202764332575037536437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6495468509555050025024291 9743202764332575037536437)
                  ·
                    refine ⟨913425259156178909769041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9743202764332575037536437 913425259156178909769041)
                    ·
                      rfl

theorem cell22_2668334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2668334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668334 prefixEnd_2668334 := by exact prefixLift 2668334
  have htrace : WordTrace (prefixWord ++ tailWord_2668334) baseStart_2668334 baseEnd_2668334 := by
    simpa [prefixWord, tailWord_2668334, baseEnd_2668334] using wordTrace_append hprefix tailTrace_2668334
  have hstable : (prefixWord ++ tailWord_2668334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668334).length < 2 ^ (prefixWord ++ tailWord_2668334).sum := by decide
  have hdescent : baseEnd_2668334 < baseStart_2668334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668349 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_2668349 : Nat := 118140960795 + 2668349 * 2 ^ 59
def prefixEnd_2668349 : Nat := 4983230072969 + 3 ^ 40 * 2668349 * 2
def baseEnd_2668349 : Nat := 913430393962723870643995

theorem tailTrace_2668349 : CollatzResearch.WordTrace tailWord_2668349 prefixEnd_2668349 913430393962723870643995 := by
  unfold tailWord_2668349
  simp only [CollatzResearch.WordTrace]
  refine ⟨97322683410034765572768101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64881788940023177048512067 97322683410034765572768101)
  ·
    refine ⟨18248003139381518544894019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97322683410034765572768101 18248003139381518544894019)
    ·
      refine ⟨27372004709072277817341029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248003139381518544894019 27372004709072277817341029)
      ·
        refine ⟨5132250882951052090751443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27372004709072277817341029 5132250882951052090751443)
        ·
          refine ⟨7698376324426578136127165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132250882951052090751443 7698376324426578136127165)
          ·
            refine ⟨2886891121659966801047687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7698376324426578136127165 2886891121659966801047687)
            ·
              refine ⟨4330336682489950201571531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886891121659966801047687 4330336682489950201571531)
              ·
                refine ⟨6495505023734925302357297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330336682489950201571531 6495505023734925302357297)
                ·
                  refine ⟨4871628767801193976767973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495505023734925302357297 4871628767801193976767973)
                  ·
                    refine ⟨913430393962723870643995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871628767801193976767973 913430393962723870643995)
                    ·
                      rfl

theorem cell22_2668349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_2668349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668349 prefixEnd_2668349 := by exact prefixLift 2668349
  have htrace : WordTrace (prefixWord ++ tailWord_2668349) baseStart_2668349 baseEnd_2668349 := by
    simpa [prefixWord, tailWord_2668349, baseEnd_2668349] using wordTrace_append hprefix tailTrace_2668349
  have hstable : (prefixWord ++ tailWord_2668349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668349).length < 2 ^ (prefixWord ++ tailWord_2668349).sum := by decide
  have hdescent : baseEnd_2668349 < baseStart_2668349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668420 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2668420 : Nat := 118140960795 + 2668420 * 2 ^ 59
def prefixEnd_2668420 : Nat := 4983230072969 + 3 ^ 40 * 2668420 * 2
def baseEnd_2668420 : Nat := 304484899571234450706259

theorem tailTrace_2668420 : CollatzResearch.WordTrace tailWord_2668420 prefixEnd_2668420 304484899571234450706259 := by
  unfold tailWord_2668420
  simp only [CollatzResearch.WordTrace]
  refine ⟨48662636496388772349301357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64883515328518363132401809 48662636496388772349301357)
  ·
    refine ⟨18248488686145789630988009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48662636496388772349301357 18248488686145789630988009)
    ·
      refine ⟨13686366514609342223241007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18248488686145789630988009 13686366514609342223241007)
      ·
        refine ⟨20529549771914013334861511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13686366514609342223241007 20529549771914013334861511)
        ·
          refine ⟨30794324657871020002292267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20529549771914013334861511 30794324657871020002292267)
          ·
            refine ⟨46191486986806530003438401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30794324657871020002292267 46191486986806530003438401)
            ·
              refine ⟨34643615240104897502578801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46191486986806530003438401 34643615240104897502578801)
              ·
                refine ⟨25982711430078673126934101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34643615240104897502578801 25982711430078673126934101)
                ·
                  refine ⟨304484899571234450706259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25982711430078673126934101 304484899571234450706259)
                  ·
                    rfl

theorem cell22_2668420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2668420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668420 prefixEnd_2668420 := by exact prefixLift 2668420
  have htrace : WordTrace (prefixWord ++ tailWord_2668420) baseStart_2668420 baseEnd_2668420 := by
    simpa [prefixWord, tailWord_2668420, baseEnd_2668420] using wordTrace_append hprefix tailTrace_2668420
  have hstable : (prefixWord ++ tailWord_2668420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668420).length < 2 ^ (prefixWord ++ tailWord_2668420).sum := by decide
  have hdescent : baseEnd_2668420 < baseStart_2668420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668430 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_2668430 : Nat := 118140960795 + 2668430 * 2 ^ 59
def prefixEnd_2668430 : Nat := 4983230072969 + 3 ^ 40 * 2668430 * 2
def baseEnd_2668430 : Nat := 913458121918066659368747

theorem tailTrace_2668430 : CollatzResearch.WordTrace tailWord_2668430 prefixEnd_2668430 913458121918066659368747 := by
  unfold tailWord_2668430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165704715342664550808343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64883758481827544270977829 12165704715342664550808343)
  ·
    refine ⟨18248557073013996826212515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12165704715342664550808343 18248557073013996826212515)
    ·
      refine ⟨27372835609520995239318773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248557073013996826212515 27372835609520995239318773)
      ·
        refine ⟨2566203338392593303686135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27372835609520995239318773 2566203338392593303686135)
        ·
          refine ⟨3849305007588889955529203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566203338392593303686135 3849305007588889955529203)
          ·
            refine ⟨5773957511383334933293805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849305007588889955529203 5773957511383334933293805)
            ·
              refine ⟨2165234066768750599985177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5773957511383334933293805 2165234066768750599985177)
              ·
                refine ⟨1623925550076562949988883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165234066768750599985177 1623925550076562949988883)
                ·
                  refine ⟨2435888325114844424983325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623925550076562949988883 2435888325114844424983325)
                  ·
                    refine ⟨913458121918066659368747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435888325114844424983325 913458121918066659368747)
                    ·
                      rfl

theorem cell22_2668430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_2668430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668430 prefixEnd_2668430 := by exact prefixLift 2668430
  have htrace : WordTrace (prefixWord ++ tailWord_2668430) baseStart_2668430 baseEnd_2668430 := by
    simpa [prefixWord, tailWord_2668430, baseEnd_2668430] using wordTrace_append hprefix tailTrace_2668430
  have hstable : (prefixWord ++ tailWord_2668430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668430).length < 2 ^ (prefixWord ++ tailWord_2668430).sum := by decide
  have hdescent : baseEnd_2668430 < baseStart_2668430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668456 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2668456 : Nat := 118140960795 + 2668456 * 2 ^ 59
def prefixEnd_2668456 : Nat := 4983230072969 + 3 ^ 40 * 2668456 * 2
def baseEnd_2668456 : Nat := 913467022249411258218667

theorem tailTrace_2668456 : CollatzResearch.WordTrace tailWord_2668456 prefixEnd_2668456 913467022249411258218667 := by
  unfold tailWord_2668456
  simp only [CollatzResearch.WordTrace]
  refine ⟨48663293010323561423456611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64884390680431415231275481 48663293010323561423456611)
  ·
    refine ⟨72994939515485342135184917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48663293010323561423456611 72994939515485342135184917)
    ·
      refine ⟨3421637789788375412586793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72994939515485342135184917 3421637789788375412586793)
      ·
        refine ⟨2566228342341281559440095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3421637789788375412586793 2566228342341281559440095)
        ·
          refine ⟨3849342513511922339160143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566228342341281559440095 3849342513511922339160143)
          ·
            refine ⟨5774013770267883508740215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849342513511922339160143 5774013770267883508740215)
            ·
              refine ⟨8661020655401825263110323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774013770267883508740215 8661020655401825263110323)
              ·
                refine ⟨12991530983102737894665485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661020655401825263110323 12991530983102737894665485)
                ·
                  refine ⟨4871824118663526710499557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12991530983102737894665485 4871824118663526710499557)
                  ·
                    refine ⟨913467022249411258218667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871824118663526710499557 913467022249411258218667)
                    ·
                      rfl

theorem cell22_2668456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2668456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668456 prefixEnd_2668456 := by exact prefixLift 2668456
  have htrace : WordTrace (prefixWord ++ tailWord_2668456) baseStart_2668456 baseEnd_2668456 := by
    simpa [prefixWord, tailWord_2668456, baseEnd_2668456] using wordTrace_append hprefix tailTrace_2668456
  have hstable : (prefixWord ++ tailWord_2668456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668456).length < 2 ^ (prefixWord ++ tailWord_2668456).sum := by decide
  have hdescent : baseEnd_2668456 < baseStart_2668456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668467 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 2, 4]
def baseStart_2668467 : Nat := 118140960795 + 2668467 * 2 ^ 59
def prefixEnd_2668467 : Nat := 4983230072969 + 3 ^ 40 * 2668467 * 2
def baseEnd_2668467 : Nat := 913470787774210896193633

theorem tailTrace_2668467 : CollatzResearch.WordTrace tailWord_2668467 prefixEnd_2668467 913470787774210896193633 := by
  unfold tailWord_2668467
  simp only [CollatzResearch.WordTrace]
  refine ⟨97326987223607271725563655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64884658149071514483709103 97326987223607271725563655)
  ·
    refine ⟨145990480835410907588345483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97326987223607271725563655 145990480835410907588345483)
    ·
      refine ⟨218985721253116361382518225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145990480835410907588345483 218985721253116361382518225)
      ·
        refine ⟨164239290939837271036888669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218985721253116361382518225 164239290939837271036888669)
        ·
          refine ⟨61589734102438976638833251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164239290939837271036888669 61589734102438976638833251)
          ·
            refine ⟨92384601153658464958249877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61589734102438976638833251 92384601153658464958249877)
            ·
              refine ⟨4330528179077740544917963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92384601153658464958249877 4330528179077740544917963)
              ·
                refine ⟨6495792268616610817376945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330528179077740544917963 6495792268616610817376945)
                ·
                  refine ⟨4871844201462458113032709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495792268616610817376945 4871844201462458113032709)
                  ·
                    refine ⟨913470787774210896193633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4871844201462458113032709 913470787774210896193633)
                    ·
                      rfl

theorem cell22_2668467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_2668467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668467 prefixEnd_2668467 := by exact prefixLift 2668467
  have htrace : WordTrace (prefixWord ++ tailWord_2668467) baseStart_2668467 baseEnd_2668467 := by
    simpa [prefixWord, tailWord_2668467, baseEnd_2668467] using wordTrace_append hprefix tailTrace_2668467
  have hstable : (prefixWord ++ tailWord_2668467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668467).length < 2 ^ (prefixWord ++ tailWord_2668467).sum := by decide
  have hdescent : baseEnd_2668467 < baseStart_2668467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668495 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2668495 : Nat := 118140960795 + 2668495 * 2 ^ 59
def prefixEnd_2668495 : Nat := 4983230072969 + 3 ^ 40 * 2668495 * 2
def baseEnd_2668495 : Nat := 913480372746428156493547

theorem tailTrace_2668495 : CollatzResearch.WordTrace tailWord_2668495 prefixEnd_2668495 913480372746428156493547 := by
  unfold tailWord_2668495
  simp only [CollatzResearch.WordTrace]
  refine ⟨97328008467505832507582939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64885338978337221671721959 97328008467505832507582939)
  ·
    refine ⟨145992012701258748761374409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97328008467505832507582939 145992012701258748761374409)
    ·
      refine ⟨109494009525944061571030807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145992012701258748761374409 109494009525944061571030807)
      ·
        refine ⟨164241014288916092356546211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109494009525944061571030807 164241014288916092356546211)
        ·
          refine ⟨246361521433374138534819317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164241014288916092356546211 246361521433374138534819317)
          ·
            refine ⟨23096392634378825487639311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246361521433374138534819317 23096392634378825487639311)
            ·
              refine ⟨34644588951568238231458967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23096392634378825487639311 34644588951568238231458967)
              ·
                refine ⟨51966883427352357347188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34644588951568238231458967 51966883427352357347188451)
                ·
                  refine ⟨77950325141028536020782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51966883427352357347188451 77950325141028536020782677)
                  ·
                    refine ⟨913480372746428156493547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77950325141028536020782677 913480372746428156493547)
                    ·
                      rfl

theorem cell22_2668495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2668495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668495 prefixEnd_2668495 := by exact prefixLift 2668495
  have htrace : WordTrace (prefixWord ++ tailWord_2668495) baseStart_2668495 baseEnd_2668495 := by
    simpa [prefixWord, tailWord_2668495, baseEnd_2668495] using wordTrace_append hprefix tailTrace_2668495
  have hstable : (prefixWord ++ tailWord_2668495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668495).length < 2 ^ (prefixWord ++ tailWord_2668495).sum := by decide
  have hdescent : baseEnd_2668495 < baseStart_2668495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668548 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2668548 : Nat := 118140960795 + 2668548 * 2 ^ 59
def prefixEnd_2668548 : Nat := 4983230072969 + 3 ^ 40 * 2668548 * 2
def baseEnd_2668548 : Nat := 913498515729553684918385

theorem tailTrace_2668548 : CollatzResearch.WordTrace tailWord_2668548 prefixEnd_2668548 913498515729553684918385 := by
  unfold tailWord_2668548
  simp only [CollatzResearch.WordTrace]
  refine ⟨48664970768156911279631149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64886627690875881706174865 48664970768156911279631149)
  ·
    refine ⟨18249364038058841729861681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48664970768156911279631149 18249364038058841729861681)
    ·
      refine ⟨13687023028544131297396261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18249364038058841729861681 13687023028544131297396261)
      ·
        refine ⟨2566316817852024618261799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13687023028544131297396261 2566316817852024618261799)
        ·
          refine ⟨3849475226778036927392699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566316817852024618261799 3849475226778036927392699)
          ·
            refine ⟨5774212840167055391089049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849475226778036927392699 5774212840167055391089049)
            ·
              refine ⟨4330659630125291543316787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774212840167055391089049 4330659630125291543316787)
              ·
                refine ⟨6495989445187937314975181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330659630125291543316787 6495989445187937314975181)
                ·
                  refine ⟨2435996041945476493115693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6495989445187937314975181 2435996041945476493115693)
                  ·
                    refine ⟨913498515729553684918385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435996041945476493115693 913498515729553684918385)
                    ·
                      rfl

theorem cell22_2668548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2668548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668548 prefixEnd_2668548 := by exact prefixLift 2668548
  have htrace : WordTrace (prefixWord ++ tailWord_2668548) baseStart_2668548 baseEnd_2668548 := by
    simpa [prefixWord, tailWord_2668548, baseEnd_2668548] using wordTrace_append hprefix tailTrace_2668548
  have hstable : (prefixWord ++ tailWord_2668548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668548).length < 2 ^ (prefixWord ++ tailWord_2668548).sum := by decide
  have hdescent : baseEnd_2668548 < baseStart_2668548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668604 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_2668604 : Nat := 118140960795 + 2668604 * 2 ^ 59
def prefixEnd_2668604 : Nat := 4983230072969 + 3 ^ 40 * 2668604 * 2
def baseEnd_2668604 : Nat := 913517685673988205518213

theorem tailTrace_2668604 : CollatzResearch.WordTrace tailWord_2668604 prefixEnd_2668604 913517685673988205518213 := by
  unfold tailWord_2668604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665992012055472061650433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64887989349407296082200577 48665992012055472061650433)
  ·
    refine ⟨36499494009041604046237825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48665992012055472061650433 36499494009041604046237825)
    ·
      refine ⟨27374620506781203034678369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36499494009041604046237825 27374620506781203034678369)
      ·
        refine ⟨20530965380085902276008777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27374620506781203034678369 20530965380085902276008777)
        ·
          refine ⟨15398224035064426707006583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20530965380085902276008777 15398224035064426707006583)
          ·
            refine ⟨23097336052596640060509875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15398224035064426707006583 23097336052596640060509875)
            ·
              refine ⟨34646004078894960090764813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23097336052596640060509875 34646004078894960090764813)
              ·
                refine ⟨12992251529585610034036805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34646004078894960090764813 12992251529585610034036805)
                ·
                  refine ⟨2436047161797301881381901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12992251529585610034036805 2436047161797301881381901)
                  ·
                    refine ⟨913517685673988205518213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436047161797301881381901 913517685673988205518213)
                    ·
                      rfl

theorem cell22_2668604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_2668604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668604 prefixEnd_2668604 := by exact prefixLift 2668604
  have htrace : WordTrace (prefixWord ++ tailWord_2668604) baseStart_2668604 baseEnd_2668604 := by
    simpa [prefixWord, tailWord_2668604, baseEnd_2668604] using wordTrace_append hprefix tailTrace_2668604
  have hstable : (prefixWord ++ tailWord_2668604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668604).length < 2 ^ (prefixWord ++ tailWord_2668604).sum := by decide
  have hdescent : baseEnd_2668604 < baseStart_2668604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668617 : List Nat := [1, 2, 1, 1, 2, 2, 6, 7]
def baseStart_2668617 : Nat := 118140960795 + 2668617 * 2 ^ 59
def prefixEnd_2668617 : Nat := 4983230072969 + 3 ^ 40 * 2668617 * 2
def baseEnd_2668617 : Nat := 101502459537740056104797

theorem tailTrace_2668617 : CollatzResearch.WordTrace tailWord_2668617 prefixEnd_2668617 101502459537740056104797 := by
  unfold tailWord_2668617
  simp only [CollatzResearch.WordTrace]
  refine ⟨97332458173063847343524105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64888305448709231562349403 97332458173063847343524105)
  ·
    refine ⟨72999343629797885507643079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97332458173063847343524105 72999343629797885507643079)
    ·
      refine ⟨109499015444696828261464619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72999343629797885507643079 109499015444696828261464619)
      ·
        refine ⟨164248523167045242392196929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109499015444696828261464619 164248523167045242392196929)
        ·
          refine ⟨123186392375283931794147697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164248523167045242392196929 123186392375283931794147697)
          ·
            refine ⟨92389794281462948845610773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123186392375283931794147697 92389794281462948845610773)
            ·
              refine ⟨4330771606943575727138005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92389794281462948845610773 4330771606943575727138005)
              ·
                refine ⟨101502459537740056104797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4330771606943575727138005 101502459537740056104797)
                ·
                  rfl

theorem cell22_2668617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 7].length) (baseStart_2668617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668617 prefixEnd_2668617 := by exact prefixLift 2668617
  have htrace : WordTrace (prefixWord ++ tailWord_2668617) baseStart_2668617 baseEnd_2668617 := by
    simpa [prefixWord, tailWord_2668617, baseEnd_2668617] using wordTrace_append hprefix tailTrace_2668617
  have hstable : (prefixWord ++ tailWord_2668617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668617).length < 2 ^ (prefixWord ++ tailWord_2668617).sum := by decide
  have hdescent : baseEnd_2668617 < baseStart_2668617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668636 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2668636 : Nat := 118140960795 + 2668636 * 2 ^ 59
def prefixEnd_2668636 : Nat := 4983230072969 + 3 ^ 40 * 2668636 * 2
def baseEnd_2668636 : Nat := 913528639927950788718115

theorem tailTrace_2668636 : CollatzResearch.WordTrace tailWord_2668636 prefixEnd_2668636 913528639927950788718115 := by
  unfold tailWord_2668636
  simp only [CollatzResearch.WordTrace]
  refine ⟨48666575579997506794232881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64888767439996675725643841 48666575579997506794232881)
  ·
    refine ⟨36499931684998130095674661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48666575579997506794232881 36499931684998130095674661)
    ·
      refine ⟨6843737190937149392938999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36499931684998130095674661 6843737190937149392938999)
      ·
        refine ⟨10265605786405724089408499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843737190937149392938999 10265605786405724089408499)
        ·
          refine ⟨15398408679608586134112749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265605786405724089408499 15398408679608586134112749)
          ·
            refine ⟨5774403254853219800292281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15398408679608586134112749 5774403254853219800292281)
            ·
              refine ⟨4330802441139914850219211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774403254853219800292281 4330802441139914850219211)
              ·
                refine ⟨6496203661709872275328817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330802441139914850219211 6496203661709872275328817)
                ·
                  refine ⟨4872152746282404206496613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6496203661709872275328817 4872152746282404206496613)
                  ·
                    refine ⟨913528639927950788718115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4872152746282404206496613 913528639927950788718115)
                    ·
                      rfl

theorem cell22_2668636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2668636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668636 prefixEnd_2668636 := by exact prefixLift 2668636
  have htrace : WordTrace (prefixWord ++ tailWord_2668636) baseStart_2668636 baseEnd_2668636 := by
    simpa [prefixWord, tailWord_2668636, baseEnd_2668636] using wordTrace_append hprefix tailTrace_2668636
  have hstable : (prefixWord ++ tailWord_2668636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668636).length < 2 ^ (prefixWord ++ tailWord_2668636).sum := by decide
  have hdescent : baseEnd_2668636 < baseStart_2668636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668679 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 5]
def baseStart_2668679 : Nat := 118140960795 + 2668679 * 2 ^ 59
def prefixEnd_2668679 : Nat := 4983230072969 + 3 ^ 40 * 2668679 * 2
def baseEnd_2668679 : Nat := 304514453235571003297661

theorem tailTrace_2668679 : CollatzResearch.WordTrace tailWord_2668679 prefixEnd_2668679 304514453235571003297661 := by
  unfold tailWord_2668679
  simp only [CollatzResearch.WordTrace]
  refine ⟨97334719498839231932281091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64889812999226154621520727 97334719498839231932281091)
  ·
    refine ⟨146002079248258847898421637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97334719498839231932281091 146002079248258847898421637)
    ·
      refine ⟨27375389859048533980954057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146002079248258847898421637 27375389859048533980954057)
      ·
        refine ⟨20531542394286400485715543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27375389859048533980954057 20531542394286400485715543)
        ·
          refine ⟨30797313591429600728573315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20531542394286400485715543 30797313591429600728573315)
          ·
            refine ⟨46195970387144401092859973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30797313591429600728573315 46195970387144401092859973)
            ·
              refine ⟨8661744447589575204911245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46195970387144401092859973 8661744447589575204911245)
              ·
                refine ⟨3248154167846090701841717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8661744447589575204911245 3248154167846090701841717)
                ·
                  refine ⟨304514453235571003297661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248154167846090701841717 304514453235571003297661)
                  ·
                    rfl

theorem cell22_2668679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 5].length) (baseStart_2668679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668679 prefixEnd_2668679 := by exact prefixLift 2668679
  have htrace : WordTrace (prefixWord ++ tailWord_2668679) baseStart_2668679 baseEnd_2668679 := by
    simpa [prefixWord, tailWord_2668679, baseEnd_2668679] using wordTrace_append hprefix tailTrace_2668679
  have hstable : (prefixWord ++ tailWord_2668679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668679).length < 2 ^ (prefixWord ++ tailWord_2668679).sum := by decide
  have hdescent : baseEnd_2668679 < baseStart_2668679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668775 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 4]
def baseStart_2668775 : Nat := 118140960795 + 2668775 * 2 ^ 59
def prefixEnd_2668775 : Nat := 4983230072969 + 3 ^ 40 * 2668775 * 2
def baseEnd_2668775 : Nat := 304525407489533586497563

theorem tailTrace_2668775 : CollatzResearch.WordTrace tailWord_2668775 prefixEnd_2668775 304525407489533586497563 := by
  unfold tailWord_2668775
  simp only [CollatzResearch.WordTrace]
  refine ⟨97338220906491440327775779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64892147270994293551850519 97338220906491440327775779)
  ·
    refine ⟨146007331359737160491663669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97338220906491440327775779 146007331359737160491663669)
    ·
      refine ⟨13688187314975358796093469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146007331359737160491663669 13688187314975358796093469)
      ·
        refine ⟨5133070243115759548535051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13688187314975358796093469 5133070243115759548535051)
        ·
          refine ⟨7699605364673639322802577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5133070243115759548535051 7699605364673639322802577)
          ·
            refine ⟨5774704023505229492101933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699605364673639322802577 5774704023505229492101933)
            ·
              refine ⟨2165514008814461059538225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5774704023505229492101933 2165514008814461059538225)
              ·
                refine ⟨1624135506610845794653669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165514008814461059538225 1624135506610845794653669)
                ·
                  refine ⟨304525407489533586497563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624135506610845794653669 304525407489533586497563)
                  ·
                    rfl

theorem cell22_2668775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 4].length) (baseStart_2668775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668775 prefixEnd_2668775 := by exact prefixLift 2668775
  have htrace : WordTrace (prefixWord ++ tailWord_2668775) baseStart_2668775 baseEnd_2668775 := by
    simpa [prefixWord, tailWord_2668775, baseEnd_2668775] using wordTrace_append hprefix tailTrace_2668775
  have hstable : (prefixWord ++ tailWord_2668775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668775).length < 2 ^ (prefixWord ++ tailWord_2668775).sum := by decide
  have hdescent : baseEnd_2668775 < baseStart_2668775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668786 : List Nat := [3, 2, 1, 3, 2, 2, 2, 7]
def baseStart_2668786 : Nat := 118140960795 + 2668786 * 2 ^ 59
def prefixEnd_2668786 : Nat := 4983230072969 + 3 ^ 40 * 2668786 * 2
def baseEnd_2668786 : Nat := 101508887554822266385295

theorem tailTrace_2668786 : CollatzResearch.WordTrace tailWord_2668786 prefixEnd_2668786 101508887554822266385295 := by
  unfold tailWord_2668786
  simp only [CollatzResearch.WordTrace]
  refine ⟨24334655527362897301606553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64892414739634392804284141 24334655527362897301606553)
  ·
    refine ⟨18250991645522172976204915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24334655527362897301606553 18250991645522172976204915)
    ·
      refine ⟨27376487468283259464307373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18250991645522172976204915 27376487468283259464307373)
      ·
        refine ⟨10266182800606222299115265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27376487468283259464307373 10266182800606222299115265)
        ·
          refine ⟨7699637100454666724336449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10266182800606222299115265 7699637100454666724336449)
          ·
            refine ⟨5774727825341000043252337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699637100454666724336449 5774727825341000043252337)
            ·
              refine ⟨4331045869005750032439253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774727825341000043252337 4331045869005750032439253)
              ·
                refine ⟨101508887554822266385295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4331045869005750032439253 101508887554822266385295)
                ·
                  rfl

theorem cell22_2668786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_2668786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668786 prefixEnd_2668786 := by exact prefixLift 2668786
  have htrace : WordTrace (prefixWord ++ tailWord_2668786) baseStart_2668786 baseEnd_2668786 := by
    simpa [prefixWord, tailWord_2668786, baseEnd_2668786] using wordTrace_append hprefix tailTrace_2668786
  have hstable : (prefixWord ++ tailWord_2668786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668786).length < 2 ^ (prefixWord ++ tailWord_2668786).sum := by decide
  have hdescent : baseEnd_2668786 < baseStart_2668786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668790 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2668790 : Nat := 118140960795 + 2668790 * 2 ^ 59
def prefixEnd_2668790 : Nat := 4983230072969 + 3 ^ 40 * 2668790 * 2
def baseEnd_2668790 : Nat := 913581357275145720367643

theorem tailTrace_2668790 : CollatzResearch.WordTrace tailWord_2668790 prefixEnd_2668790 913581357275145720367643 := by
  unfold tailWord_2668790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083673000089818618098239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64892512000958065259714549 6083673000089818618098239)
  ·
    refine ⟨9125509500134727927147359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6083673000089818618098239 9125509500134727927147359)
    ·
      refine ⟨13688264250202091890721039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9125509500134727927147359 13688264250202091890721039)
      ·
        refine ⟨20532396375303137836081559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13688264250202091890721039 20532396375303137836081559)
        ·
          refine ⟨30798594562954706754122339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20532396375303137836081559 30798594562954706754122339)
          ·
            refine ⟨46197891844432060131183509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30798594562954706754122339 46197891844432060131183509)
            ·
              refine ⟨2165526180207752818649227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46197891844432060131183509 2165526180207752818649227)
              ·
                refine ⟨3248289270311629227973841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165526180207752818649227 3248289270311629227973841)
                ·
                  refine ⟨2436216952733721920980381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248289270311629227973841 2436216952733721920980381)
                  ·
                    refine ⟨913581357275145720367643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436216952733721920980381 913581357275145720367643)
                    ·
                      rfl

theorem cell22_2668790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2668790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668790 prefixEnd_2668790 := by exact prefixLift 2668790
  have htrace : WordTrace (prefixWord ++ tailWord_2668790) baseStart_2668790 baseEnd_2668790 := by
    simpa [prefixWord, tailWord_2668790, baseEnd_2668790] using wordTrace_append hprefix tailTrace_2668790
  have hstable : (prefixWord ++ tailWord_2668790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668790).length < 2 ^ (prefixWord ++ tailWord_2668790).sum := by decide
  have hdescent : baseEnd_2668790 < baseStart_2668790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668801 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2668801 : Nat := 118140960795 + 2668801 * 2 ^ 59
def prefixEnd_2668801 : Nat := 4983230072969 + 3 ^ 40 * 2668801 * 2
def baseEnd_2668801 : Nat := 913585122799945358342609

theorem tailTrace_2668801 : CollatzResearch.WordTrace tailWord_2668801 prefixEnd_2668801 913585122799945358342609 := by
  unfold tailWord_2668801
  simp only [CollatzResearch.WordTrace]
  refine ⟨97339169204397246768222257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64892779469598164512148171 97339169204397246768222257)
  ·
    refine ⟨73004376903297935076166693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97339169204397246768222257 73004376903297935076166693)
    ·
      refine ⟨13688320669368362826781255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73004376903297935076166693 13688320669368362826781255)
      ·
        refine ⟨20532481004052544240171883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13688320669368362826781255 20532481004052544240171883)
        ·
          refine ⟨30798721506078816360257825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20532481004052544240171883 30798721506078816360257825)
          ·
            refine ⟨23099041129559112270193369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30798721506078816360257825 23099041129559112270193369)
            ·
              refine ⟨17324280847169334202645027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23099041129559112270193369 17324280847169334202645027)
              ·
                refine ⟨25986421270754001303967541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17324280847169334202645027 25986421270754001303967541)
                ·
                  refine ⟨2436226994133187622246957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25986421270754001303967541 2436226994133187622246957)
                  ·
                    refine ⟨913585122799945358342609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436226994133187622246957 913585122799945358342609)
                    ·
                      rfl

theorem cell22_2668801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2668801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668801 prefixEnd_2668801 := by exact prefixLift 2668801
  have htrace : WordTrace (prefixWord ++ tailWord_2668801) baseStart_2668801 baseEnd_2668801 := by
    simpa [prefixWord, tailWord_2668801, baseEnd_2668801] using wordTrace_append hprefix tailTrace_2668801
  have hstable : (prefixWord ++ tailWord_2668801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668801).length < 2 ^ (prefixWord ++ tailWord_2668801).sum := by decide
  have hdescent : baseEnd_2668801 < baseStart_2668801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668831 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 5]
def baseStart_2668831 : Nat := 118140960795 + 2668831 * 2 ^ 59
def prefixEnd_2668831 : Nat := 4983230072969 + 3 ^ 40 * 2668831 * 2
def baseEnd_2668831 : Nat := 304531797471011760030839

theorem tailTrace_2668831 : CollatzResearch.WordTrace tailWord_2668831 prefixEnd_2668831 304531797471011760030839 := by
  unfold tailWord_2668831
  simp only [CollatzResearch.WordTrace]
  refine ⟨97340263394288561891814347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64893508929525707927876231 97340263394288561891814347)
  ·
    refine ⟨146010395091432842837721521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97340263394288561891814347 146010395091432842837721521)
    ·
      refine ⟨109507796318574632128291141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146010395091432842837721521 109507796318574632128291141)
      ·
        refine ⟨20532711809732743524054589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109507796318574632128291141 20532711809732743524054589)
        ·
          refine ⟨7699766928649778821520471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20532711809732743524054589 7699766928649778821520471)
          ·
            refine ⟨11549650392974668232280707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7699766928649778821520471 11549650392974668232280707)
            ·
              refine ⟨17324475589462002348421061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11549650392974668232280707 17324475589462002348421061)
              ·
                refine ⟨3248339173024125440328949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17324475589462002348421061 3248339173024125440328949)
                ·
                  refine ⟨304531797471011760030839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248339173024125440328949 304531797471011760030839)
                  ·
                    rfl

theorem cell22_2668831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 5].length) (baseStart_2668831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2668831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2668831 prefixEnd_2668831 := by exact prefixLift 2668831
  have htrace : WordTrace (prefixWord ++ tailWord_2668831) baseStart_2668831 baseEnd_2668831 := by
    simpa [prefixWord, tailWord_2668831, baseEnd_2668831] using wordTrace_append hprefix tailTrace_2668831
  have hstable : (prefixWord ++ tailWord_2668831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668831).length < 2 ^ (prefixWord ++ tailWord_2668831).sum := by decide
  have hdescent : baseEnd_2668831 < baseStart_2668831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669013 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2669013 : Nat := 118140960795 + 2669013 * 2 ^ 59
def prefixEnd_2669013 : Nat := 4983230072969 + 3 ^ 40 * 2669013 * 2
def baseEnd_2669013 : Nat := 913657694732447472041959

theorem tailTrace_2669013 : CollatzResearch.WordTrace tailWord_2669013 prefixEnd_2669013 913657694732447472041959 := by
  unfold tailWord_2669013
  simp only [CollatzResearch.WordTrace]
  refine ⟨97346901479629206974939693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64897934319752804649959795 97346901479629206974939693)
  ·
    refine ⟨36505088054860952615602385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97346901479629206974939693 36505088054860952615602385)
    ·
      refine ⟨27378816041145714461701789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36505088054860952615602385 27378816041145714461701789)
      ·
        refine ⟨10267056015429642923138171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27378816041145714461701789 10267056015429642923138171)
        ·
          refine ⟨15400584023144464384707257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10267056015429642923138171 15400584023144464384707257)
          ·
            refine ⟨11550438017358348288530443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15400584023144464384707257 11550438017358348288530443)
            ·
              refine ⟨17325657026037522432795665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11550438017358348288530443 17325657026037522432795665)
              ·
                refine ⟨12994242769528141824596749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17325657026037522432795665 12994242769528141824596749)
                ·
                  refine ⟨4872841038573053184223781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12994242769528141824596749 4872841038573053184223781)
                  ·
                    refine ⟨913657694732447472041959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4872841038573053184223781 913657694732447472041959)
                    ·
                      rfl

theorem cell22_2669013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2669013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669013 prefixEnd_2669013 := by exact prefixLift 2669013
  have htrace : WordTrace (prefixWord ++ tailWord_2669013) baseStart_2669013 baseEnd_2669013 := by
    simpa [prefixWord, tailWord_2669013, baseEnd_2669013] using wordTrace_append hprefix tailTrace_2669013
  have hstable : (prefixWord ++ tailWord_2669013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669013).length < 2 ^ (prefixWord ++ tailWord_2669013).sum := by decide
  have hdescent : baseEnd_2669013 < baseStart_2669013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669043 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 4, 3]
def baseStart_2669043 : Nat := 118140960795 + 2669043 * 2 ^ 59
def prefixEnd_2669043 : Nat := 4983230072969 + 3 ^ 40 * 2669043 * 2
def baseEnd_2669043 : Nat := 913667964345537393791867

theorem tailTrace_2669043 : CollatzResearch.WordTrace tailWord_2669043 prefixEnd_2669043 913667964345537393791867 := by
  unfold tailWord_2669043
  simp only [CollatzResearch.WordTrace]
  refine ⟨97347995669520522098531783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64898663779680348065687855 97347995669520522098531783)
  ·
    refine ⟨146021993504280783147797675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97347995669520522098531783 146021993504280783147797675)
    ·
      refine ⟨219032990256421174721696513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146021993504280783147797675 219032990256421174721696513)
      ·
        refine ⟨164274742692315881041272385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219032990256421174721696513 164274742692315881041272385)
        ·
          refine ⟨123206057019236910780954289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164274742692315881041272385 123206057019236910780954289)
          ·
            refine ⟨92404542764427683085715717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123206057019236910780954289 92404542764427683085715717)
            ·
              refine ⟨17325851768330190578571697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92404542764427683085715717 17325851768330190578571697)
              ·
                refine ⟨12994388826247642933928773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17325851768330190578571697 12994388826247642933928773)
                ·
                  refine ⟨2436447904921433050111645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12994388826247642933928773 2436447904921433050111645)
                  ·
                    refine ⟨913667964345537393791867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436447904921433050111645 913667964345537393791867)
                    ·
                      rfl

theorem cell22_2669043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3].length) (baseStart_2669043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669043 prefixEnd_2669043 := by exact prefixLift 2669043
  have htrace : WordTrace (prefixWord ++ tailWord_2669043) baseStart_2669043 baseEnd_2669043 := by
    simpa [prefixWord, tailWord_2669043, baseEnd_2669043] using wordTrace_append hprefix tailTrace_2669043
  have hstable : (prefixWord ++ tailWord_2669043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669043).length < 2 ^ (prefixWord ++ tailWord_2669043).sum := by decide
  have hdescent : baseEnd_2669043 < baseStart_2669043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669071 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2669071 : Nat := 118140960795 + 2669071 * 2 ^ 59
def prefixEnd_2669071 : Nat := 4983230072969 + 3 ^ 40 * 2669071 * 2
def baseEnd_2669071 : Nat := 913677549317754654091781

theorem tailTrace_2669071 : CollatzResearch.WordTrace tailWord_2669071 prefixEnd_2669071 913677549317754654091781 := by
  unfold tailWord_2669071
  simp only [CollatzResearch.WordTrace]
  refine ⟨97349016913419082880551067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64899344608946055253700711 97349016913419082880551067)
  ·
    refine ⟨146023525370128624320826601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97349016913419082880551067 146023525370128624320826601)
    ·
      refine ⟨109517644027596468240619951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146023525370128624320826601 109517644027596468240619951)
      ·
        refine ⟨164276466041394702360929927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109517644027596468240619951 164276466041394702360929927)
        ·
          refine ⟨246414699062092053541394891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164276466041394702360929927 246414699062092053541394891)
          ·
            refine ⟨369622048593138080312092337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246414699062092053541394891 369622048593138080312092337)
            ·
              refine ⟨277216536444853560234069253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369622048593138080312092337 277216536444853560234069253)
              ·
                refine ⟨51978100583410042543887985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277216536444853560234069253 51978100583410042543887985)
                ·
                  refine ⟨38983575437557531907915989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51978100583410042543887985 38983575437557531907915989)
                  ·
                    refine ⟨913677549317754654091781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38983575437557531907915989 913677549317754654091781)
                    ·
                      rfl

theorem cell22_2669071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2669071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669071 prefixEnd_2669071 := by exact prefixLift 2669071
  have htrace : WordTrace (prefixWord ++ tailWord_2669071) baseStart_2669071 baseEnd_2669071 := by
    simpa [prefixWord, tailWord_2669071, baseEnd_2669071] using wordTrace_append hprefix tailTrace_2669071
  have hstable : (prefixWord ++ tailWord_2669071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669071).length < 2 ^ (prefixWord ++ tailWord_2669071).sum := by decide
  have hdescent : baseEnd_2669071 < baseStart_2669071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669077 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2669077 : Nat := 118140960795 + 2669077 * 2 ^ 59
def prefixEnd_2669077 : Nat := 4983230072969 + 3 ^ 40 * 2669077 * 2
def baseEnd_2669077 : Nat := 913679603240372638441763

theorem tailTrace_2669077 : CollatzResearch.WordTrace tailWord_2669077 prefixEnd_2669077 913679603240372638441763 := by
  unfold tailWord_2669077
  simp only [CollatzResearch.WordTrace]
  refine ⟨97349235751397345905269485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64899490500931563936846323 97349235751397345905269485)
  ·
    refine ⟨36505963406774004714476057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97349235751397345905269485 36505963406774004714476057)
    ·
      refine ⟨27379472555080503535857043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36505963406774004714476057 27379472555080503535857043)
      ·
        refine ⟨41069208832620755303785565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27379472555080503535857043 41069208832620755303785565)
        ·
          refine ⟨15400953312232783238919587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41069208832620755303785565 15400953312232783238919587)
          ·
            refine ⟨23101429968349174858379381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15400953312232783238919587 23101429968349174858379381)
            ·
              refine ⟨2165759059532735142973067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23101429968349174858379381 2165759059532735142973067)
              ·
                refine ⟨3248638589299102714459601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165759059532735142973067 3248638589299102714459601)
                ·
                  refine ⟨2436478941974327035844701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248638589299102714459601 2436478941974327035844701)
                  ·
                    refine ⟨913679603240372638441763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436478941974327035844701 913679603240372638441763)
                    ·
                      rfl

theorem cell22_2669077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2669077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669077 prefixEnd_2669077 := by exact prefixLift 2669077
  have htrace : WordTrace (prefixWord ++ tailWord_2669077) baseStart_2669077 baseEnd_2669077 := by
    simpa [prefixWord, tailWord_2669077, baseEnd_2669077] using wordTrace_append hprefix tailTrace_2669077
  have hstable : (prefixWord ++ tailWord_2669077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669077).length < 2 ^ (prefixWord ++ tailWord_2669077).sum := by decide
  have hdescent : baseEnd_2669077 < baseStart_2669077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669124 : List Nat := [2, 3, 5, 1, 1, 1, 2, 7]
def baseStart_2669124 : Nat := 118140960795 + 2669124 * 2 ^ 59
def prefixEnd_2669124 : Nat := 4983230072969 + 3 ^ 40 * 2669124 * 2
def baseEnd_2669124 : Nat := 101521743588986686946291

theorem tailTrace_2669124 : CollatzResearch.WordTrace tailWord_2669124 prefixEnd_2669124 101521743588986686946291 := by
  unfold tailWord_2669124
  simp only [CollatzResearch.WordTrace]
  refine ⟨48675474991113536466115213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64900633321484715288153617 48675474991113536466115213)
  ·
    refine ⟨18253303121667576174793205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48675474991113536466115213 18253303121667576174793205)
    ·
      refine ⟨1711247167656335266386863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18253303121667576174793205 1711247167656335266386863)
      ·
        refine ⟨2566870751484502899580295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711247167656335266386863 2566870751484502899580295)
        ·
          refine ⟨3850306127226754349370443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566870751484502899580295 3850306127226754349370443)
          ·
            refine ⟨5775459190840131524055665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850306127226754349370443 5775459190840131524055665)
            ·
              refine ⟨4331594393130098643041749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5775459190840131524055665 4331594393130098643041749)
              ·
                refine ⟨101521743588986686946291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4331594393130098643041749 101521743588986686946291)
                ·
                  rfl

theorem cell22_2669124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_2669124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669124 prefixEnd_2669124 := by exact prefixLift 2669124
  have htrace : WordTrace (prefixWord ++ tailWord_2669124) baseStart_2669124 baseEnd_2669124 := by
    simpa [prefixWord, tailWord_2669124, baseEnd_2669124] using wordTrace_append hprefix tailTrace_2669124
  have hstable : (prefixWord ++ tailWord_2669124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669124).length < 2 ^ (prefixWord ++ tailWord_2669124).sum := by decide
  have hdescent : baseEnd_2669124 < baseStart_2669124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669135 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 5]
def baseStart_2669135 : Nat := 118140960795 + 2669135 * 2 ^ 59
def prefixEnd_2669135 : Nat := 4983230072969 + 3 ^ 40 * 2669135 * 2
def baseEnd_2669135 : Nat := 304566485941893273497195

theorem tailTrace_2669135 : CollatzResearch.WordTrace tailWord_2669135 prefixEnd_2669135 304566485941893273497195 := by
  unfold tailWord_2669135
  simp only [CollatzResearch.WordTrace]
  refine ⟨97351351185187221810880859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64900900790124814540587239 97351351185187221810880859)
  ·
    refine ⟨146027026777780832716321289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97351351185187221810880859 146027026777780832716321289)
    ·
      refine ⟨109520270083335624537240967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146027026777780832716321289 109520270083335624537240967)
      ·
        refine ⟨164280405125003436805861451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109520270083335624537240967 164280405125003436805861451)
        ·
          refine ⟨246420607687505155208792177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164280405125003436805861451 246420607687505155208792177)
          ·
            refine ⟨184815455765628866406594133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246420607687505155208792177 184815455765628866406594133)
            ·
              refine ⟨2165806122253463278202275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 184815455765628866406594133 2165806122253463278202275)
              ·
                refine ⟨3248709183380194917303413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165806122253463278202275 3248709183380194917303413)
                ·
                  refine ⟨304566485941893273497195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248709183380194917303413 304566485941893273497195)
                  ·
                    rfl

theorem cell22_2669135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 5].length) (baseStart_2669135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669135 prefixEnd_2669135 := by exact prefixLift 2669135
  have htrace : WordTrace (prefixWord ++ tailWord_2669135) baseStart_2669135 baseEnd_2669135 := by
    simpa [prefixWord, tailWord_2669135, baseEnd_2669135] using wordTrace_append hprefix tailTrace_2669135
  have hstable : (prefixWord ++ tailWord_2669135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669135).length < 2 ^ (prefixWord ++ tailWord_2669135).sum := by decide
  have hdescent : baseEnd_2669135 < baseStart_2669135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669173 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2669173 : Nat := 118140960795 + 2669173 * 2 ^ 59
def prefixEnd_2669173 : Nat := 4983230072969 + 3 ^ 40 * 2669173 * 2
def baseEnd_2669173 : Nat := 913712466002260388041469

theorem tailTrace_2669173 : CollatzResearch.WordTrace tailWord_2669173 prefixEnd_2669173 913712466002260388041469 := by
  unfold tailWord_2669173
  simp only [CollatzResearch.WordTrace]
  refine ⟨97352737159049554300764173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64901824772699702867176115 97352737159049554300764173)
  ·
    refine ⟨36507276434643582862786565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97352737159049554300764173 36507276434643582862786565)
    ·
      refine ⟨6845114331495671786772481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36507276434643582862786565 6845114331495671786772481)
      ·
        refine ⟨5133835748621753840079361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6845114331495671786772481 5133835748621753840079361)
        ·
          refine ⟨3850376811466315380059521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5133835748621753840079361 3850376811466315380059521)
          ·
            refine ⟨2887782608599736535044641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3850376811466315380059521 2887782608599736535044641)
            ·
              refine ⟨2165836956449802401283481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887782608599736535044641 2165836956449802401283481)
              ·
                refine ⟨1624377717337351800962611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165836956449802401283481 1624377717337351800962611)
                ·
                  refine ⟨2436566576006027701443917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624377717337351800962611 2436566576006027701443917)
                  ·
                    refine ⟨913712466002260388041469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436566576006027701443917 913712466002260388041469)
                    ·
                      rfl

theorem cell22_2669173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2669173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669173 prefixEnd_2669173 := by exact prefixLift 2669173
  have htrace : WordTrace (prefixWord ++ tailWord_2669173) baseStart_2669173 baseEnd_2669173 := by
    simpa [prefixWord, tailWord_2669173, baseEnd_2669173] using wordTrace_append hprefix tailTrace_2669173
  have hstable : (prefixWord ++ tailWord_2669173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669173).length < 2 ^ (prefixWord ++ tailWord_2669173).sum := by decide
  have hdescent : baseEnd_2669173 < baseStart_2669173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669193 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_2669193 : Nat := 118140960795 + 2669193 * 2 ^ 59
def prefixEnd_2669193 : Nat := 4983230072969 + 3 ^ 40 * 2669193 * 2
def baseEnd_2669193 : Nat := 913719312410987002541407

theorem tailTrace_2669193 : CollatzResearch.WordTrace tailWord_2669193 prefixEnd_2669193 913719312410987002541407 := by
  unfold tailWord_2669193
  simp only [CollatzResearch.WordTrace]
  refine ⟨97353466618977097716492233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64902311079318065144328155 97353466618977097716492233)
  ·
    refine ⟨73015099964232823287369175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97353466618977097716492233 73015099964232823287369175)
    ·
      refine ⟨109522649946349234931053763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73015099964232823287369175 109522649946349234931053763)
      ·
        refine ⟨164283974919523852396580645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109522649946349234931053763 164283974919523852396580645)
        ·
          refine ⟨30803245297410722324358871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164283974919523852396580645 30803245297410722324358871)
          ·
            refine ⟨46204867946116083486538307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30803245297410722324358871 46204867946116083486538307)
            ·
              refine ⟨69307301919174125229807461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46204867946116083486538307 69307301919174125229807461)
              ·
                refine ⟨12995119109845148480588899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69307301919174125229807461 12995119109845148480588899)
                ·
                  refine ⟨19492678664767722720883349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12995119109845148480588899 19492678664767722720883349)
                  ·
                    refine ⟨913719312410987002541407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19492678664767722720883349 913719312410987002541407)
                    ·
                      rfl

theorem cell22_2669193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_2669193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669193 prefixEnd_2669193 := by exact prefixLift 2669193
  have htrace : WordTrace (prefixWord ++ tailWord_2669193) baseStart_2669193 baseEnd_2669193 := by
    simpa [prefixWord, tailWord_2669193, baseEnd_2669193] using wordTrace_append hprefix tailTrace_2669193
  have hstable : (prefixWord ++ tailWord_2669193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669193).length < 2 ^ (prefixWord ++ tailWord_2669193).sum := by decide
  have hdescent : baseEnd_2669193 < baseStart_2669193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669214 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2669214 : Nat := 118140960795 + 2669214 * 2 ^ 59
def prefixEnd_2669214 : Nat := 4983230072969 + 3 ^ 40 * 2669214 * 2
def baseEnd_2669214 : Nat := 304575500380049982588781

theorem tailTrace_2669214 : CollatzResearch.WordTrace tailWord_2669214 prefixEnd_2669214 304575500380049982588781 := by
  unfold tailWord_2669214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169279068987627287875837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64902821701267345535337797 12169279068987627287875837)
  ·
    refine ⟨4563479650870360232953439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12169279068987627287875837 4563479650870360232953439)
    ·
      refine ⟨6845219476305540349430159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563479650870360232953439 6845219476305540349430159)
      ·
        refine ⟨10267829214458310524145239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6845219476305540349430159 10267829214458310524145239)
        ·
          refine ⟨15401743821687465786217859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10267829214458310524145239 15401743821687465786217859)
          ·
            refine ⟨23102615732531198679326789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15401743821687465786217859 23102615732531198679326789)
            ·
              refine ⟨4331740449849599752373773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23102615732531198679326789 4331740449849599752373773)
              ·
                refine ⟨1624402668693599907140165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4331740449849599752373773 1624402668693599907140165)
                ·
                  refine ⟨304575500380049982588781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624402668693599907140165 304575500380049982588781)
                  ·
                    rfl

theorem cell22_2669214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2669214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669214 prefixEnd_2669214 := by exact prefixLift 2669214
  have htrace : WordTrace (prefixWord ++ tailWord_2669214) baseStart_2669214 baseEnd_2669214 := by
    simpa [prefixWord, tailWord_2669214, baseEnd_2669214] using wordTrace_append hprefix tailTrace_2669214
  have hstable : (prefixWord ++ tailWord_2669214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669214).length < 2 ^ (prefixWord ++ tailWord_2669214).sum := by decide
  have hdescent : baseEnd_2669214 < baseStart_2669214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669216 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_2669216 : Nat := 118140960795 + 2669216 * 2 ^ 59
def prefixEnd_2669216 : Nat := 4983230072969 + 3 ^ 40 * 2669216 * 2
def baseEnd_2669216 : Nat := 913727185781022609216337

theorem tailTrace_2669216 : CollatzResearch.WordTrace tailWord_2669216 prefixEnd_2669216 913727185781022609216337 := by
  unfold tailWord_2669216
  simp only [CollatzResearch.WordTrace]
  refine ⟨48677152748946886322289751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64902870331929181763053001 48677152748946886322289751)
  ·
    refine ⟨73015729123420329483434627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48677152748946886322289751 73015729123420329483434627)
    ·
      refine ⟨109523593685130494225151941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73015729123420329483434627 109523593685130494225151941)
      ·
        refine ⟨20535673815961967667215989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109523593685130494225151941 20535673815961967667215989)
        ·
          refine ⟨1925219420246434468801499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20535673815961967667215989 1925219420246434468801499)
          ·
            refine ⟨2887829130369651703202249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925219420246434468801499 2887829130369651703202249)
            ·
              refine ⟨2165871847777238777401687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887829130369651703202249 2165871847777238777401687)
              ·
                refine ⟨3248807771665858166102531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165871847777238777401687 3248807771665858166102531)
                ·
                  refine ⟨4873211657498787249153797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248807771665858166102531 4873211657498787249153797)
                  ·
                    refine ⟨913727185781022609216337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4873211657498787249153797 913727185781022609216337)
                    ·
                      rfl

theorem cell22_2669216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_2669216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669216 prefixEnd_2669216 := by exact prefixLift 2669216
  have htrace : WordTrace (prefixWord ++ tailWord_2669216) baseStart_2669216 baseEnd_2669216 := by
    simpa [prefixWord, tailWord_2669216, baseEnd_2669216] using wordTrace_append hprefix tailTrace_2669216
  have hstable : (prefixWord ++ tailWord_2669216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669216).length < 2 ^ (prefixWord ++ tailWord_2669216).sum := by decide
  have hdescent : baseEnd_2669216 < baseStart_2669216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669229 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2669229 : Nat := 118140960795 + 2669229 * 2 ^ 59
def prefixEnd_2669229 : Nat := 4983230072969 + 3 ^ 40 * 2669229 * 2
def baseEnd_2669229 : Nat := 913731635946694908641297

theorem tailTrace_2669229 : CollatzResearch.WordTrace tailWord_2669229 prefixEnd_2669229 913731635946694908641297 := by
  unfold tailWord_2669229
  simp only [CollatzResearch.WordTrace]
  refine ⟨97354779646846675864802741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64903186431231117243201827 97354779646846675864802741)
  ·
    refine ⟨9127010591891875862325257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97354779646846675864802741 9127010591891875862325257)
    ·
      refine ⟨6845257943918906896743943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9127010591891875862325257 6845257943918906896743943)
      ·
        refine ⟨10267886915878360345115915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6845257943918906896743943 10267886915878360345115915)
        ·
          refine ⟨15401830373817540517673873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10267886915878360345115915 15401830373817540517673873)
          ·
            refine ⟨11551372780363155388255405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15401830373817540517673873 11551372780363155388255405)
            ·
              refine ⟨4331764792636183270595777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11551372780363155388255405 4331764792636183270595777)
              ·
                refine ⟨3248823594477137452946833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4331764792636183270595777 3248823594477137452946833)
                ·
                  refine ⟨2436617695857853089710125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248823594477137452946833 2436617695857853089710125)
                  ·
                    refine ⟨913731635946694908641297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436617695857853089710125 913731635946694908641297)
                    ·
                      rfl

theorem cell22_2669229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2669229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669229 prefixEnd_2669229 := by exact prefixLift 2669229
  have htrace : WordTrace (prefixWord ++ tailWord_2669229) baseStart_2669229 baseEnd_2669229 := by
    simpa [prefixWord, tailWord_2669229, baseEnd_2669229] using wordTrace_append hprefix tailTrace_2669229
  have hstable : (prefixWord ++ tailWord_2669229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669229).length < 2 ^ (prefixWord ++ tailWord_2669229).sum := by decide
  have hdescent : baseEnd_2669229 < baseStart_2669229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669253 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 11]
def baseStart_2669253 : Nat := 118140960795 + 2669253 * 2 ^ 59
def prefixEnd_2669253 : Nat := 4983230072969 + 3 ^ 40 * 2669253 * 2
def baseEnd_2669253 : Nat := 304579950545722282013741

theorem tailTrace_2669253 : CollatzResearch.WordTrace tailWord_2669253 prefixEnd_2669253 304579950545722282013741 := by
  unfold tailWord_2669253
  simp only [CollatzResearch.WordTrace]
  refine ⟨97355654998759727963676413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64903769999173151975784275 97355654998759727963676413)
  ·
    refine ⟨36508370624534897986378655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97355654998759727963676413 36508370624534897986378655)
    ·
      refine ⟨54762555936802346979567983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36508370624534897986378655 54762555936802346979567983)
      ·
        refine ⟨82143833905203520469351975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54762555936802346979567983 82143833905203520469351975)
        ·
          refine ⟨123215750857805280704027963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82143833905203520469351975 123215750857805280704027963)
          ·
            refine ⟨184823626286707921056041945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123215750857805280704027963 184823626286707921056041945)
            ·
              refine ⟨138617719715030940792031459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184823626286707921056041945 138617719715030940792031459)
              ·
                refine ⟨207926579572546411188047189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138617719715030940792031459 207926579572546411188047189)
                ·
                  refine ⟨304579950545722282013741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 207926579572546411188047189 304579950545722282013741)
                  ·
                    rfl

theorem cell22_2669253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_2669253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669253 prefixEnd_2669253 := by exact prefixLift 2669253
  have htrace : WordTrace (prefixWord ++ tailWord_2669253) baseStart_2669253 baseEnd_2669253 := by
    simpa [prefixWord, tailWord_2669253, baseEnd_2669253] using wordTrace_append hprefix tailTrace_2669253
  have hstable : (prefixWord ++ tailWord_2669253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669253).length < 2 ^ (prefixWord ++ tailWord_2669253).sum := by decide
  have hdescent : baseEnd_2669253 < baseStart_2669253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669512 : List Nat := [2, 1, 3, 1, 5, 10]
def baseStart_2669512 : Nat := 118140960795 + 2669512 * 2 ^ 59
def prefixEnd_2669512 : Nat := 4983230072969 + 3 ^ 40 * 2669512 * 2
def baseEnd_2669512 : Nat := 11281833489261438318709

theorem tailTrace_2669512 : CollatzResearch.WordTrace tailWord_2669512 prefixEnd_2669512 11281833489261438318709 := by
  unfold tailWord_2669512
  simp only [CollatzResearch.WordTrace]
  refine ⟨48682550752410707598677395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64910067669880943464903193 48682550752410707598677395)
  ·
    refine ⟨73023826128616061398016093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48682550752410707598677395 73023826128616061398016093)
    ·
      refine ⟨27383934798231023024256035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73023826128616061398016093 27383934798231023024256035)
      ·
        refine ⟨41075902197346534536384053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27383934798231023024256035 41075902197346534536384053)
        ·
          refine ⟨3850865831001237612786005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41075902197346534536384053 3850865831001237612786005)
          ·
            refine ⟨11281833489261438318709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3850865831001237612786005 11281833489261438318709)
            ·
              rfl

theorem cell22_2669512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 10].length) (baseStart_2669512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669512 prefixEnd_2669512 := by exact prefixLift 2669512
  have htrace : WordTrace (prefixWord ++ tailWord_2669512) baseStart_2669512 baseEnd_2669512 := by
    simpa [prefixWord, tailWord_2669512, baseEnd_2669512] using wordTrace_append hprefix tailTrace_2669512
  have hstable : (prefixWord ++ tailWord_2669512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669512).length < 2 ^ (prefixWord ++ tailWord_2669512).sum := by decide
  have hdescent : baseEnd_2669512 < baseStart_2669512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669516 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_2669516 : Nat := 118140960795 + 2669516 * 2 ^ 59
def prefixEnd_2669516 : Nat := 4983230072969 + 3 ^ 40 * 2669516 * 2
def baseEnd_2669516 : Nat := 913829881911921826715417

theorem tailTrace_2669516 : CollatzResearch.WordTrace tailWord_2669516 prefixEnd_2669516 913829881911921826715417 := by
  unfold tailWord_2669516
  simp only [CollatzResearch.WordTrace]
  refine ⟨48682623698403461940250201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64910164931204615920333601 48682623698403461940250201)
  ·
    refine ⟨36511967773802596455187651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48682623698403461940250201 36511967773802596455187651)
    ·
      refine ⟨54767951660703894682781477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36511967773802596455187651 54767951660703894682781477)
      ·
        refine ⟨10268990936381980253021527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54767951660703894682781477 10268990936381980253021527)
        ·
          refine ⟨15403486404572970379532291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10268990936381980253021527 15403486404572970379532291)
          ·
            refine ⟨23105229606859455569298437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15403486404572970379532291 23105229606859455569298437)
            ·
              refine ⟨4332230551286147919243457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23105229606859455569298437 4332230551286147919243457)
              ·
                refine ⟨3249172913464610939432593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4332230551286147919243457 3249172913464610939432593)
                ·
                  refine ⟨2436879685098458204574445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249172913464610939432593 2436879685098458204574445)
                  ·
                    refine ⟨913829881911921826715417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436879685098458204574445 913829881911921826715417)
                    ·
                      rfl

theorem cell22_2669516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_2669516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669516 prefixEnd_2669516 := by exact prefixLift 2669516
  have htrace : WordTrace (prefixWord ++ tailWord_2669516) baseStart_2669516 baseEnd_2669516 := by
    simpa [prefixWord, tailWord_2669516, baseEnd_2669516] using wordTrace_append hprefix tailTrace_2669516
  have hstable : (prefixWord ++ tailWord_2669516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669516).length < 2 ^ (prefixWord ++ tailWord_2669516).sum := by decide
  have hdescent : baseEnd_2669516 < baseStart_2669516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669518 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_2669518 : Nat := 118140960795 + 2669518 * 2 ^ 59
def prefixEnd_2669518 : Nat := 4983230072969 + 3 ^ 40 * 2669518 * 2
def baseEnd_2669518 : Nat := 304610188850931496055137

theorem tailTrace_2669518 : CollatzResearch.WordTrace tailWord_2669518 prefixEnd_2669518 304610188850931496055137 := by
  unfold tailWord_2669518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12170665042849959777759151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64910213561866452148048805 12170665042849959777759151)
  ·
    refine ⟨18255997564274939666638727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12170665042849959777759151 18255997564274939666638727)
    ·
      refine ⟨27383996346412409499958091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18255997564274939666638727 27383996346412409499958091)
      ·
        refine ⟨41075994519618614249937137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27383996346412409499958091 41075994519618614249937137)
        ·
          refine ⟨30806995889713960687452853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41075994519618614249937137 30806995889713960687452853)
          ·
            refine ⟨2888155864660683814448705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30806995889713960687452853 2888155864660683814448705)
            ·
              refine ⟨2166116898495512860836529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888155864660683814448705 2166116898495512860836529)
              ·
                refine ⟨1624587673871634645627397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166116898495512860836529 1624587673871634645627397)
                ·
                  refine ⟨304610188850931496055137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624587673871634645627397 304610188850931496055137)
                  ·
                    rfl

theorem cell22_2669518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_2669518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669518 prefixEnd_2669518 := by exact prefixLift 2669518
  have htrace : WordTrace (prefixWord ++ tailWord_2669518) baseStart_2669518 baseEnd_2669518 := by
    simpa [prefixWord, tailWord_2669518, baseEnd_2669518] using wordTrace_append hprefix tailTrace_2669518
  have hstable : (prefixWord ++ tailWord_2669518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669518).length < 2 ^ (prefixWord ++ tailWord_2669518).sum := by decide
  have hdescent : baseEnd_2669518 < baseStart_2669518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669529 : List Nat := [1, 2, 1, 2, 5, 3, 1, 7]
def baseStart_2669529 : Nat := 118140960795 + 2669529 * 2 ^ 59
def prefixEnd_2669529 : Nat := 4983230072969 + 3 ^ 40 * 2669529 * 2
def baseEnd_2669529 : Nat := 101537148008621569571153

theorem tailTrace_2669529 : CollatzResearch.WordTrace tailWord_2669529 prefixEnd_2669529 101537148008621569571153 := by
  unfold tailWord_2669529
  simp only [CollatzResearch.WordTrace]
  refine ⟨97365721545759827100723641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64910481030506551400482427 97365721545759827100723641)
  ·
    refine ⟨73024291159319870325542731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97365721545759827100723641 73024291159319870325542731)
    ·
      refine ⟨109536436738979805488314097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73024291159319870325542731 109536436738979805488314097)
      ·
        refine ⟨82152327554234854116235573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109536436738979805488314097 82152327554234854116235573)
        ·
          refine ⟨7701780708209517573397085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82152327554234854116235573 7701780708209517573397085)
          ·
            refine ⟨2888167765578569090023907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7701780708209517573397085 2888167765578569090023907)
            ·
              refine ⟨4332251648367853635035861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888167765578569090023907 4332251648367853635035861)
              ·
                refine ⟨101537148008621569571153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4332251648367853635035861 101537148008621569571153)
                ·
                  rfl

theorem cell22_2669529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 7].length) (baseStart_2669529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669529 prefixEnd_2669529 := by exact prefixLift 2669529
  have htrace : WordTrace (prefixWord ++ tailWord_2669529) baseStart_2669529 baseEnd_2669529 := by
    simpa [prefixWord, tailWord_2669529, baseEnd_2669529] using wordTrace_append hprefix tailTrace_2669529
  have hstable : (prefixWord ++ tailWord_2669529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669529).length < 2 ^ (prefixWord ++ tailWord_2669529).sum := by decide
  have hdescent : baseEnd_2669529 < baseStart_2669529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669544 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_2669544 : Nat := 118140960795 + 2669544 * 2 ^ 59
def prefixEnd_2669544 : Nat := 4983230072969 + 3 ^ 40 * 2669544 * 2
def baseEnd_2669544 : Nat := 913839466884139087015331

theorem tailTrace_2669544 : CollatzResearch.WordTrace tailWord_2669544 prefixEnd_2669544 913839466884139087015331 := by
  unfold tailWord_2669544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48683134320352742331259843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64910845760470323108346457 48683134320352742331259843)
  ·
    refine ⟨73024701480529113496889765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48683134320352742331259843 73024701480529113496889765)
    ·
      refine ⟨13692131527599208780666831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73024701480529113496889765 13692131527599208780666831)
      ·
        refine ⟨20538197291398813171000247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13692131527599208780666831 20538197291398813171000247)
        ·
          refine ⟨30807295937098219756500371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20538197291398813171000247 30807295937098219756500371)
          ·
            refine ⟨46210943905647329634750557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30807295937098219756500371 46210943905647329634750557)
            ·
              refine ⟨17329103964617748613031459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46210943905647329634750557 17329103964617748613031459)
              ·
                refine ⟨25993655946926622919547189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17329103964617748613031459 25993655946926622919547189)
                ·
                  refine ⟨2436905245024370898707549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25993655946926622919547189 2436905245024370898707549)
                  ·
                    refine ⟨913839466884139087015331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436905245024370898707549 913839466884139087015331)
                    ·
                      rfl

theorem cell22_2669544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_2669544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669544 prefixEnd_2669544 := by exact prefixLift 2669544
  have htrace : WordTrace (prefixWord ++ tailWord_2669544) baseStart_2669544 baseEnd_2669544 := by
    simpa [prefixWord, tailWord_2669544, baseEnd_2669544] using wordTrace_append hprefix tailTrace_2669544
  have hstable : (prefixWord ++ tailWord_2669544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669544).length < 2 ^ (prefixWord ++ tailWord_2669544).sum := by decide
  have hdescent : baseEnd_2669544 < baseStart_2669544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669578 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2669578 : Nat := 118140960795 + 2669578 * 2 ^ 59
def prefixEnd_2669578 : Nat := 4983230072969 + 3 ^ 40 * 2669578 * 2
def baseEnd_2669578 : Nat := 913851105778974331665227

theorem tailTrace_2669578 : CollatzResearch.WordTrace tailWord_2669578 prefixEnd_2669578 913851105778974331665227 := by
  unfold tailWord_2669578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24341877180645577117314347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64911672481721538979504925 24341877180645577117314347)
  ·
    refine ⟨36512815770968365675971521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24341877180645577117314347 36512815770968365675971521)
    ·
      refine ⟨27384611828226274256978641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36512815770968365675971521 27384611828226274256978641)
      ·
        refine ⟨20538458871169705692733981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27384611828226274256978641 20538458871169705692733981)
        ·
          refine ⟨7701922076688639634775243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20538458871169705692733981 7701922076688639634775243)
          ·
            refine ⟨11552883115032959452162865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701922076688639634775243 11552883115032959452162865)
            ·
              refine ⟨8664662336274719589122149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11552883115032959452162865 8664662336274719589122149)
              ·
                refine ⟨1624624188051509922960403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8664662336274719589122149 1624624188051509922960403)
                ·
                  refine ⟨2436936282077264884440605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624624188051509922960403 2436936282077264884440605)
                  ·
                    refine ⟨913851105778974331665227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436936282077264884440605 913851105778974331665227)
                    ·
                      rfl

theorem cell22_2669578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2669578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669578 prefixEnd_2669578 := by exact prefixLift 2669578
  have htrace : WordTrace (prefixWord ++ tailWord_2669578) baseStart_2669578 baseEnd_2669578 := by
    simpa [prefixWord, tailWord_2669578, baseEnd_2669578] using wordTrace_append hprefix tailTrace_2669578
  have hstable : (prefixWord ++ tailWord_2669578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669578).length < 2 ^ (prefixWord ++ tailWord_2669578).sum := by decide
  have hdescent : baseEnd_2669578 < baseStart_2669578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669589 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2669589 : Nat := 118140960795 + 2669589 * 2 ^ 59
def prefixEnd_2669589 : Nat := 4983230072969 + 3 ^ 40 * 2669589 * 2
def baseEnd_2669589 : Nat := 913854871303773969640193

theorem tailTrace_2669589 : CollatzResearch.WordTrace tailWord_2669589 prefixEnd_2669589 913854871303773969640193 := by
  unfold tailWord_2669589
  simp only [CollatzResearch.WordTrace]
  refine ⟨97367909925542457347907821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64911939950361638231938547 97367909925542457347907821)
  ·
    refine ⟨36512966222078421505465433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97367909925542457347907821 36512966222078421505465433)
    ·
      refine ⟨27384724666558816129099075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36512966222078421505465433 27384724666558816129099075)
      ·
        refine ⟨41077086999838224193648613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27384724666558816129099075 41077086999838224193648613)
        ·
          refine ⟨7701953812469667036309115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41077086999838224193648613 7701953812469667036309115)
          ·
            refine ⟨11552930718704500554463673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701953812469667036309115 11552930718704500554463673)
            ·
              refine ⟨8664698039028375415847755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11552930718704500554463673 8664698039028375415847755)
              ·
                refine ⟨12997047058542563123771633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8664698039028375415847755 12997047058542563123771633)
                ·
                  refine ⟨9747785293906922342828725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12997047058542563123771633 9747785293906922342828725)
                  ·
                    refine ⟨913854871303773969640193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9747785293906922342828725 913854871303773969640193)
                    ·
                      rfl

theorem cell22_2669589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2669589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669589 prefixEnd_2669589 := by exact prefixLift 2669589
  have htrace : WordTrace (prefixWord ++ tailWord_2669589) baseStart_2669589 baseEnd_2669589 := by
    simpa [prefixWord, tailWord_2669589, baseEnd_2669589] using wordTrace_append hprefix tailTrace_2669589
  have hstable : (prefixWord ++ tailWord_2669589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669589).length < 2 ^ (prefixWord ++ tailWord_2669589).sum := by decide
  have hdescent : baseEnd_2669589 < baseStart_2669589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669820 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_2669820 : Nat := 118140960795 + 2669820 * 2 ^ 59
def prefixEnd_2669820 : Nat := 4983230072969 + 3 ^ 40 * 2669820 * 2
def baseEnd_2669820 : Nat := 913933947324566367114485

theorem tailTrace_2669820 : CollatzResearch.WordTrace tailWord_2669820 prefixEnd_2669820 913933947324566367114485 := by
  unfold tailWord_2669820
  simp only [CollatzResearch.WordTrace]
  refine ⟨48688167593852791899783457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64917556791803722533044609 48688167593852791899783457)
  ·
    refine ⟨36516125695389593924837593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48688167593852791899783457 36516125695389593924837593)
    ·
      refine ⟨27387094271542195443628195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36516125695389593924837593 27387094271542195443628195)
      ·
        refine ⟨41080641407313293165442293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27387094271542195443628195 41080641407313293165442293)
        ·
          refine ⟨3851310131935621234260215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41080641407313293165442293 3851310131935621234260215)
          ·
            refine ⟨5776965197903431851390323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3851310131935621234260215 5776965197903431851390323)
            ·
              refine ⟨8665447796855147777085485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5776965197903431851390323 8665447796855147777085485)
              ·
                refine ⟨3249542923820680416407057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8665447796855147777085485 3249542923820680416407057)
                ·
                  refine ⟨2437157192865510312305293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249542923820680416407057 2437157192865510312305293)
                  ·
                    refine ⟨913933947324566367114485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2437157192865510312305293 913933947324566367114485)
                    ·
                      rfl

theorem cell22_2669820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_2669820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669820 prefixEnd_2669820 := by exact prefixLift 2669820
  have htrace : WordTrace (prefixWord ++ tailWord_2669820) baseStart_2669820 baseEnd_2669820 := by
    simpa [prefixWord, tailWord_2669820, baseEnd_2669820] using wordTrace_append hprefix tailTrace_2669820
  have hstable : (prefixWord ++ tailWord_2669820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669820).length < 2 ^ (prefixWord ++ tailWord_2669820).sum := by decide
  have hdescent : baseEnd_2669820 < baseStart_2669820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669854 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2669854 : Nat := 118140960795 + 2669854 * 2 ^ 59
def prefixEnd_2669854 : Nat := 4983230072969 + 3 ^ 40 * 2669854 * 2
def baseEnd_2669854 : Nat := 913945586219401611764381

theorem tailTrace_2669854 : CollatzResearch.WordTrace tailWord_2669854 prefixEnd_2669854 913945586219401611764381 := by
  unfold tailWord_2669854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172196908697800950788077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64918383513054938404203077 12172196908697800950788077)
  ·
    refine ⟨4564573840761675356545529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12172196908697800950788077 4564573840761675356545529)
    ·
      refine ⟨3423430380571256517409147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4564573840761675356545529 3423430380571256517409147)
      ·
        refine ⟨5135145570856884776113721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3423430380571256517409147 5135145570856884776113721)
        ·
          refine ⟨3851359178142663582085291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5135145570856884776113721 3851359178142663582085291)
          ·
            refine ⟨5777038767213995373127937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3851359178142663582085291 5777038767213995373127937)
            ·
              refine ⟨4332779075410496529845953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777038767213995373127937 4332779075410496529845953)
              ·
                refine ⟨3249584306557872397384465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4332779075410496529845953 3249584306557872397384465)
                ·
                  refine ⟨2437188229918404298038349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249584306557872397384465 2437188229918404298038349)
                  ·
                    refine ⟨913945586219401611764381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2437188229918404298038349 913945586219401611764381)
                    ·
                      rfl

theorem cell22_2669854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2669854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669854 prefixEnd_2669854 := by exact prefixLift 2669854
  have htrace : WordTrace (prefixWord ++ tailWord_2669854) baseStart_2669854 baseEnd_2669854 := by
    simpa [prefixWord, tailWord_2669854, baseEnd_2669854] using wordTrace_append hprefix tailTrace_2669854
  have hstable : (prefixWord ++ tailWord_2669854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669854).length < 2 ^ (prefixWord ++ tailWord_2669854).sum := by decide
  have hdescent : baseEnd_2669854 < baseStart_2669854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669906 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_2669906 : Nat := 118140960795 + 2669906 * 2 ^ 59
def prefixEnd_2669906 : Nat := 4983230072969 + 3 ^ 40 * 2669906 * 2
def baseEnd_2669906 : Nat := 304654462294030269821407

theorem tailTrace_2669906 : CollatzResearch.WordTrace tailWord_2669906 prefixEnd_2669906 304654462294030269821407 := by
  unfold tailWord_2669906
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344867966348505121799393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64919647910262680324798381 24344867966348505121799393)
  ·
    refine ⟨18258650974761378841349545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24344867966348505121799393 18258650974761378841349545)
    ·
      refine ⟨13693988231071034131012159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18258650974761378841349545 13693988231071034131012159)
      ·
        refine ⟨20540982346606551196518239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13693988231071034131012159 20540982346606551196518239)
        ·
          refine ⟨30811473519909826794777359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20540982346606551196518239 30811473519909826794777359)
          ·
            refine ⟨46217210279864740192166039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30811473519909826794777359 46217210279864740192166039)
            ·
              refine ⟨69325815419797110288249059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46217210279864740192166039 69325815419797110288249059)
              ·
                refine ⟨103988723129695665432373589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69325815419797110288249059 103988723129695665432373589)
                ·
                  refine ⟨304654462294030269821407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103988723129695665432373589 304654462294030269821407)
                  ·
                    rfl

theorem cell22_2669906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_2669906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669906 prefixEnd_2669906 := by exact prefixLift 2669906
  have htrace : WordTrace (prefixWord ++ tailWord_2669906) baseStart_2669906 baseEnd_2669906 := by
    simpa [prefixWord, tailWord_2669906, baseEnd_2669906] using wordTrace_append hprefix tailTrace_2669906
  have hstable : (prefixWord ++ tailWord_2669906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669906).length < 2 ^ (prefixWord ++ tailWord_2669906).sum := by decide
  have hdescent : baseEnd_2669906 < baseStart_2669906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669921 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2669921 : Nat := 118140960795 + 2669921 * 2 ^ 59
def prefixEnd_2669921 : Nat := 4983230072969 + 3 ^ 40 * 2669921 * 2
def baseEnd_2669921 : Nat := 913968521688635770339175

theorem tailTrace_2669921 : CollatzResearch.WordTrace tailWord_2669921 prefixEnd_2669921 913968521688635770339175 := by
  unfold tailWord_2669921
  simp only [CollatzResearch.WordTrace]
  refine ⟨97380018960339678048993617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64920012640226452032662411 97380018960339678048993617)
  ·
    refine ⟨73035014220254758536745213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97380018960339678048993617 73035014220254758536745213)
    ·
      refine ⟨27388130332595534451279455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73035014220254758536745213 27388130332595534451279455)
      ·
        refine ⟨41082195498893301676919183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27388130332595534451279455 41082195498893301676919183)
        ·
          refine ⟨61623293248339952515378775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41082195498893301676919183 61623293248339952515378775)
          ·
            refine ⟨92434939872509928773068163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61623293248339952515378775 92434939872509928773068163)
            ·
              refine ⟨138652409808764893159602245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92434939872509928773068163 138652409808764893159602245)
              ·
                refine ⟨25997326839143417467425421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138652409808764893159602245 25997326839143417467425421)
                ·
                  refine ⟨9748997564678781550284533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25997326839143417467425421 9748997564678781550284533)
                  ·
                    refine ⟨913968521688635770339175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9748997564678781550284533 913968521688635770339175)
                    ·
                      rfl

theorem cell22_2669921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2669921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669921 prefixEnd_2669921 := by exact prefixLift 2669921
  have htrace : WordTrace (prefixWord ++ tailWord_2669921) baseStart_2669921 baseEnd_2669921 := by
    simpa [prefixWord, tailWord_2669921, baseEnd_2669921] using wordTrace_append hprefix tailTrace_2669921
  have hstable : (prefixWord ++ tailWord_2669921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669921).length < 2 ^ (prefixWord ++ tailWord_2669921).sum := by decide
  have hdescent : baseEnd_2669921 < baseStart_2669921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669923 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 6]
def baseStart_2669923 : Nat := 118140960795 + 2669923 * 2 ^ 59
def prefixEnd_2669923 : Nat := 4983230072969 + 3 ^ 40 * 2669923 * 2
def baseEnd_2669923 : Nat := 304656402109836143929723

theorem tailTrace_2669923 : CollatzResearch.WordTrace tailWord_2669923 prefixEnd_2669923 304656402109836143929723 := by
  unfold tailWord_2669923
  simp only [CollatzResearch.WordTrace]
  refine ⟨97380091906332432390566423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64920061270888288260377615 97380091906332432390566423)
  ·
    refine ⟨146070137859498648585849635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97380091906332432390566423 146070137859498648585849635)
    ·
      refine ⟨219105206789247972878774453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146070137859498648585849635 219105206789247972878774453)
      ·
        refine ⟨20541113136491997457385105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219105206789247972878774453 20541113136491997457385105)
        ·
          refine ⟨15405834852368998093038829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20541113136491997457385105 15405834852368998093038829)
          ·
            refine ⟨5777188069638374284889561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15405834852368998093038829 5777188069638374284889561)
            ·
              refine ⟨4332891052228780713667171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777188069638374284889561 4332891052228780713667171)
              ·
                refine ⟨6499336578343171070500757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332891052228780713667171 6499336578343171070500757)
                ·
                  refine ⟨304656402109836143929723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6499336578343171070500757 304656402109836143929723)
                  ·
                    rfl

theorem cell22_2669923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 6].length) (baseStart_2669923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669923 prefixEnd_2669923 := by exact prefixLift 2669923
  have htrace : WordTrace (prefixWord ++ tailWord_2669923) baseStart_2669923 baseEnd_2669923 := by
    simpa [prefixWord, tailWord_2669923, baseEnd_2669923] using wordTrace_append hprefix tailTrace_2669923
  have hstable : (prefixWord ++ tailWord_2669923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669923).length < 2 ^ (prefixWord ++ tailWord_2669923).sum := by decide
  have hdescent : baseEnd_2669923 < baseStart_2669923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669936 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_2669936 : Nat := 118140960795 + 2669936 * 2 ^ 59
def prefixEnd_2669936 : Nat := 4983230072969 + 3 ^ 40 * 2669936 * 2
def baseEnd_2669936 : Nat := 913973656495180731214129

theorem tailTrace_2669936 : CollatzResearch.WordTrace tailWord_2669936 prefixEnd_2669936 913973656495180731214129 := by
  unfold tailWord_2669936
  simp only [CollatzResearch.WordTrace]
  refine ⟨48690283027642667805394831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64920377370190223740526441 48690283027642667805394831)
  ·
    refine ⟨73035424541464001708092247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48690283027642667805394831 73035424541464001708092247)
    ·
      refine ⟨109553136812196002562138371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73035424541464001708092247 109553136812196002562138371)
      ·
        refine ⟨164329705218294003843207557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109553136812196002562138371 164329705218294003843207557)
        ·
          refine ⟨30811819728430125720601417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164329705218294003843207557 30811819728430125720601417)
          ·
            refine ⟨23108864796322594290451063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30811819728430125720601417 23108864796322594290451063)
            ·
              refine ⟨34663297194483891435676595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23108864796322594290451063 34663297194483891435676595)
              ·
                refine ⟨51994945791725837153514893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34663297194483891435676595 51994945791725837153514893)
                ·
                  refine ⟨19498104671897188932568085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51994945791725837153514893 19498104671897188932568085)
                  ·
                    refine ⟨913973656495180731214129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19498104671897188932568085 913973656495180731214129)
                    ·
                      rfl

theorem cell22_2669936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_2669936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669936 prefixEnd_2669936 := by exact prefixLift 2669936
  have htrace : WordTrace (prefixWord ++ tailWord_2669936) baseStart_2669936 baseEnd_2669936 := by
    simpa [prefixWord, tailWord_2669936, baseEnd_2669936] using wordTrace_append hprefix tailTrace_2669936
  have hstable : (prefixWord ++ tailWord_2669936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669936).length < 2 ^ (prefixWord ++ tailWord_2669936).sum := by decide
  have hdescent : baseEnd_2669936 < baseStart_2669936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670045 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2670045 : Nat := 118140960795 + 2670045 * 2 ^ 59
def prefixEnd_2670045 : Nat := 4983230072969 + 3 ^ 40 * 2670045 * 2
def baseEnd_2670045 : Nat := 914010969422740780238795

theorem tailTrace_2670045 : CollatzResearch.WordTrace tailWord_2670045 prefixEnd_2670045 914010969422740780238795 := by
  unfold tailWord_2670045
  simp only [CollatzResearch.WordTrace]
  refine ⟨97384541611890447226507589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64923027741260298151005059 97384541611890447226507589)
  ·
    refine ⟨18259601552229458854970173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97384541611890447226507589 18259601552229458854970173)
    ·
      refine ⟨6847350582086047070613815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18259601552229458854970173 6847350582086047070613815)
      ·
        refine ⟨10271025873129070605920723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847350582086047070613815 10271025873129070605920723)
        ·
          refine ⟨15406538809693605908881085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10271025873129070605920723 15406538809693605908881085)
          ·
            refine ⟨5777452053635102215830407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15406538809693605908881085 5777452053635102215830407)
            ·
              refine ⟨8666178080452653323745611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5777452053635102215830407 8666178080452653323745611)
              ·
                refine ⟨12999267120678979985618417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8666178080452653323745611 12999267120678979985618417)
                ·
                  refine ⟨9749450340509234989213813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12999267120678979985618417 9749450340509234989213813)
                  ·
                    refine ⟨914010969422740780238795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9749450340509234989213813 914010969422740780238795)
                    ·
                      rfl

theorem cell22_2670045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2670045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670045 prefixEnd_2670045 := by exact prefixLift 2670045
  have htrace : WordTrace (prefixWord ++ tailWord_2670045) baseStart_2670045 baseEnd_2670045 := by
    simpa [prefixWord, tailWord_2670045, baseEnd_2670045] using wordTrace_append hprefix tailTrace_2670045
  have hstable : (prefixWord ++ tailWord_2670045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670045).length < 2 ^ (prefixWord ++ tailWord_2670045).sum := by decide
  have hdescent : baseEnd_2670045 < baseStart_2670045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670077 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_2670077 : Nat := 118140960795 + 2670077 * 2 ^ 59
def prefixEnd_2670077 : Nat := 4983230072969 + 3 ^ 40 * 2670077 * 2
def baseEnd_2670077 : Nat := 914021923676703363438697

theorem tailTrace_2670077 : CollatzResearch.WordTrace tailWord_2670077 prefixEnd_2670077 914021923676703363438697 := by
  unfold tailWord_2670077
  simp only [CollatzResearch.WordTrace]
  refine ⟨97385708747774516691672485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64923805831849677794448323 97385708747774516691672485)
  ·
    refine ⟨18259820390207721879688591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97385708747774516691672485 18259820390207721879688591)
    ·
      refine ⟨27389730585311582819532887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18259820390207721879688591 27389730585311582819532887)
      ·
        refine ⟨41084595877967374229299331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27389730585311582819532887 41084595877967374229299331)
        ·
          refine ⟨61626893816951061343948997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41084595877967374229299331 61626893816951061343948997)
          ·
            refine ⟨11555042590678324001990437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61626893816951061343948997 11555042590678324001990437)
            ·
              refine ⟨2166570485752185750373207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11555042590678324001990437 2166570485752185750373207)
              ·
                refine ⟨3249855728628278625559811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166570485752185750373207 3249855728628278625559811)
                ·
                  refine ⟨4874783592942417938339717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249855728628278625559811 4874783592942417938339717)
                  ·
                    refine ⟨914021923676703363438697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4874783592942417938339717 914021923676703363438697)
                    ·
                      rfl

theorem cell22_2670077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_2670077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670077 prefixEnd_2670077 := by exact prefixLift 2670077
  have htrace : WordTrace (prefixWord ++ tailWord_2670077) baseStart_2670077 baseEnd_2670077 := by
    simpa [prefixWord, tailWord_2670077, baseEnd_2670077] using wordTrace_append hprefix tailTrace_2670077
  have hstable : (prefixWord ++ tailWord_2670077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670077).length < 2 ^ (prefixWord ++ tailWord_2670077).sum := by decide
  have hdescent : baseEnd_2670077 < baseStart_2670077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670244 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2670244 : Nat := 118140960795 + 2670244 * 2 ^ 59
def prefixEnd_2670244 : Nat := 4983230072969 + 3 ^ 40 * 2670244 * 2
def baseEnd_2670244 : Nat := 304693030396523531504395

theorem tailTrace_2670244 : CollatzResearch.WordTrace tailWord_2670244 prefixEnd_2670244 304693030396523531504395 := by
  unfold tailWord_2670244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48695899869084752106500893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64927866492113002808667857 48695899869084752106500893)
  ·
    refine ⟨18260962450906782039937835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48695899869084752106500893 18260962450906782039937835)
    ·
      refine ⟨27391443676360173059906753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18260962450906782039937835 27391443676360173059906753)
      ·
        refine ⟨20543582757270129794930065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27391443676360173059906753 20543582757270129794930065)
        ·
          refine ⟨15407687067952597346197549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20543582757270129794930065 15407687067952597346197549)
          ·
            refine ⟨5777882650482224004824081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15407687067952597346197549 5777882650482224004824081)
            ·
              refine ⟨4333411987861668003618061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777882650482224004824081 4333411987861668003618061)
              ·
                refine ⟨1625029495448125501356773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4333411987861668003618061 1625029495448125501356773)
                ·
                  refine ⟨304693030396523531504395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625029495448125501356773 304693030396523531504395)
                  ·
                    rfl

theorem cell22_2670244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2670244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670244 prefixEnd_2670244 := by exact prefixLift 2670244
  have htrace : WordTrace (prefixWord ++ tailWord_2670244) baseStart_2670244 baseEnd_2670244 := by
    simpa [prefixWord, tailWord_2670244, baseEnd_2670244] using wordTrace_append hprefix tailTrace_2670244
  have hstable : (prefixWord ++ tailWord_2670244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670244).length < 2 ^ (prefixWord ++ tailWord_2670244).sum := by decide
  have hdescent : baseEnd_2670244 < baseStart_2670244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670276 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2670276 : Nat := 118140960795 + 2670276 * 2 ^ 59
def prefixEnd_2670276 : Nat := 4983230072969 + 3 ^ 40 * 2670276 * 2
def baseEnd_2670276 : Nat := 914090045443533177713087

theorem tailTrace_2670276 : CollatzResearch.WordTrace tailWord_2670276 prefixEnd_2670276 914090045443533177713087 := by
  unfold tailWord_2670276
  simp only [CollatzResearch.WordTrace]
  refine ⟨48696483437026786839083341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64928644582702382452111121 48696483437026786839083341)
  ·
    refine ⟨18261181288885045064656253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48696483437026786839083341 18261181288885045064656253)
    ·
      refine ⟨6847942983331891899246095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18261181288885045064656253 6847942983331891899246095)
      ·
        refine ⟨10271914474997837848869143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847942983331891899246095 10271914474997837848869143)
        ·
          refine ⟨15407871712496756773303715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10271914474997837848869143 15407871712496756773303715)
          ·
            refine ⟨23111807568745135159955573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15407871712496756773303715 23111807568745135159955573)
            ·
              refine ⟨2166731959569856421245835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23111807568745135159955573 2166731959569856421245835)
              ·
                refine ⟨3250097939354784631868753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166731959569856421245835 3250097939354784631868753)
                ·
                  refine ⟨2437573454516088473901565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3250097939354784631868753 2437573454516088473901565)
                  ·
                    refine ⟨914090045443533177713087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2437573454516088473901565 914090045443533177713087)
                    ·
                      rfl

theorem cell22_2670276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2670276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670276 prefixEnd_2670276 := by exact prefixLift 2670276
  have htrace : WordTrace (prefixWord ++ tailWord_2670276) baseStart_2670276 baseEnd_2670276 := by
    simpa [prefixWord, tailWord_2670276, baseEnd_2670276] using wordTrace_append hprefix tailTrace_2670276
  have hstable : (prefixWord ++ tailWord_2670276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670276).length < 2 ^ (prefixWord ++ tailWord_2670276).sum := by decide
  have hdescent : baseEnd_2670276 < baseStart_2670276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670315 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_2670315 : Nat := 118140960795 + 2670315 * 2 ^ 59
def prefixEnd_2670315 : Nat := 4983230072969 + 3 ^ 40 * 2670315 * 2
def baseEnd_2670315 : Nat := 914103395940550075987967

theorem tailTrace_2670315 : CollatzResearch.WordTrace tailWord_2670315 prefixEnd_2670315 914103395940550075987967 := by
  unfold tailWord_2670315
  simp only [CollatzResearch.WordTrace]
  refine ⟨97394389320912283338836399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64929592880608188892557599 97394389320912283338836399)
  ·
    refine ⟨146091583981368425008254599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97394389320912283338836399 146091583981368425008254599)
    ·
      refine ⟨219137375972052637512381899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146091583981368425008254599 219137375972052637512381899)
      ·
        refine ⟨328706063958078956268572849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219137375972052637512381899 328706063958078956268572849)
        ·
          refine ⟨246529547968559217201429637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328706063958078956268572849 246529547968559217201429637)
          ·
            refine ⟨46224290244104853225268057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246529547968559217201429637 46224290244104853225268057)
            ·
              refine ⟨34668217683078639918951043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46224290244104853225268057 34668217683078639918951043)
              ·
                refine ⟨52002326524617959878426565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34668217683078639918951043 52002326524617959878426565)
                ·
                  refine ⟨9750436223365867477204981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52002326524617959878426565 9750436223365867477204981)
                  ·
                    refine ⟨914103395940550075987967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9750436223365867477204981 914103395940550075987967)
                    ·
                      rfl

theorem cell22_2670315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_2670315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670315 prefixEnd_2670315 := by exact prefixLift 2670315
  have htrace : WordTrace (prefixWord ++ tailWord_2670315) baseStart_2670315 baseEnd_2670315 := by
    simpa [prefixWord, tailWord_2670315, baseEnd_2670315] using wordTrace_append hprefix tailTrace_2670315
  have hstable : (prefixWord ++ tailWord_2670315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670315).length < 2 ^ (prefixWord ++ tailWord_2670315).sum := by decide
  have hdescent : baseEnd_2670315 < baseStart_2670315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670317 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2670317 : Nat := 118140960795 + 2670317 * 2 ^ 59
def prefixEnd_2670317 : Nat := 4983230072969 + 3 ^ 40 * 2670317 * 2
def baseEnd_2670317 : Nat := 304701360193807579145987

theorem tailTrace_2670317 : CollatzResearch.WordTrace tailWord_2670317 prefixEnd_2670317 304701360193807579145987 := by
  unfold tailWord_2670317
  simp only [CollatzResearch.WordTrace]
  refine ⟨97394462266905037680409205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64929641511270025120272803 97394462266905037680409205)
  ·
    refine ⟨9130730837522347282538363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97394462266905037680409205 9130730837522347282538363)
    ·
      refine ⟨13696096256283520923807545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9130730837522347282538363 13696096256283520923807545)
      ·
        refine ⟨10272072192212640692855659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13696096256283520923807545 10272072192212640692855659)
        ·
          refine ⟨15408108288318961039283489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272072192212640692855659 15408108288318961039283489)
          ·
            refine ⟨11556081216239220779462617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15408108288318961039283489 11556081216239220779462617)
            ·
              refine ⟨8667060912179415584596963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11556081216239220779462617 8667060912179415584596963)
              ·
                refine ⟨13000591368269123376895445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667060912179415584596963 13000591368269123376895445)
                ·
                  refine ⟨304701360193807579145987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13000591368269123376895445 304701360193807579145987)
                  ·
                    rfl

theorem cell22_2670317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2670317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670317 prefixEnd_2670317 := by exact prefixLift 2670317
  have htrace : WordTrace (prefixWord ++ tailWord_2670317) baseStart_2670317 baseEnd_2670317 := by
    simpa [prefixWord, tailWord_2670317, baseEnd_2670317] using wordTrace_append hprefix tailTrace_2670317
  have hstable : (prefixWord ++ tailWord_2670317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670317).length < 2 ^ (prefixWord ++ tailWord_2670317).sum := by decide
  have hdescent : baseEnd_2670317 < baseStart_2670317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670330 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2670330 : Nat := 118140960795 + 2670330 * 2 ^ 59
def prefixEnd_2670330 : Nat := 4983230072969 + 3 ^ 40 * 2670330 * 2
def baseEnd_2670330 : Nat := 914108530747095036862921

theorem tailTrace_2670330 : CollatzResearch.WordTrace tailWord_2670330 prefixEnd_2670330 914108530747095036862921 := by
  unfold tailWord_2670330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348734103964485225158111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64929957610571960600421629 24348734103964485225158111)
  ·
    refine ⟨36523101155946727837737167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24348734103964485225158111 36523101155946727837737167)
    ·
      refine ⟨54784651733920091756605751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36523101155946727837737167 54784651733920091756605751)
      ·
        refine ⟨82176977600880137634908627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54784651733920091756605751 82176977600880137634908627)
        ·
          refine ⟨123265466401320206452362941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82176977600880137634908627 123265466401320206452362941)
          ·
            refine ⟨46224549900495077419636103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123265466401320206452362941 46224549900495077419636103)
            ·
              refine ⟨69336824850742616129454155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46224549900495077419636103 69336824850742616129454155)
              ·
                refine ⟨104005237276113924194181233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69336824850742616129454155 104005237276113924194181233)
                ·
                  refine ⟨78003927957085443145635925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104005237276113924194181233 78003927957085443145635925)
                  ·
                    refine ⟨914108530747095036862921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78003927957085443145635925 914108530747095036862921)
                    ·
                      rfl

theorem cell22_2670330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2670330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670330 prefixEnd_2670330 := by exact prefixLift 2670330
  have htrace : WordTrace (prefixWord ++ tailWord_2670330) baseStart_2670330 baseEnd_2670330 := by
    simpa [prefixWord, tailWord_2670330, baseEnd_2670330] using wordTrace_append hprefix tailTrace_2670330
  have hstable : (prefixWord ++ tailWord_2670330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670330).length < 2 ^ (prefixWord ++ tailWord_2670330).sum := by decide
  have hdescent : baseEnd_2670330 < baseStart_2670330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670342 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2670342 : Nat := 118140960795 + 2670342 * 2 ^ 59
def prefixEnd_2670342 : Nat := 4983230072969 + 3 ^ 40 * 2670342 * 2
def baseEnd_2670342 : Nat := 914112638592331005562885

theorem tailTrace_2670342 : CollatzResearch.WordTrace tailWord_2670342 prefixEnd_2670342 914112638592331005562885 := by
  unfold tailWord_2670342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043605440369202092189665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64930249394542977966712853 3043605440369202092189665)
  ·
    refine ⟨2282704080276901569142249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3043605440369202092189665 2282704080276901569142249)
    ·
      refine ⟨1712028060207676176856687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2282704080276901569142249 1712028060207676176856687)
      ·
        refine ⟨2568042090311514265285031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712028060207676176856687 2568042090311514265285031)
        ·
          refine ⟨3852063135467271397927547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568042090311514265285031 3852063135467271397927547)
          ·
            refine ⟨5778094703200907096891321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852063135467271397927547 5778094703200907096891321)
            ·
              refine ⟨4333571027400680322668491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778094703200907096891321 4333571027400680322668491)
              ·
                refine ⟨6500356541101020484002737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333571027400680322668491 6500356541101020484002737)
                ·
                  refine ⟨4875267405825765363002053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500356541101020484002737 4875267405825765363002053)
                  ·
                    refine ⟨914112638592331005562885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875267405825765363002053 914112638592331005562885)
                    ·
                      rfl

theorem cell22_2670342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2670342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670342 prefixEnd_2670342 := by exact prefixLift 2670342
  have htrace : WordTrace (prefixWord ++ tailWord_2670342) baseStart_2670342 baseEnd_2670342 := by
    simpa [prefixWord, tailWord_2670342, baseEnd_2670342] using wordTrace_append hprefix tailTrace_2670342
  have hstable : (prefixWord ++ tailWord_2670342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670342).length < 2 ^ (prefixWord ++ tailWord_2670342).sum := by decide
  have hdescent : baseEnd_2670342 < baseStart_2670342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670345 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 8]
def baseStart_2670345 : Nat := 118140960795 + 2670345 * 2 ^ 59
def prefixEnd_2670345 : Nat := 4983230072969 + 3 ^ 40 * 2670345 * 2
def baseEnd_2670345 : Nat := 304704555184546665912625

theorem tailTrace_2670345 : CollatzResearch.WordTrace tailWord_2670345 prefixEnd_2670345 304704555184546665912625 := by
  unfold tailWord_2670345
  simp only [CollatzResearch.WordTrace]
  refine ⟨97395483510803598462428489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64930322340535732308285659 97395483510803598462428489)
  ·
    refine ⟨73046612633102698846821367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97395483510803598462428489 73046612633102698846821367)
    ·
      refine ⟨109569918949654048270232051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73046612633102698846821367 109569918949654048270232051)
      ·
        refine ⟨164354878424481072405348077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109569918949654048270232051 164354878424481072405348077)
        ·
          refine ⟨61633079409180402152005529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164354878424481072405348077 61633079409180402152005529)
          ·
            refine ⟨46224809556885301614004147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61633079409180402152005529 46224809556885301614004147)
            ·
              refine ⟨69337214335327952421006221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46224809556885301614004147 69337214335327952421006221)
              ·
                refine ⟨26001455375747982157877333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69337214335327952421006221 26001455375747982157877333)
                ·
                  refine ⟨304704555184546665912625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26001455375747982157877333 304704555184546665912625)
                  ·
                    rfl

theorem cell22_2670345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_2670345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670345 prefixEnd_2670345 := by exact prefixLift 2670345
  have htrace : WordTrace (prefixWord ++ tailWord_2670345) baseStart_2670345 baseEnd_2670345 := by
    simpa [prefixWord, tailWord_2670345, baseEnd_2670345] using wordTrace_append hprefix tailTrace_2670345
  have hstable : (prefixWord ++ tailWord_2670345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670345).length < 2 ^ (prefixWord ++ tailWord_2670345).sum := by decide
  have hdescent : baseEnd_2670345 < baseStart_2670345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670394 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_2670394 : Nat := 118140960795 + 2670394 * 2 ^ 59
def prefixEnd_2670394 : Nat := 4983230072969 + 3 ^ 40 * 2670394 * 2
def baseEnd_2670394 : Nat := 914130439255020203262725

theorem tailTrace_2670394 : CollatzResearch.WordTrace tailWord_2670394 prefixEnd_2670394 914130439255020203262725 := by
  unfold tailWord_2670394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24349317671906519957740559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64931513791750719887308157 24349317671906519957740559)
  ·
    refine ⟨36523976507859779936610839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24349317671906519957740559 36523976507859779936610839)
    ·
      refine ⟨54785964761789669904916259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36523976507859779936610839 54785964761789669904916259)
      ·
        refine ⟨82178947142684504857374389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54785964761789669904916259 82178947142684504857374389)
        ·
          refine ⟨7704276294626672330378849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82178947142684504857374389 7704276294626672330378849)
          ·
            refine ⟨5778207220970004247784137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704276294626672330378849 5778207220970004247784137)
            ·
              refine ⟨4333655415727503185838103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778207220970004247784137 4333655415727503185838103)
              ·
                refine ⟨6500483123591254778757155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333655415727503185838103 6500483123591254778757155)
                ·
                  refine ⟨9750724685386882168135733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6500483123591254778757155 9750724685386882168135733)
                  ·
                    refine ⟨914130439255020203262725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9750724685386882168135733 914130439255020203262725)
                    ·
                      rfl

theorem cell22_2670394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_2670394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670394 prefixEnd_2670394 := by exact prefixLift 2670394
  have htrace : WordTrace (prefixWord ++ tailWord_2670394) baseStart_2670394 baseEnd_2670394 := by
    simpa [prefixWord, tailWord_2670394, baseEnd_2670394] using wordTrace_append hprefix tailTrace_2670394
  have hstable : (prefixWord ++ tailWord_2670394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670394).length < 2 ^ (prefixWord ++ tailWord_2670394).sum := by decide
  have hdescent : baseEnd_2670394 < baseStart_2670394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670413 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2670413 : Nat := 118140960795 + 2670413 * 2 ^ 59
def prefixEnd_2670413 : Nat := 4983230072969 + 3 ^ 40 * 2670413 * 2
def baseEnd_2670413 : Nat := 304712314447770162345889

theorem tailTrace_2670413 : CollatzResearch.WordTrace tailWord_2670413 prefixEnd_2670413 304712314447770162345889 := by
  unfold tailWord_2670413
  simp only [CollatzResearch.WordTrace]
  refine ⟨97397963674557246075903893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64931975783038164050602595 97397963674557246075903893)
  ·
    refine ⟨4565529547244870909807995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97397963674557246075903893 4565529547244870909807995)
    ·
      refine ⟨6848294320867306364711993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4565529547244870909807995 6848294320867306364711993)
      ·
        refine ⟨5136220740650479773533995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6848294320867306364711993 5136220740650479773533995)
        ·
          refine ⟨7704331110975719660300993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136220740650479773533995 7704331110975719660300993)
          ·
            refine ⟨5778248333231789745225745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704331110975719660300993 5778248333231789745225745)
            ·
              refine ⟨4333686249923842308919309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778248333231789745225745 4333686249923842308919309)
              ·
                refine ⟨1625132343721440865844741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4333686249923842308919309 1625132343721440865844741)
                ·
                  refine ⟨304712314447770162345889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625132343721440865844741 304712314447770162345889)
                  ·
                    rfl

theorem cell22_2670413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2670413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670413 prefixEnd_2670413 := by exact prefixLift 2670413
  have htrace : WordTrace (prefixWord ++ tailWord_2670413) baseStart_2670413 baseEnd_2670413 := by
    simpa [prefixWord, tailWord_2670413, baseEnd_2670413] using wordTrace_append hprefix tailTrace_2670413
  have hstable : (prefixWord ++ tailWord_2670413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670413).length < 2 ^ (prefixWord ++ tailWord_2670413).sum := by decide
  have hdescent : baseEnd_2670413 < baseStart_2670413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670490 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_2670490 : Nat := 118140960795 + 2670490 * 2 ^ 59
def prefixEnd_2670490 : Nat := 4983230072969 + 3 ^ 40 * 2670490 * 2
def baseEnd_2670490 : Nat := 914163302016907952862431

theorem tailTrace_2670490 : CollatzResearch.WordTrace tailWord_2670490 prefixEnd_2670490 914163302016907952862431 := by
  unfold tailWord_2670490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24350193023819572056614231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64933848063518858817637949 24350193023819572056614231)
  ·
    refine ⟨36525289535729358084921347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24350193023819572056614231 36525289535729358084921347)
    ·
      refine ⟨54787934303594037127382021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36525289535729358084921347 54787934303594037127382021)
      ·
        refine ⟨10272737681923881961384129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54787934303594037127382021 10272737681923881961384129)
        ·
          refine ⟨7704553261442911471038097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10272737681923881961384129 7704553261442911471038097)
          ·
            refine ⟨5778414946082183603278573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704553261442911471038097 5778414946082183603278573)
            ·
              refine ⟨2166905604780818851229465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5778414946082183603278573 2166905604780818851229465)
              ·
                refine ⟨1625179203585614138422099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166905604780818851229465 1625179203585614138422099)
                ·
                  refine ⟨2437768805378421207633149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625179203585614138422099 2437768805378421207633149)
                  ·
                    refine ⟨914163302016907952862431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2437768805378421207633149 914163302016907952862431)
                    ·
                      rfl

theorem cell22_2670490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_2670490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670490 prefixEnd_2670490 := by exact prefixLift 2670490
  have htrace : WordTrace (prefixWord ++ tailWord_2670490) baseStart_2670490 baseEnd_2670490 := by
    simpa [prefixWord, tailWord_2670490, baseEnd_2670490] using wordTrace_append hprefix tailTrace_2670490
  have hstable : (prefixWord ++ tailWord_2670490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670490).length < 2 ^ (prefixWord ++ tailWord_2670490).sum := by decide
  have hdescent : baseEnd_2670490 < baseStart_2670490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670503 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 5]
def baseStart_2670503 : Nat := 118140960795 + 2670503 * 2 ^ 59
def prefixEnd_2670503 : Nat := 4983230072969 + 3 ^ 40 * 2670503 * 2
def baseEnd_2670503 : Nat := 304722584060860084095797

theorem tailTrace_2670503 : CollatzResearch.WordTrace tailWord_2670503 prefixEnd_2670503 304722584060860084095797 := by
  unfold tailWord_2670503
  simp only [CollatzResearch.WordTrace]
  refine ⟨97401246244231191446680163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64934164162820794297786775 97401246244231191446680163)
  ·
    refine ⟨146101869366346787170020245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97401246244231191446680163 146101869366346787170020245)
    ·
      refine ⟨6848525126547505648594699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146101869366346787170020245 6848525126547505648594699)
      ·
        refine ⟨10272787689821258472892049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848525126547505648594699 10272787689821258472892049)
        ·
          refine ⟨7704590767365943854669037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10272787689821258472892049 7704590767365943854669037)
          ·
            refine ⟨2889221537762228945500889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7704590767365943854669037 2889221537762228945500889)
            ·
              refine ⟨2166916153321671709125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2889221537762228945500889 2166916153321671709125667)
              ·
                refine ⟨3250374229982507563688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166916153321671709125667 3250374229982507563688501)
                ·
                  refine ⟨304722584060860084095797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3250374229982507563688501 304722584060860084095797)
                  ·
                    rfl

theorem cell22_2670503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 5].length) (baseStart_2670503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670503 prefixEnd_2670503 := by exact prefixLift 2670503
  have htrace : WordTrace (prefixWord ++ tailWord_2670503) baseStart_2670503 baseEnd_2670503 := by
    simpa [prefixWord, tailWord_2670503, baseEnd_2670503] using wordTrace_append hprefix tailTrace_2670503
  have hstable : (prefixWord ++ tailWord_2670503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670503).length < 2 ^ (prefixWord ++ tailWord_2670503).sum := by decide
  have hdescent : baseEnd_2670503 < baseStart_2670503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670512 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_2670512 : Nat := 118140960795 + 2670512 * 2 ^ 59
def prefixEnd_2670512 : Nat := 4983230072969 + 3 ^ 40 * 2670512 * 2
def baseEnd_2670512 : Nat := 914170833066507228812363

theorem tailTrace_2670512 : CollatzResearch.WordTrace tailWord_2670512 prefixEnd_2670512 914170833066507228812363 := by
  unfold tailWord_2670512
  simp only [CollatzResearch.WordTrace]
  refine ⟨48700787250599292991878895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64934383000799057322505193 48700787250599292991878895)
  ·
    refine ⟨73051180875898939487818343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48700787250599292991878895 73051180875898939487818343)
    ·
      refine ⟨109576771313848409231727515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73051180875898939487818343 109576771313848409231727515)
      ·
        refine ⟨164365156970772613847591273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109576771313848409231727515 164365156970772613847591273)
        ·
          refine ⟨123273867728079460385693455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164365156970772613847591273 123273867728079460385693455)
          ·
            refine ⟨184910801592119190578540183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123273867728079460385693455 184910801592119190578540183)
            ·
              refine ⟨277366202388178785867810275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184910801592119190578540183 277366202388178785867810275)
              ·
                refine ⟨416049303582268178801715413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277366202388178785867810275 416049303582268178801715413)
                ·
                  refine ⟨9751155552709410440665205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 416049303582268178801715413 9751155552709410440665205)
                  ·
                    refine ⟨914170833066507228812363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9751155552709410440665205 914170833066507228812363)
                    ·
                      rfl

theorem cell22_2670512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_2670512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670512 prefixEnd_2670512 := by exact prefixLift 2670512
  have htrace : WordTrace (prefixWord ++ tailWord_2670512) baseStart_2670512 baseEnd_2670512 := by
    simpa [prefixWord, tailWord_2670512, baseEnd_2670512] using wordTrace_append hprefix tailTrace_2670512
  have hstable : (prefixWord ++ tailWord_2670512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670512).length < 2 ^ (prefixWord ++ tailWord_2670512).sum := by decide
  have hdescent : baseEnd_2670512 < baseStart_2670512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670544 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_2670544 : Nat := 118140960795 + 2670544 * 2 ^ 59
def prefixEnd_2670544 : Nat := 4983230072969 + 3 ^ 40 * 2670544 * 2
def baseEnd_2670544 : Nat := 914181787320469812012265

theorem tailTrace_2670544 : CollatzResearch.WordTrace tailWord_2670544 prefixEnd_2670544 914181787320469812012265 := by
  unfold tailWord_2670544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48701370818541327724461343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64935161091388436965948457 48701370818541327724461343)
  ·
    refine ⟨73052056227811991586692015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48701370818541327724461343 73052056227811991586692015)
    ·
      refine ⟨109578084341717987380038023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73052056227811991586692015 109578084341717987380038023)
      ·
        refine ⟨164367126512576981070057035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109578084341717987380038023 164367126512576981070057035)
        ·
          refine ⟨246550689768865471605085553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164367126512576981070057035 246550689768865471605085553)
          ·
            refine ⟨184913017326649103703814165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246550689768865471605085553 184913017326649103703814165)
            ·
              refine ⟨8667797687186676736116289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184913017326649103703814165 8667797687186676736116289)
              ·
                refine ⟨6500848265390007552087217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8667797687186676736116289 6500848265390007552087217)
                ·
                  refine ⟨4875636199042505664065413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500848265390007552087217 4875636199042505664065413)
                  ·
                    refine ⟨914181787320469812012265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875636199042505664065413 914181787320469812012265)
                    ·
                      rfl

theorem cell22_2670544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_2670544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670544 prefixEnd_2670544 := by exact prefixLift 2670544
  have htrace : WordTrace (prefixWord ++ tailWord_2670544) baseStart_2670544 baseEnd_2670544 := by
    simpa [prefixWord, tailWord_2670544, baseEnd_2670544] using wordTrace_append hprefix tailTrace_2670544
  have hstable : (prefixWord ++ tailWord_2670544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670544).length < 2 ^ (prefixWord ++ tailWord_2670544).sum := by decide
  have hdescent : baseEnd_2670544 < baseStart_2670544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670559 : List Nat := [1, 1, 2, 3, 4, 1, 3, 7]
def baseStart_2670559 : Nat := 118140960795 + 2670559 * 2 ^ 59
def prefixEnd_2670559 : Nat := 4983230072969 + 3 ^ 40 * 2670559 * 2
def baseEnd_2670559 : Nat := 101576324680779419209691

theorem tailTrace_2670559 : CollatzResearch.WordTrace tailWord_2670559 prefixEnd_2670559 101576324680779419209691 := by
  unfold tailWord_2670559
  simp only [CollatzResearch.WordTrace]
  refine ⟨97403288732028313010718731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64935525821352208673812487 97403288732028313010718731)
  ·
    refine ⟨146104933098042469516078097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97403288732028313010718731 146104933098042469516078097)
    ·
      refine ⟨109578699823531852137058573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146104933098042469516078097 109578699823531852137058573)
      ·
        refine ⟨41092012433824444551396965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109578699823531852137058573 41092012433824444551396965)
        ·
          refine ⟨7704752331342083353386931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41092012433824444551396965 7704752331342083353386931)
          ·
            refine ⟨11557128497013125030080397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7704752331342083353386931 11557128497013125030080397)
            ·
              refine ⟨4333923186379921886280149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11557128497013125030080397 4333923186379921886280149)
              ·
                refine ⟨101576324680779419209691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4333923186379921886280149 101576324680779419209691)
                ·
                  rfl

theorem cell22_2670559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 7].length) (baseStart_2670559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670559 prefixEnd_2670559 := by exact prefixLift 2670559
  have htrace : WordTrace (prefixWord ++ tailWord_2670559) baseStart_2670559 baseEnd_2670559 := by
    simpa [prefixWord, tailWord_2670559, baseEnd_2670559] using wordTrace_append hprefix tailTrace_2670559
  have hstable : (prefixWord ++ tailWord_2670559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670559).length < 2 ^ (prefixWord ++ tailWord_2670559).sum := by decide
  have hdescent : baseEnd_2670559 < baseStart_2670559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670604 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_2670604 : Nat := 118140960795 + 2670604 * 2 ^ 59
def prefixEnd_2670604 : Nat := 4983230072969 + 3 ^ 40 * 2670604 * 2
def baseEnd_2670604 : Nat := 304734108848883218504027

theorem tailTrace_2670604 : CollatzResearch.WordTrace tailWord_2670604 prefixEnd_2670604 304734108848883218504027 := by
  unfold tailWord_2670604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48702465008432642848053433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64936620011243523797404577 48702465008432642848053433)
  ·
    refine ⟨36526848756324482136040075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48702465008432642848053433 36526848756324482136040075)
    ·
      refine ⟨54790273134486723204060113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36526848756324482136040075 54790273134486723204060113)
      ·
        refine ⟨41092704850865042403045085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54790273134486723204060113 41092704850865042403045085)
        ·
          refine ⟨15409764319074390901141907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41092704850865042403045085 15409764319074390901141907)
          ·
            refine ⟨23114646478611586351712861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15409764319074390901141907 23114646478611586351712861)
            ·
              refine ⟨8667992429479344881892323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23114646478611586351712861 8667992429479344881892323)
              ·
                refine ⟨13001988644219017322838485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667992429479344881892323 13001988644219017322838485)
                ·
                  refine ⟨304734108848883218504027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13001988644219017322838485 304734108848883218504027)
                  ·
                    rfl

theorem cell22_2670604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_2670604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670604 prefixEnd_2670604 := by exact prefixLift 2670604
  have htrace : WordTrace (prefixWord ++ tailWord_2670604) baseStart_2670604 baseEnd_2670604 := by
    simpa [prefixWord, tailWord_2670604, baseEnd_2670604] using wordTrace_append hprefix tailTrace_2670604
  have hstable : (prefixWord ++ tailWord_2670604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670604).length < 2 ^ (prefixWord ++ tailWord_2670604).sum := by decide
  have hdescent : baseEnd_2670604 < baseStart_2670604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670664 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_2670664 : Nat := 118140960795 + 2670664 * 2 ^ 59
def prefixEnd_2670664 : Nat := 4983230072969 + 3 ^ 40 * 2670664 * 2
def baseEnd_2670664 : Nat := 914222865772829499011897

theorem tailTrace_2670664 : CollatzResearch.WordTrace tailWord_2670664 prefixEnd_2670664 914222865772829499011897 := by
  unfold tailWord_2670664
  simp only [CollatzResearch.WordTrace]
  refine ⟨48703559198323957971645523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64938078931098610628860697 48703559198323957971645523)
  ·
    refine ⟨73055338797485936957468285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48703559198323957971645523 73055338797485936957468285)
    ·
      refine ⟨27395752049057226359050607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73055338797485936957468285 27395752049057226359050607)
      ·
        refine ⟨41093628073585839538575911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27395752049057226359050607 41093628073585839538575911)
        ·
          refine ⟨61640442110378759307863867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41093628073585839538575911 61640442110378759307863867)
          ·
            refine ⟨92460663165568138961795801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61640442110378759307863867 92460663165568138961795801)
            ·
              refine ⟨69345497374176104221346851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92460663165568138961795801 69345497374176104221346851)
              ·
                refine ⟨104018246061264156332020277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69345497374176104221346851 104018246061264156332020277)
                ·
                  refine ⟨9751710568243514656126901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104018246061264156332020277 9751710568243514656126901)
                  ·
                    refine ⟨914222865772829499011897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9751710568243514656126901 914222865772829499011897)
                    ·
                      rfl

theorem cell22_2670664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_2670664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670664 prefixEnd_2670664 := by exact prefixLift 2670664
  have htrace : WordTrace (prefixWord ++ tailWord_2670664) baseStart_2670664 baseEnd_2670664 := by
    simpa [prefixWord, tailWord_2670664, baseEnd_2670664] using wordTrace_append hprefix tailTrace_2670664
  have hstable : (prefixWord ++ tailWord_2670664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670664).length < 2 ^ (prefixWord ++ tailWord_2670664).sum := by decide
  have hdescent : baseEnd_2670664 < baseStart_2670664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670679 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2670679 : Nat := 118140960795 + 2670679 * 2 ^ 59
def prefixEnd_2670679 : Nat := 4983230072969 + 3 ^ 40 * 2670679 * 2
def baseEnd_2670679 : Nat := 914228000579374459886851

theorem tailTrace_2670679 : CollatzResearch.WordTrace tailWord_2670679 prefixEnd_2670679 914228000579374459886851 := by
  unfold tailWord_2670679
  simp only [CollatzResearch.WordTrace]
  refine ⟨97407665491593573505087091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64938443661062382336724727 97407665491593573505087091)
  ·
    refine ⟨146111498237390360257630637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97407665491593573505087091 146111498237390360257630637)
    ·
      refine ⟨54791811839021385096611489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146111498237390360257630637 54791811839021385096611489)
      ·
        refine ⟨41093858879266038822458617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54791811839021385096611489 41093858879266038822458617)
        ·
          refine ⟨30820394159449529116843963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41093858879266038822458617 30820394159449529116843963)
          ·
            refine ⟨46230591239174293675265945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30820394159449529116843963 46230591239174293675265945)
            ·
              refine ⟨34672943429380720256449459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46230591239174293675265945 34672943429380720256449459)
              ·
                refine ⟨52009415144071080384674189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34672943429380720256449459 52009415144071080384674189)
                ·
                  refine ⟨19503530679026655144252821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52009415144071080384674189 19503530679026655144252821)
                  ·
                    refine ⟨914228000579374459886851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19503530679026655144252821 914228000579374459886851)
                    ·
                      rfl

theorem cell22_2670679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2670679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670679 prefixEnd_2670679 := by exact prefixLift 2670679
  have htrace : WordTrace (prefixWord ++ tailWord_2670679) baseStart_2670679 baseEnd_2670679 := by
    simpa [prefixWord, tailWord_2670679, baseEnd_2670679] using wordTrace_append hprefix tailTrace_2670679
  have hstable : (prefixWord ++ tailWord_2670679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670679).length < 2 ^ (prefixWord ++ tailWord_2670679).sum := by decide
  have hdescent : baseEnd_2670679 < baseStart_2670679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670685 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2670685 : Nat := 118140960795 + 2670685 * 2 ^ 59
def prefixEnd_2670685 : Nat := 4983230072969 + 3 ^ 40 * 2670685 * 2
def baseEnd_2670685 : Nat := 914230054501992444236833

theorem tailTrace_2670685 : CollatzResearch.WordTrace tailWord_2670685 prefixEnd_2670685 914230054501992444236833 := by
  unfold tailWord_2670685
  simp only [CollatzResearch.WordTrace]
  refine ⟨97407884329571836529805509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64938589553047891019870339 97407884329571836529805509)
  ·
    refine ⟨18263978311794719349338533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97407884329571836529805509 18263978311794719349338533)
    ·
      refine ⟨3424495933461509878000975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18263978311794719349338533 3424495933461509878000975)
      ·
        refine ⟨5136743900192264817001463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3424495933461509878000975 5136743900192264817001463)
        ·
          refine ⟨7705115850288397225502195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136743900192264817001463 7705115850288397225502195)
          ·
            refine ⟨11557673775432595838253293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705115850288397225502195 11557673775432595838253293)
            ·
              refine ⟨4334127665787223439344985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11557673775432595838253293 4334127665787223439344985)
              ·
                refine ⟨3250595749340417579508739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334127665787223439344985 3250595749340417579508739)
                ·
                  refine ⟨4875893624010626369263109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250595749340417579508739 4875893624010626369263109)
                  ·
                    refine ⟨914230054501992444236833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875893624010626369263109 914230054501992444236833)
                    ·
                      rfl

theorem cell22_2670685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2670685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670685 prefixEnd_2670685 := by exact prefixLift 2670685
  have htrace : WordTrace (prefixWord ++ tailWord_2670685) baseStart_2670685 baseEnd_2670685 := by
    simpa [prefixWord, tailWord_2670685, baseEnd_2670685] using wordTrace_append hprefix tailTrace_2670685
  have hstable : (prefixWord ++ tailWord_2670685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670685).length < 2 ^ (prefixWord ++ tailWord_2670685).sum := by decide
  have hdescent : baseEnd_2670685 < baseStart_2670685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670698 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2670698 : Nat := 118140960795 + 2670698 * 2 ^ 59
def prefixEnd_2670698 : Nat := 4983230072969 + 3 ^ 40 * 2670698 * 2
def baseEnd_2670698 : Nat := 914234504667664743661793

theorem tailTrace_2670698 : CollatzResearch.WordTrace tailWord_2670698 prefixEnd_2670698 914234504667664743661793 := by
  unfold tailWord_2670698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24352089619631184937507187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64938905652349826500019165 24352089619631184937507187)
  ·
    refine ⟨36528134429446777406260781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24352089619631184937507187 36528134429446777406260781)
    ·
      refine ⟨13698050411042541527347793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36528134429446777406260781 13698050411042541527347793)
      ·
        refine ⟨10273537808281906145510845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13698050411042541527347793 10273537808281906145510845)
        ·
          refine ⟨3852576678105714804566567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10273537808281906145510845 3852576678105714804566567)
          ·
            refine ⟨5778865017158572206849851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852576678105714804566567 5778865017158572206849851)
            ·
              refine ⟨8668297525737858310274777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778865017158572206849851 8668297525737858310274777)
              ·
                refine ⟨6501223144303393732706083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8668297525737858310274777 6501223144303393732706083)
                ·
                  refine ⟨9751834716455090599059125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6501223144303393732706083 9751834716455090599059125)
                  ·
                    refine ⟨914234504667664743661793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9751834716455090599059125 914234504667664743661793)
                    ·
                      rfl

theorem cell22_2670698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2670698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670698 prefixEnd_2670698 := by exact prefixLift 2670698
  have htrace : WordTrace (prefixWord ++ tailWord_2670698) baseStart_2670698 baseEnd_2670698 := by
    simpa [prefixWord, tailWord_2670698, baseEnd_2670698] using wordTrace_append hprefix tailTrace_2670698
  have hstable : (prefixWord ++ tailWord_2670698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670698).length < 2 ^ (prefixWord ++ tailWord_2670698).sum := by decide
  have hdescent : baseEnd_2670698 < baseStart_2670698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670728 : List Nat := [2, 1, 3, 4, 1, 3, 1, 7]
def baseStart_2670728 : Nat := 118140960795 + 2670728 * 2 ^ 59
def prefixEnd_2670728 : Nat := 4983230072969 + 3 ^ 40 * 2670728 * 2
def baseEnd_2670728 : Nat := 101582752697861629490189

theorem tailTrace_2670728 : CollatzResearch.WordTrace tailWord_2670728 prefixEnd_2670728 101582752697861629490189 := by
  unfold tailWord_2670728
  simp only [CollatzResearch.WordTrace]
  refine ⟨48704726334208027436810419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64939635112277369915747225 48704726334208027436810419)
  ·
    refine ⟨73057089501312041155215629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48704726334208027436810419 73057089501312041155215629)
    ·
      refine ⟨27396408562992015433205861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73057089501312041155215629 27396408562992015433205861)
      ·
        refine ⟨5136826605561002893726099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27396408562992015433205861 5136826605561002893726099)
        ·
          refine ⟨7705239908341504340589149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136826605561002893726099 7705239908341504340589149)
          ·
            refine ⟨2889464965628064127720931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7705239908341504340589149 2889464965628064127720931)
            ·
              refine ⟨4334197448442096191581397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889464965628064127720931 4334197448442096191581397)
              ·
                refine ⟨101582752697861629490189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4334197448442096191581397 101582752697861629490189)
                ·
                  rfl

theorem cell22_2670728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_2670728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670728 prefixEnd_2670728 := by exact prefixLift 2670728
  have htrace : WordTrace (prefixWord ++ tailWord_2670728) baseStart_2670728 baseEnd_2670728 := by
    simpa [prefixWord, tailWord_2670728, baseEnd_2670728] using wordTrace_append hprefix tailTrace_2670728
  have hstable : (prefixWord ++ tailWord_2670728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670728).length < 2 ^ (prefixWord ++ tailWord_2670728).sum := by decide
  have hdescent : baseEnd_2670728 < baseStart_2670728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670739 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 9]
def baseStart_2670739 : Nat := 118140960795 + 2670739 * 2 ^ 59
def prefixEnd_2670739 : Nat := 4983230072969 + 3 ^ 40 * 2670739 * 2
def baseEnd_2670739 : Nat := 304749513268518101128889

theorem tailTrace_2670739 : CollatzResearch.WordTrace tailWord_2670739 prefixEnd_2670739 304749513268518101128889 := by
  unfold tailWord_2670739
  simp only [CollatzResearch.WordTrace]
  refine ⟨97409853871376203752271271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64939902580917469168180847 97409853871376203752271271)
  ·
    refine ⟨146114780807064305628406907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97409853871376203752271271 146114780807064305628406907)
    ·
      refine ⟨219172171210596458442610361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146114780807064305628406907 219172171210596458442610361)
      ·
        refine ⟨164379128407947343831957771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219172171210596458442610361 164379128407947343831957771)
        ·
          refine ⟨246568692611921015747936657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164379128407947343831957771 246568692611921015747936657)
          ·
            refine ⟨184926519458940761810952493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246568692611921015747936657 184926519458940761810952493)
            ·
              refine ⟨69347444797102785679107185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184926519458940761810952493 69347444797102785679107185)
              ·
                refine ⟨52010583597827089259330389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69347444797102785679107185 52010583597827089259330389)
                ·
                  refine ⟨304749513268518101128889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52010583597827089259330389 304749513268518101128889)
                  ·
                    rfl

theorem cell22_2670739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_2670739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670739 prefixEnd_2670739 := by exact prefixLift 2670739
  have htrace : WordTrace (prefixWord ++ tailWord_2670739) baseStart_2670739 baseEnd_2670739 := by
    simpa [prefixWord, tailWord_2670739, baseEnd_2670739] using wordTrace_append hprefix tailTrace_2670739
  have hstable : (prefixWord ++ tailWord_2670739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670739).length < 2 ^ (prefixWord ++ tailWord_2670739).sum := by decide
  have hdescent : baseEnd_2670739 < baseStart_2670739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670766 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2670766 : Nat := 118140960795 + 2670766 * 2 ^ 59
def prefixEnd_2670766 : Nat := 4983230072969 + 3 ^ 40 * 2670766 * 2
def baseEnd_2670766 : Nat := 914257782457335232961585

theorem tailTrace_2670766 : CollatzResearch.WordTrace tailWord_2670766 prefixEnd_2670766 914257782457335232961585 := by
  unfold tailWord_2670766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12176354830284798420438019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64940559094852258242336101 12176354830284798420438019)
  ·
    refine ⟨18264532245427197630657029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12176354830284798420438019 18264532245427197630657029)
    ·
      refine ⟨3424599796017599555748193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18264532245427197630657029 3424599796017599555748193)
      ·
        refine ⟨2568449847013199666811145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3424599796017599555748193 2568449847013199666811145)
        ·
          refine ⟨1926337385259899750108359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2568449847013199666811145 1926337385259899750108359)
          ·
            refine ⟨2889506077889849625162539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926337385259899750108359 2889506077889849625162539)
            ·
              refine ⟨4334259116834774437743809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889506077889849625162539 4334259116834774437743809)
              ·
                refine ⟨3250694337626080828307857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334259116834774437743809 3250694337626080828307857)
                ·
                  refine ⟨2438020753219560621230893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3250694337626080828307857 2438020753219560621230893)
                  ·
                    refine ⟨914257782457335232961585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438020753219560621230893 914257782457335232961585)
                    ·
                      rfl

theorem cell22_2670766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2670766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670766 prefixEnd_2670766 := by exact prefixLift 2670766
  have htrace : WordTrace (prefixWord ++ tailWord_2670766) baseStart_2670766 baseEnd_2670766 := by
    simpa [prefixWord, tailWord_2670766, baseEnd_2670766] using wordTrace_append hprefix tailTrace_2670766
  have hstable : (prefixWord ++ tailWord_2670766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670766).length < 2 ^ (prefixWord ++ tailWord_2670766).sum := by decide
  have hdescent : baseEnd_2670766 < baseStart_2670766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670788 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2670788 : Nat := 118140960795 + 2670788 * 2 ^ 59
def prefixEnd_2670788 : Nat := 4983230072969 + 3 ^ 40 * 2670788 * 2
def baseEnd_2670788 : Nat := 914265313506934508911517

theorem tailTrace_2670788 : CollatzResearch.WordTrace tailWord_2670788 prefixEnd_2670788 914265313506934508911517 := by
  unfold tailWord_2670788
  simp only [CollatzResearch.WordTrace]
  refine ⟨48705820524099342560402509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64941094032132456747203345 48705820524099342560402509)
  ·
    refine ⟨18264682696537253460150941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48705820524099342560402509 18264682696537253460150941)
    ·
      refine ⟨6849256011201470047556603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18264682696537253460150941 6849256011201470047556603)
      ·
        refine ⟨10273884016802205071334905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6849256011201470047556603 10273884016802205071334905)
        ·
          refine ⟨7705413012601653803501179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273884016802205071334905 7705413012601653803501179)
          ·
            refine ⟨11558119518902480705251769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705413012601653803501179 11558119518902480705251769)
            ·
              refine ⟨8668589639176860528938827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11558119518902480705251769 8668589639176860528938827)
              ·
                refine ⟨13002884458765290793408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668589639176860528938827 13002884458765290793408241)
                ·
                  refine ⟨9752163344073968095056181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13002884458765290793408241 9752163344073968095056181)
                  ·
                    refine ⟨914265313506934508911517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9752163344073968095056181 914265313506934508911517)
                    ·
                      rfl

theorem cell22_2670788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2670788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670788 prefixEnd_2670788 := by exact prefixLift 2670788
  have htrace : WordTrace (prefixWord ++ tailWord_2670788) baseStart_2670788 baseEnd_2670788 := by
    simpa [prefixWord, tailWord_2670788, baseEnd_2670788] using wordTrace_append hprefix tailTrace_2670788
  have hstable : (prefixWord ++ tailWord_2670788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670788).length < 2 ^ (prefixWord ++ tailWord_2670788).sum := by decide
  have hdescent : baseEnd_2670788 < baseStart_2670788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670801 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 6]
def baseStart_2670801 : Nat := 118140960795 + 2670801 * 2 ^ 59
def prefixEnd_2670801 : Nat := 4983230072969 + 3 ^ 40 * 2670801 * 2
def baseEnd_2670801 : Nat := 304756587890868936112159

theorem tailTrace_2670801 : CollatzResearch.WordTrace tailWord_2670801 prefixEnd_2670801 304756587890868936112159 := by
  unfold tailWord_2670801
  simp only [CollatzResearch.WordTrace]
  refine ⟨97412115197151588341028257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64941410131434392227352171 97412115197151588341028257)
  ·
    refine ⟨73059086397863691255771193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97412115197151588341028257 73059086397863691255771193)
    ·
      refine ⟨54794314798397768441828395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73059086397863691255771193 54794314798397768441828395)
      ·
        refine ⟨82191472197596652662742593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54794314798397768441828395 82191472197596652662742593)
        ·
          refine ⟨61643604148197489497056945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82191472197596652662742593 61643604148197489497056945)
          ·
            refine ⟨46232703111148117122792709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61643604148197489497056945 46232703111148117122792709)
            ·
              refine ⟨8668631833340271960523633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46232703111148117122792709 8668631833340271960523633)
              ·
                refine ⟨6501473875005203970392725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8668631833340271960523633 6501473875005203970392725)
                ·
                  refine ⟨304756587890868936112159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6501473875005203970392725 304756587890868936112159)
                  ·
                    rfl

theorem cell22_2670801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_2670801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670801 prefixEnd_2670801 := by exact prefixLift 2670801
  have htrace : WordTrace (prefixWord ++ tailWord_2670801) baseStart_2670801 baseEnd_2670801 := by
    simpa [prefixWord, tailWord_2670801, baseEnd_2670801] using wordTrace_append hprefix tailTrace_2670801
  have hstable : (prefixWord ++ tailWord_2670801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670801).length < 2 ^ (prefixWord ++ tailWord_2670801).sum := by decide
  have hdescent : baseEnd_2670801 < baseStart_2670801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670816 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_2670816 : Nat := 118140960795 + 2670816 * 2 ^ 59
def prefixEnd_2670816 : Nat := 4983230072969 + 3 ^ 40 * 2670816 * 2
def baseEnd_2670816 : Nat := 914274898479151769211431

theorem tailTrace_2670816 : CollatzResearch.WordTrace tailWord_2670816 prefixEnd_2670816 914274898479151769211431 := by
  unfold tailWord_2670816
  simp only [CollatzResearch.WordTrace]
  refine ⟨48706331146048622951412151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64941774861398163935216201 48706331146048622951412151)
  ·
    refine ⟨73059496719072934427118227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48706331146048622951412151 73059496719072934427118227)
    ·
      refine ⟨109589245078609401640677341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73059496719072934427118227 109589245078609401640677341)
      ·
        refine ⟨41095966904478525615254003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109589245078609401640677341 41095966904478525615254003)
        ·
          refine ⟨61643950356717788422881005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41095966904478525615254003 61643950356717788422881005)
          ·
            refine ⟨23116481383769170658580377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61643950356717788422881005 23116481383769170658580377)
            ·
              refine ⟨17337361037826877993935283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23116481383769170658580377 17337361037826877993935283)
              ·
                refine ⟨26006041556740316990902925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17337361037826877993935283 26006041556740316990902925)
                ·
                  refine ⟨9752265583777618871588597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26006041556740316990902925 9752265583777618871588597)
                  ·
                    refine ⟨914274898479151769211431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9752265583777618871588597 914274898479151769211431)
                    ·
                      rfl

theorem cell22_2670816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_2670816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670816 prefixEnd_2670816 := by exact prefixLift 2670816
  have htrace : WordTrace (prefixWord ++ tailWord_2670816) baseStart_2670816 baseEnd_2670816 := by
    simpa [prefixWord, tailWord_2670816, baseEnd_2670816] using wordTrace_append hprefix tailTrace_2670816
  have hstable : (prefixWord ++ tailWord_2670816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670816).length < 2 ^ (prefixWord ++ tailWord_2670816).sum := by decide
  have hdescent : baseEnd_2670816 < baseStart_2670816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670833 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_2670833 : Nat := 118140960795 + 2670833 * 2 ^ 59
def prefixEnd_2670833 : Nat := 4983230072969 + 3 ^ 40 * 2670833 * 2
def baseEnd_2670833 : Nat := 914280717926569391536379

theorem tailTrace_2670833 : CollatzResearch.WordTrace tailWord_2670833 prefixEnd_2670833 914280717926569391536379 := by
  unfold tailWord_2670833
  simp only [CollatzResearch.WordTrace]
  refine ⟨97413282333035657806193153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64942188222023771870795435 97413282333035657806193153)
  ·
    refine ⟨73059961749776743354644865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97413282333035657806193153 73059961749776743354644865)
    ·
      refine ⟨54794971312332557515983649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73059961749776743354644865 54794971312332557515983649)
      ·
        refine ⟨41096228484249418136987737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54794971312332557515983649 41096228484249418136987737)
        ·
          refine ⟨30822171363187063602740803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41096228484249418136987737 30822171363187063602740803)
          ·
            refine ⟨46233257044780595404111205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30822171363187063602740803 46233257044780595404111205)
            ·
              refine ⟨8668735695896361638270851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46233257044780595404111205 8668735695896361638270851)
              ·
                refine ⟨13003103543844542457406277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668735695896361638270851 13003103543844542457406277)
                ·
                  refine ⟨2438081914470851710763677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13003103543844542457406277 2438081914470851710763677)
                  ·
                    refine ⟨914280717926569391536379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438081914470851710763677 914280717926569391536379)
                    ·
                      rfl

theorem cell22_2670833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_2670833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670833 prefixEnd_2670833 := by exact prefixLift 2670833
  have htrace : WordTrace (prefixWord ++ tailWord_2670833) baseStart_2670833 baseEnd_2670833 := by
    simpa [prefixWord, tailWord_2670833, baseEnd_2670833] using wordTrace_append hprefix tailTrace_2670833
  have hstable : (prefixWord ++ tailWord_2670833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670833).length < 2 ^ (prefixWord ++ tailWord_2670833).sum := by decide
  have hdescent : baseEnd_2670833 < baseStart_2670833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670835 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 4]
def baseStart_2670835 : Nat := 118140960795 + 2670835 * 2 ^ 59
def prefixEnd_2670835 : Nat := 4983230072969 + 3 ^ 40 * 2670835 * 2
def baseEnd_2670835 : Nat := 304760467522480684328791

theorem tailTrace_2670835 : CollatzResearch.WordTrace tailWord_2670835 prefixEnd_2670835 304760467522480684328791 := by
  unfold tailWord_2670835
  simp only [CollatzResearch.WordTrace]
  refine ⟨97413355279028412147765959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64942236852685608098510639 97413355279028412147765959)
  ·
    refine ⟨146120032918542618221648939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97413355279028412147765959 146120032918542618221648939)
    ·
      refine ⟨219180049377813927332473409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146120032918542618221648939 219180049377813927332473409)
      ·
        refine ⟨164385037033360445499355057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219180049377813927332473409 164385037033360445499355057)
        ·
          refine ⟨123288777775020334124516293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164385037033360445499355057 123288777775020334124516293)
          ·
            refine ⟨23116645832816312648346805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123288777775020334124516293 23116645832816312648346805)
            ·
              refine ⟨2167185546826529310782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23116645832816312648346805 2167185546826529310782513)
              ·
                refine ⟨1625389160119896983086885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167185546826529310782513 1625389160119896983086885)
                ·
                  refine ⟨304760467522480684328791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625389160119896983086885 304760467522480684328791)
                  ·
                    rfl

theorem cell22_2670835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 4].length) (baseStart_2670835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670835 prefixEnd_2670835 := by exact prefixLift 2670835
  have htrace : WordTrace (prefixWord ++ tailWord_2670835) baseStart_2670835 baseEnd_2670835 := by
    simpa [prefixWord, tailWord_2670835, baseEnd_2670835] using wordTrace_append hprefix tailTrace_2670835
  have hstable : (prefixWord ++ tailWord_2670835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670835).length < 2 ^ (prefixWord ++ tailWord_2670835).sum := by decide
  have hdescent : baseEnd_2670835 < baseStart_2670835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670908 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_2670908 : Nat := 118140960795 + 2670908 * 2 ^ 59
def prefixEnd_2670908 : Nat := 4983230072969 + 3 ^ 40 * 2670908 * 2
def baseEnd_2670908 : Nat := 304768797319764731970383

theorem tailTrace_2670908 : CollatzResearch.WordTrace tailWord_2670908 prefixEnd_2670908 304768797319764731970383 := by
  unfold tailWord_2670908
  simp only [CollatzResearch.WordTrace]
  refine ⟨48708008903881972807586689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64944011871842630410115585 48708008903881972807586689)
  ·
    refine ⟨36531006677911479605690017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48708008903881972807586689 36531006677911479605690017)
    ·
      refine ⟨27398255008433609704267513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36531006677911479605690017 27398255008433609704267513)
      ·
        refine ⟨20548691256325207278200635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27398255008433609704267513 20548691256325207278200635)
        ·
          refine ⟨30823036884487810917300953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20548691256325207278200635 30823036884487810917300953)
          ·
            refine ⟨23117277663365858187975715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30823036884487810917300953 23117277663365858187975715)
            ·
              refine ⟨34675916495048787281963573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23117277663365858187975715 34675916495048787281963573)
              ·
                refine ⟨3250867171410823807684085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34675916495048787281963573 3250867171410823807684085)
                ·
                  refine ⟨304768797319764731970383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3250867171410823807684085 304768797319764731970383)
                  ·
                    rfl

theorem cell22_2670908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_2670908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670908 prefixEnd_2670908 := by exact prefixLift 2670908
  have htrace : WordTrace (prefixWord ++ tailWord_2670908) baseStart_2670908 baseEnd_2670908 := by
    simpa [prefixWord, tailWord_2670908, baseEnd_2670908] using wordTrace_append hprefix tailTrace_2670908
  have hstable : (prefixWord ++ tailWord_2670908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670908).length < 2 ^ (prefixWord ++ tailWord_2670908).sum := by decide
  have hdescent : baseEnd_2670908 < baseStart_2670908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670953 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 6]
def baseStart_2670953 : Nat := 118140960795 + 2670953 * 2 ^ 59
def prefixEnd_2670953 : Nat := 4983230072969 + 3 ^ 40 * 2670953 * 2
def baseEnd_2670953 : Nat := 304773932126309692845337

theorem tailTrace_2670953 : CollatzResearch.WordTrace tailWord_2670953 prefixEnd_2670953 304773932126309692845337 := by
  unfold tailWord_2670953
  simp only [CollatzResearch.WordTrace]
  refine ⟨97417659092600918300561513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64945106061733945533707675 97417659092600918300561513)
  ·
    refine ⟨73063244319450688725421135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97417659092600918300561513 73063244319450688725421135)
    ·
      refine ⟨109594866479176033088131703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73063244319450688725421135 109594866479176033088131703)
      ·
        refine ⟨164392299718764049632197555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109594866479176033088131703 164392299718764049632197555)
        ·
          refine ⟨246588449578146074448296333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164392299718764049632197555 246588449578146074448296333)
          ·
            refine ⟨92470668591804777918111125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246588449578146074448296333 92470668591804777918111125)
            ·
              refine ⟨4334562590240848964911459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92470668591804777918111125 4334562590240848964911459)
              ·
                refine ⟨6501843885361273447367189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334562590240848964911459 6501843885361273447367189)
                ·
                  refine ⟨304773932126309692845337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6501843885361273447367189 304773932126309692845337)
                  ·
                    rfl

theorem cell22_2670953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_2670953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670953 prefixEnd_2670953 := by exact prefixLift 2670953
  have htrace : WordTrace (prefixWord ++ tailWord_2670953) baseStart_2670953 baseEnd_2670953 := by
    simpa [prefixWord, tailWord_2670953, baseEnd_2670953] using wordTrace_append hprefix tailTrace_2670953
  have hstable : (prefixWord ++ tailWord_2670953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670953).length < 2 ^ (prefixWord ++ tailWord_2670953).sum := by decide
  have hdescent : baseEnd_2670953 < baseStart_2670953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670983 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2670983 : Nat := 118140960795 + 2670983 * 2 ^ 59
def prefixEnd_2670983 : Nat := 4983230072969 + 3 ^ 40 * 2670983 * 2
def baseEnd_2670983 : Nat := 914332065992019000285919

theorem tailTrace_2670983 : CollatzResearch.WordTrace tailWord_2670983 prefixEnd_2670983 914332065992019000285919 := by
  unfold tailWord_2670983
  simp only [CollatzResearch.WordTrace]
  refine ⟨97418753282492233424153603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64945835521661488949435735 97418753282492233424153603)
  ·
    refine ⟨146128129923738350136230405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97418753282492233424153603 146128129923738350136230405)
    ·
      refine ⟨27399024360700940650543201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146128129923738350136230405 27399024360700940650543201)
      ·
        refine ⟨20549268270525705487907401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27399024360700940650543201 20549268270525705487907401)
        ·
          refine ⟨15411951202894279115930551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20549268270525705487907401 15411951202894279115930551)
          ·
            refine ⟨23117926804341418673895827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15411951202894279115930551 23117926804341418673895827)
            ·
              refine ⟨34676890206512128010843741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23117926804341418673895827 34676890206512128010843741)
              ·
                refine ⟨13003833827442048004066403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34676890206512128010843741 13003833827442048004066403)
                ·
                  refine ⟨19505750741163072006099605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13003833827442048004066403 19505750741163072006099605)
                  ·
                    refine ⟨914332065992019000285919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19505750741163072006099605 914332065992019000285919)
                    ·
                      rfl

theorem cell22_2670983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2670983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670983 prefixEnd_2670983 := by exact prefixLift 2670983
  have htrace : WordTrace (prefixWord ++ tailWord_2670983) baseStart_2670983 baseEnd_2670983 := by
    simpa [prefixWord, tailWord_2670983, baseEnd_2670983] using wordTrace_append hprefix tailTrace_2670983
  have hstable : (prefixWord ++ tailWord_2670983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670983).length < 2 ^ (prefixWord ++ tailWord_2670983).sum := by decide
  have hdescent : baseEnd_2670983 < baseStart_2670983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670985 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_2670985 : Nat := 118140960795 + 2670985 * 2 ^ 59
def prefixEnd_2670985 : Nat := 4983230072969 + 3 ^ 40 * 2670985 * 2
def baseEnd_2670985 : Nat := 914332750632891661735913

theorem tailTrace_2670985 : CollatzResearch.WordTrace tailWord_2670985 prefixEnd_2670985 914332750632891661735913 := by
  unfold tailWord_2670985
  simp only [CollatzResearch.WordTrace]
  refine ⟨97418826228484987765726409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64945884152323325177150939 97418826228484987765726409)
  ·
    refine ⟨73064119671363740824294807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97418826228484987765726409 73064119671363740824294807)
    ·
      refine ⟨109596179507045611236442211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73064119671363740824294807 109596179507045611236442211)
      ·
        refine ⟨164394269260568416854663317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109596179507045611236442211 164394269260568416854663317)
        ·
          refine ⟨7705981371589144540062343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164394269260568416854663317 7705981371589144540062343)
          ·
            refine ⟨11558972057383716810093515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705981371589144540062343 11558972057383716810093515)
            ·
              refine ⟨17338458086075575215140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11558972057383716810093515 17338458086075575215140273)
              ·
                refine ⟨13003843564556681411355205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17338458086075575215140273 13003843564556681411355205)
                ·
                  refine ⟨2438220668354377764629101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13003843564556681411355205 2438220668354377764629101)
                  ·
                    refine ⟨914332750632891661735913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438220668354377764629101 914332750632891661735913)
                    ·
                      rfl

theorem cell22_2670985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_2670985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670985 prefixEnd_2670985 := by exact prefixLift 2670985
  have htrace : WordTrace (prefixWord ++ tailWord_2670985) baseStart_2670985 baseEnd_2670985 := by
    simpa [prefixWord, tailWord_2670985, baseEnd_2670985] using wordTrace_append hprefix tailTrace_2670985
  have hstable : (prefixWord ++ tailWord_2670985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670985).length < 2 ^ (prefixWord ++ tailWord_2670985).sum := by decide
  have hdescent : baseEnd_2670985 < baseStart_2670985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670987 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 4]
def baseStart_2670987 : Nat := 118140960795 + 2670987 * 2 ^ 59
def prefixEnd_2670987 : Nat := 4983230072969 + 3 ^ 40 * 2670987 * 2
def baseEnd_2670987 : Nat := 304777811757921441061969

theorem tailTrace_2670987 : CollatzResearch.WordTrace tailWord_2670987 prefixEnd_2670987 304777811757921441061969 := by
  unfold tailWord_2670987
  simp only [CollatzResearch.WordTrace]
  refine ⟨97418899174477742107299215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64945932782985161404866143 97418899174477742107299215)
  ·
    refine ⟨146128348761716613160948823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97418899174477742107299215 146128348761716613160948823)
    ·
      refine ⟨219192523142574919741423235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146128348761716613160948823 219192523142574919741423235)
      ·
        refine ⟨328788784713862379612134853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219192523142574919741423235 328788784713862379612134853)
        ·
          refine ⟨61647897133849196177275285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328788784713862379612134853 61647897133849196177275285)
          ·
            refine ⟨2889745178149181070809779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61647897133849196177275285 2889745178149181070809779)
            ·
              refine ⟨4334617767223771606214669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889745178149181070809779 4334617767223771606214669)
              ·
                refine ⟨1625481662708914352330501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4334617767223771606214669 1625481662708914352330501)
                ·
                  refine ⟨304777811757921441061969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625481662708914352330501 304777811757921441061969)
                  ·
                    rfl

theorem cell22_2670987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 4].length) (baseStart_2670987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2670987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2670987 prefixEnd_2670987 := by exact prefixLift 2670987
  have htrace : WordTrace (prefixWord ++ tailWord_2670987) baseStart_2670987 baseEnd_2670987 := by
    simpa [prefixWord, tailWord_2670987, baseEnd_2670987] using wordTrace_append hprefix tailTrace_2670987
  have hstable : (prefixWord ++ tailWord_2670987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670987).length < 2 ^ (prefixWord ++ tailWord_2670987).sum := by decide
  have hdescent : baseEnd_2670987 < baseStart_2670987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671000 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_2671000 : Nat := 118140960795 + 2671000 * 2 ^ 59
def prefixEnd_2671000 : Nat := 4983230072969 + 3 ^ 40 * 2671000 * 2
def baseEnd_2671000 : Nat := 914337885439436622610867

theorem tailTrace_2671000 : CollatzResearch.WordTrace tailWord_2671000 prefixEnd_2671000 914337885439436622610867 := by
  unfold tailWord_2671000
  simp only [CollatzResearch.WordTrace]
  refine ⟨48709686661715322663761227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64946248882287096885014969 48709686661715322663761227)
  ·
    refine ⟨73064529992572983995641841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48709686661715322663761227 73064529992572983995641841)
    ·
      refine ⟨54798397494429737996731381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73064529992572983995641841 54798397494429737996731381)
      ·
        refine ⟨5137349765102787937193567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54798397494429737996731381 5137349765102787937193567)
        ·
          refine ⟨7706024647654181905790351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137349765102787937193567 7706024647654181905790351)
          ·
            refine ⟨11559036971481272858685527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7706024647654181905790351 11559036971481272858685527)
            ·
              refine ⟨17338555457221909288028291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11559036971481272858685527 17338555457221909288028291)
              ·
                refine ⟨26007833185832863932042437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17338555457221909288028291 26007833185832863932042437)
                ·
                  refine ⟨4876468722343661987257957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26007833185832863932042437 4876468722343661987257957)
                  ·
                    refine ⟨914337885439436622610867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4876468722343661987257957 914337885439436622610867)
                    ·
                      rfl

theorem cell22_2671000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_2671000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671000 prefixEnd_2671000 := by exact prefixLift 2671000
  have htrace : WordTrace (prefixWord ++ tailWord_2671000) baseStart_2671000 baseEnd_2671000 := by
    simpa [prefixWord, tailWord_2671000, baseEnd_2671000] using wordTrace_append hprefix tailTrace_2671000
  have hstable : (prefixWord ++ tailWord_2671000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671000).length < 2 ^ (prefixWord ++ tailWord_2671000).sum := by decide
  have hdescent : baseEnd_2671000 < baseStart_2671000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671015 : List Nat := [1, 1, 6, 1, 1, 3, 2, 7]
def baseStart_2671015 : Nat := 118140960795 + 2671015 * 2 ^ 59
def prefixEnd_2671015 : Nat := 4983230072969 + 3 ^ 40 * 2671015 * 2
def baseEnd_2671015 : Nat := 101593668916220175942869

theorem tailTrace_2671015 : CollatzResearch.WordTrace tailWord_2671015 prefixEnd_2671015 101593668916220175942869 := by
  unfold tailWord_2671015
  simp only [CollatzResearch.WordTrace]
  refine ⟨97419920418376302889318499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64946613612250868592878999 97419920418376302889318499)
  ·
    refine ⟨146129880627564454333977749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97419920418376302889318499 146129880627564454333977749)
    ·
      refine ⟨6849838154417083796905207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146129880627564454333977749 6849838154417083796905207)
      ·
        refine ⟨10274757231625625695357811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6849838154417083796905207 10274757231625625695357811)
        ·
          refine ⟨15412135847438438543036717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10274757231625625695357811 15412135847438438543036717)
          ·
            refine ⟨5779550942789414453638769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15412135847438438543036717 5779550942789414453638769)
            ·
              refine ⟨4334663207092060840229077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5779550942789414453638769 4334663207092060840229077)
              ·
                refine ⟨101593668916220175942869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4334663207092060840229077 101593668916220175942869)
                ·
                  rfl

theorem cell22_2671015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 7].length) (baseStart_2671015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671015 prefixEnd_2671015 := by exact prefixLift 2671015
  have htrace : WordTrace (prefixWord ++ tailWord_2671015) baseStart_2671015 baseEnd_2671015 := by
    simpa [prefixWord, tailWord_2671015, baseEnd_2671015] using wordTrace_append hprefix tailTrace_2671015
  have hstable : (prefixWord ++ tailWord_2671015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671015).length < 2 ^ (prefixWord ++ tailWord_2671015).sum := by decide
  have hdescent : baseEnd_2671015 < baseStart_2671015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671180 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2671180 : Nat := 118140960795 + 2671180 * 2 ^ 59
def prefixEnd_2671180 : Nat := 4983230072969 + 3 ^ 40 * 2671180 * 2
def baseEnd_2671180 : Nat := 914399503117976153110315

theorem tailTrace_2671180 : CollatzResearch.WordTrace tailWord_2671180 prefixEnd_2671180 914399503117976153110315 := by
  unfold tailWord_2671180
  simp only [CollatzResearch.WordTrace]
  refine ⟨48712969231389268034537497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64950625641852357379383329 48712969231389268034537497)
  ·
    refine ⟨36534726923541951025903123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48712969231389268034537497 36534726923541951025903123)
    ·
      refine ⟨54802090385312926538854685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36534726923541951025903123 54802090385312926538854685)
      ·
        refine ⟨20550783894492347452070507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54802090385312926538854685 20550783894492347452070507)
        ·
          refine ⟨30826175841738521178105761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20550783894492347452070507 30826175841738521178105761)
          ·
            refine ⟨23119631881303890883579321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30826175841738521178105761 23119631881303890883579321)
            ·
              refine ⟨17339723910977918162684491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23119631881303890883579321 17339723910977918162684491)
              ·
                refine ⟨26009585866466877244026737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17339723910977918162684491 26009585866466877244026737)
                ·
                  refine ⟨19507189399850157933020053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26009585866466877244026737 19507189399850157933020053)
                  ·
                    refine ⟨914399503117976153110315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19507189399850157933020053 914399503117976153110315)
                    ·
                      rfl

theorem cell22_2671180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2671180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671180 prefixEnd_2671180 := by exact prefixLift 2671180
  have htrace : WordTrace (prefixWord ++ tailWord_2671180) baseStart_2671180 baseEnd_2671180 := by
    simpa [prefixWord, tailWord_2671180, baseEnd_2671180] using wordTrace_append hprefix tailTrace_2671180
  have hstable : (prefixWord ++ tailWord_2671180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671180).length < 2 ^ (prefixWord ++ tailWord_2671180).sum := by decide
  have hdescent : baseEnd_2671180 < baseStart_2671180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671229 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 5]
def baseStart_2671229 : Nat := 118140960795 + 2671229 * 2 ^ 59
def prefixEnd_2671229 : Nat := 4983230072969 + 3 ^ 40 * 2671229 * 2
def baseEnd_2671229 : Nat := 304805425606452119545055

theorem tailTrace_2671229 : CollatzResearch.WordTrace tailWord_2671229 prefixEnd_2671229 304805425606452119545055 := by
  unfold tailWord_2671229
  simp only [CollatzResearch.WordTrace]
  refine ⟨97427725639601017437608741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64951817093067344958405827 97427725639601017437608741)
  ·
    refine ⟨18267698557425190769551639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97427725639601017437608741 18267698557425190769551639)
    ·
      refine ⟨27401547836137786154327459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18267698557425190769551639 27401547836137786154327459)
      ·
        refine ⟨41102321754206679231491189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27401547836137786154327459 41102321754206679231491189)
        ·
          refine ⟨3853342664456876177952299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41102321754206679231491189 3853342664456876177952299)
          ·
            refine ⟨5780013996685314266928449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853342664456876177952299 5780013996685314266928449)
            ·
              refine ⟨4335010497513985700196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5780013996685314266928449 4335010497513985700196337)
              ·
                refine ⟨3251257873135489275147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4335010497513985700196337 3251257873135489275147253)
                ·
                  refine ⟨304805425606452119545055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251257873135489275147253 304805425606452119545055)
                  ·
                    rfl

theorem cell22_2671229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_2671229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671229 prefixEnd_2671229 := by exact prefixLift 2671229
  have htrace : WordTrace (prefixWord ++ tailWord_2671229) baseStart_2671229 baseEnd_2671229 := by
    simpa [prefixWord, tailWord_2671229, baseEnd_2671229] using wordTrace_append hprefix tailTrace_2671229
  have hstable : (prefixWord ++ tailWord_2671229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671229).length < 2 ^ (prefixWord ++ tailWord_2671229).sum := by decide
  have hdescent : baseEnd_2671229 < baseStart_2671229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671319 : List Nat := [1, 1, 3, 2, 1, 6, 2, 6]
def baseStart_2671319 : Nat := 118140960795 + 2671319 * 2 ^ 59
def prefixEnd_2671319 : Nat := 4983230072969 + 3 ^ 40 * 2671319 * 2
def baseEnd_2671319 : Nat := 101605231739847347098321

theorem tailTrace_2671319 : CollatzResearch.WordTrace tailWord_2671319 prefixEnd_2671319 101605231739847347098321 := by
  unfold tailWord_2671319
  simp only [CollatzResearch.WordTrace]
  refine ⟨97431008209274962808385011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64954005472849975205590007 97431008209274962808385011)
  ·
    refine ⟨146146512313912444212577517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97431008209274962808385011 146146512313912444212577517)
    ·
      refine ⟨54804942117717166579716569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146146512313912444212577517 54804942117717166579716569)
      ·
        refine ⟨41103706588287874934787427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54804942117717166579716569 41103706588287874934787427)
        ·
          refine ⟨61655559882431812402181141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41103706588287874934787427 61655559882431812402181141)
          ·
            refine ⟨2890104369488991206352241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61655559882431812402181141 2890104369488991206352241)
            ·
              refine ⟨2167578277116743404764181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2890104369488991206352241 2167578277116743404764181)
              ·
                refine ⟨101605231739847347098321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2167578277116743404764181 101605231739847347098321)
                ·
                  rfl

theorem cell22_2671319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 6].length) (baseStart_2671319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671319 prefixEnd_2671319 := by exact prefixLift 2671319
  have htrace : WordTrace (prefixWord ++ tailWord_2671319) baseStart_2671319 baseEnd_2671319 := by
    simpa [prefixWord, tailWord_2671319, baseEnd_2671319] using wordTrace_append hprefix tailTrace_2671319
  have hstable : (prefixWord ++ tailWord_2671319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671319).length < 2 ^ (prefixWord ++ tailWord_2671319).sum := by decide
  have hdescent : baseEnd_2671319 < baseStart_2671319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671347 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 5]
def baseStart_2671347 : Nat := 118140960795 + 2671347 * 2 ^ 59
def prefixEnd_2671347 : Nat := 4983230072969 + 3 ^ 40 * 2671347 * 2
def baseEnd_2671347 : Nat := 304818890210281128061601

theorem tailTrace_2671347 : CollatzResearch.WordTrace tailWord_2671347 prefixEnd_2671347 304818890210281128061601 := by
  unfold tailWord_2671347
  simp only [CollatzResearch.WordTrace]
  refine ⟨97432029453173523590404295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64954686302115682393602863 97432029453173523590404295)
  ·
    refine ⟨146148044179760285385606443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97432029453173523590404295 146148044179760285385606443)
    ·
      refine ⟨219222066269640428078409665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146148044179760285385606443 219222066269640428078409665)
      ·
        refine ⟨164416549702230321058807249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219222066269640428078409665 164416549702230321058807249)
        ·
          refine ⟨123312412276672740794105437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164416549702230321058807249 123312412276672740794105437)
          ·
            refine ⟨46242154603752277797789539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123312412276672740794105437 46242154603752277797789539)
            ·
              refine ⟨69363231905628416696684309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46242154603752277797789539 69363231905628416696684309)
              ·
                refine ⟨3251401495576332032657077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69363231905628416696684309 3251401495576332032657077)
                ·
                  refine ⟨304818890210281128061601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251401495576332032657077 304818890210281128061601)
                  ·
                    rfl

theorem cell22_2671347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 5].length) (baseStart_2671347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671347 prefixEnd_2671347 := by exact prefixLift 2671347
  have htrace : WordTrace (prefixWord ++ tailWord_2671347) baseStart_2671347 baseEnd_2671347 := by
    simpa [prefixWord, tailWord_2671347, baseEnd_2671347] using wordTrace_append hprefix tailTrace_2671347
  have hstable : (prefixWord ++ tailWord_2671347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671347).length < 2 ^ (prefixWord ++ tailWord_2671347).sum := by decide
  have hdescent : baseEnd_2671347 < baseStart_2671347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671364 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2671364 : Nat := 118140960795 + 2671364 * 2 ^ 59
def prefixEnd_2671364 : Nat := 4983230072969 + 3 ^ 40 * 2671364 * 2
def baseEnd_2671364 : Nat := 304820830026087002169917

theorem tailTrace_2671364 : CollatzResearch.WordTrace tailWord_2671364 prefixEnd_2671364 304820830026087002169917 := by
  unfold tailWord_2671364
  simp only [CollatzResearch.WordTrace]
  refine ⟨48716324747055967746886573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64955099662741290329182097 48716324747055967746886573)
  ·
    refine ⟨18268621780145987905082465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48716324747055967746886573 18268621780145987905082465)
    ·
      refine ⟨13701466335109490928811849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18268621780145987905082465 13701466335109490928811849)
      ·
        refine ⟨10276099751332118196608887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13701466335109490928811849 10276099751332118196608887)
        ·
          refine ⟨15414149626998177294913331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10276099751332118196608887 15414149626998177294913331)
          ·
            refine ⟨23121224440497265942369997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15414149626998177294913331 23121224440497265942369997)
            ·
              refine ⟨8670459165186474728388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23121224440497265942369997 8670459165186474728388749)
              ·
                refine ⟨3251422186944928023145781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8670459165186474728388749 3251422186944928023145781)
                ·
                  refine ⟨304820830026087002169917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251422186944928023145781 304820830026087002169917)
                  ·
                    rfl

theorem cell22_2671364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2671364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671364 prefixEnd_2671364 := by exact prefixLift 2671364
  have htrace : WordTrace (prefixWord ++ tailWord_2671364) baseStart_2671364 baseEnd_2671364 := by
    simpa [prefixWord, tailWord_2671364, baseEnd_2671364] using wordTrace_append hprefix tailTrace_2671364
  have hstable : (prefixWord ++ tailWord_2671364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671364).length < 2 ^ (prefixWord ++ tailWord_2671364).sum := by decide
  have hdescent : baseEnd_2671364 < baseStart_2671364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671458 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2671458 : Nat := 118140960795 + 2671458 * 2 ^ 59
def prefixEnd_2671458 : Nat := 4983230072969 + 3 ^ 40 * 2671458 * 2
def baseEnd_2671458 : Nat := 914494668199276094659463

theorem tailTrace_2671458 : CollatzResearch.WordTrace tailWord_2671458 prefixEnd_2671458 914494668199276094659463 := by
  unfold tailWord_2671458
  simp only [CollatzResearch.WordTrace]
  refine ⟨24359019488942847386923757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64957385303847593031796685 24359019488942847386923757)
  ·
    refine ⟨9134632308353567770096409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24359019488942847386923757 9134632308353567770096409)
    ·
      refine ⟨6850974231265175827572307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9134632308353567770096409 6850974231265175827572307)
      ·
        refine ⟨10276461346897763741358461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850974231265175827572307 10276461346897763741358461)
        ·
          refine ⟨3853673005086661403009423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10276461346897763741358461 3853673005086661403009423)
          ·
            refine ⟨5780509507629992104514135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853673005086661403009423 5780509507629992104514135)
            ·
              refine ⟨8670764261444988156771203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5780509507629992104514135 8670764261444988156771203)
              ·
                refine ⟨13006146392167482235156805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670764261444988156771203 13006146392167482235156805)
                ·
                  refine ⟨2438652448531402919091901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13006146392167482235156805 2438652448531402919091901)
                  ·
                    refine ⟨914494668199276094659463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438652448531402919091901 914494668199276094659463)
                    ·
                      rfl

theorem cell22_2671458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2671458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671458 prefixEnd_2671458 := by exact prefixLift 2671458
  have htrace : WordTrace (prefixWord ++ tailWord_2671458) baseStart_2671458 baseEnd_2671458 := by
    simpa [prefixWord, tailWord_2671458, baseEnd_2671458] using wordTrace_append hprefix tailTrace_2671458
  have hstable : (prefixWord ++ tailWord_2671458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671458).length < 2 ^ (prefixWord ++ tailWord_2671458).sum := by decide
  have hdescent : baseEnd_2671458 < baseStart_2671458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671467 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_2671467 : Nat := 118140960795 + 2671467 * 2 ^ 59
def prefixEnd_2671467 : Nat := 4983230072969 + 3 ^ 40 * 2671467 * 2
def baseEnd_2671467 : Nat := 914497749083203071184435

theorem tailTrace_2671467 : CollatzResearch.WordTrace tailWord_2671467 prefixEnd_2671467 914497749083203071184435 := by
  unfold tailWord_2671467
  simp only [CollatzResearch.WordTrace]
  refine ⟨97436406212738784084772655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64957604141825856056515103 97436406212738784084772655)
  ·
    refine ⟨146154609319108176127158983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97436406212738784084772655 146154609319108176127158983)
    ·
      refine ⟨219231913978662264190738475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146154609319108176127158983 219231913978662264190738475)
      ·
        refine ⟨328847870967993396286107713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219231913978662264190738475 328847870967993396286107713)
        ·
          refine ⟨246635903225995047214580785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328847870967993396286107713 246635903225995047214580785)
          ·
            refine ⟨184976927419496285410935589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246635903225995047214580785 184976927419496285410935589)
            ·
              refine ⟨34683173891155553514550423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184976927419496285410935589 34683173891155553514550423)
              ·
                refine ⟨52024760836733330271825635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34683173891155553514550423 52024760836733330271825635)
                ·
                  refine ⟨78037141255099995407738453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52024760836733330271825635 78037141255099995407738453)
                  ·
                    refine ⟨914497749083203071184435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78037141255099995407738453 914497749083203071184435)
                    ·
                      rfl

theorem cell22_2671467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_2671467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671467 prefixEnd_2671467 := by exact prefixLift 2671467
  have htrace : WordTrace (prefixWord ++ tailWord_2671467) baseStart_2671467 baseEnd_2671467 := by
    simpa [prefixWord, tailWord_2671467, baseEnd_2671467] using wordTrace_append hprefix tailTrace_2671467
  have hstable : (prefixWord ++ tailWord_2671467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671467).length < 2 ^ (prefixWord ++ tailWord_2671467).sum := by decide
  have hdescent : baseEnd_2671467 < baseStart_2671467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671529 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_2671529 : Nat := 118140960795 + 2671529 * 2 ^ 59
def prefixEnd_2671529 : Nat := 4983230072969 + 3 ^ 40 * 2671529 * 2
def baseEnd_2671529 : Nat := 914518972950255576134245

theorem tailTrace_2671529 : CollatzResearch.WordTrace tailWord_2671529 prefixEnd_2671529 914518972950255576134245 := by
  unfold tailWord_2671529
  simp only [CollatzResearch.WordTrace]
  refine ⟨97438667538514168673529641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64959111692342779115686427 97438667538514168673529641)
  ·
    refine ⟨73079000653885626505147231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97438667538514168673529641 73079000653885626505147231)
    ·
      refine ⟨109618500980828439757720847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73079000653885626505147231 109618500980828439757720847)
      ·
        refine ⟨164427751471242659636581271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109618500980828439757720847 164427751471242659636581271)
        ·
          refine ⟨246641627206863989454871907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164427751471242659636581271 246641627206863989454871907)
          ·
            refine ⟨369962440810295984182307861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246641627206863989454871907 369962440810295984182307861)
            ·
              refine ⟨17341989412982624258545681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 369962440810295984182307861 17341989412982624258545681)
              ·
                refine ⟨13006492059736968193909261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17341989412982624258545681 13006492059736968193909261)
                ·
                  refine ⟨4877434522401363072715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13006492059736968193909261 4877434522401363072715973)
                  ·
                    refine ⟨914518972950255576134245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4877434522401363072715973 914518972950255576134245)
                    ·
                      rfl

theorem cell22_2671529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_2671529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671529 prefixEnd_2671529 := by exact prefixLift 2671529
  have htrace : WordTrace (prefixWord ++ tailWord_2671529) baseStart_2671529 baseEnd_2671529 := by
    simpa [prefixWord, tailWord_2671529, baseEnd_2671529] using wordTrace_append hprefix tailTrace_2671529
  have hstable : (prefixWord ++ tailWord_2671529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671529).length < 2 ^ (prefixWord ++ tailWord_2671529).sum := by decide
  have hdescent : baseEnd_2671529 < baseStart_2671529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671559 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2671559 : Nat := 118140960795 + 2671559 * 2 ^ 59
def prefixEnd_2671559 : Nat := 4983230072969 + 3 ^ 40 * 2671559 * 2
def baseEnd_2671559 : Nat := 914529242563345497884153

theorem tailTrace_2671559 : CollatzResearch.WordTrace tailWord_2671559 prefixEnd_2671559 914529242563345497884153 := by
  unfold tailWord_2671559
  simp only [CollatzResearch.WordTrace]
  refine ⟨97439761728405483797121731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64959841152270322531414487 97439761728405483797121731)
  ·
    refine ⟨146159642592608225695682597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97439761728405483797121731 146159642592608225695682597)
    ·
      refine ⟨27404932986114042317940487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146159642592608225695682597 27404932986114042317940487)
      ·
        refine ⟨41107399479171063476910731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27404932986114042317940487 41107399479171063476910731)
        ·
          refine ⟨61661099218756595215366097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41107399479171063476910731 61661099218756595215366097)
          ·
            refine ⟨46245824414067446411524573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61661099218756595215366097 46245824414067446411524573)
            ·
              refine ⟨17342184155275292404321715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46245824414067446411524573 17342184155275292404321715)
              ·
                refine ⟨26013276232912938606482573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17342184155275292404321715 26013276232912938606482573)
                ·
                  refine ⟨9754978587342351977430965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26013276232912938606482573 9754978587342351977430965)
                  ·
                    refine ⟨914529242563345497884153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9754978587342351977430965 914529242563345497884153)
                    ·
                      rfl

theorem cell22_2671559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2671559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671559 prefixEnd_2671559 := by exact prefixLift 2671559
  have htrace : WordTrace (prefixWord ++ tailWord_2671559) baseStart_2671559 baseEnd_2671559 := by
    simpa [prefixWord, tailWord_2671559, baseEnd_2671559] using wordTrace_append hprefix tailTrace_2671559
  have hstable : (prefixWord ++ tailWord_2671559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671559).length < 2 ^ (prefixWord ++ tailWord_2671559).sum := by decide
  have hdescent : baseEnd_2671559 < baseStart_2671559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671563 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 1, 4]
def baseStart_2671563 : Nat := 118140960795 + 2671563 * 2 ^ 59
def prefixEnd_2671563 : Nat := 4983230072969 + 3 ^ 40 * 2671563 * 2
def baseEnd_2671563 : Nat := 914530611845090820784141

theorem tailTrace_2671563 : CollatzResearch.WordTrace tailWord_2671563 prefixEnd_2671563 914530611845090820784141 := by
  unfold tailWord_2671563
  simp only [CollatzResearch.WordTrace]
  refine ⟨97439907620390992480267343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64959938413593994986844895 97439907620390992480267343)
  ·
    refine ⟨146159861430586488720401015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97439907620390992480267343 146159861430586488720401015)
    ·
      refine ⟨219239792145879733080601523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146159861430586488720401015 219239792145879733080601523)
      ·
        refine ⟨328859688218819599620902285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219239792145879733080601523 328859688218819599620902285)
        ·
          refine ⟨123322383082057349857838357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328859688218819599620902285 123322383082057349857838357)
          ·
            refine ⟨5780736706971438274586173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123322383082057349857838357 5780736706971438274586173)
            ·
              refine ⟨2167776265114289352969815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5780736706971438274586173 2167776265114289352969815)
              ·
                refine ⟨3251664397671434029454723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167776265114289352969815 3251664397671434029454723)
                ·
                  refine ⟨4877496596507151044182085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251664397671434029454723 4877496596507151044182085)
                  ·
                    refine ⟨914530611845090820784141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4877496596507151044182085 914530611845090820784141)
                    ·
                      rfl

theorem cell22_2671563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 4].length) (baseStart_2671563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671563 prefixEnd_2671563 := by exact prefixLift 2671563
  have htrace : WordTrace (prefixWord ++ tailWord_2671563) baseStart_2671563 baseEnd_2671563 := by
    simpa [prefixWord, tailWord_2671563, baseEnd_2671563] using wordTrace_append hprefix tailTrace_2671563
  have hstable : (prefixWord ++ tailWord_2671563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671563).length < 2 ^ (prefixWord ++ tailWord_2671563).sum := by decide
  have hdescent : baseEnd_2671563 < baseStart_2671563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671578 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_2671578 : Nat := 118140960795 + 2671578 * 2 ^ 59
def prefixEnd_2671578 : Nat := 4983230072969 + 3 ^ 40 * 2671578 * 2
def baseEnd_2671578 : Nat := 304845248883878593886365

theorem tailTrace_2671578 : CollatzResearch.WordTrace tailWord_2671578 prefixEnd_2671578 304845248883878593886365 := by
  unfold tailWord_2671578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24360113678834162510515847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64960303143557766694708925 24360113678834162510515847)
  ·
    refine ⟨36540170518251243765773771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24360113678834162510515847 36540170518251243765773771)
    ·
      refine ⟨54810255777376865648660657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36540170518251243765773771 54810255777376865648660657)
      ·
        refine ⟨41107691833032649236495493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54810255777376865648660657 41107691833032649236495493)
        ·
          refine ⟨7707692218693621731842905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41107691833032649236495493 7707692218693621731842905)
          ·
            refine ⟨5780769164020216298882179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7707692218693621731842905 5780769164020216298882179)
            ·
              refine ⟨8671153746030324448323269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5780769164020216298882179 8671153746030324448323269)
              ·
                refine ⟨1625841327380685834060613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8671153746030324448323269 1625841327380685834060613)
                ·
                  refine ⟨304845248883878593886365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625841327380685834060613 304845248883878593886365)
                  ·
                    rfl

theorem cell22_2671578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_2671578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671578 prefixEnd_2671578 := by exact prefixLift 2671578
  have htrace : WordTrace (prefixWord ++ tailWord_2671578) baseStart_2671578 baseEnd_2671578 := by
    simpa [prefixWord, tailWord_2671578, baseEnd_2671578] using wordTrace_append hprefix tailTrace_2671578
  have hstable : (prefixWord ++ tailWord_2671578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671578).length < 2 ^ (prefixWord ++ tailWord_2671578).sum := by decide
  have hdescent : baseEnd_2671578 < baseStart_2671578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671614 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2671614 : Nat := 118140960795 + 2671614 * 2 ^ 59
def prefixEnd_2671614 : Nat := 4983230072969 + 3 ^ 40 * 2671614 * 2
def baseEnd_2671614 : Nat := 914548070187343687758985

theorem tailTrace_2671614 : CollatzResearch.WordTrace tailWord_2671614 prefixEnd_2671614 914548070187343687758985 := by
  unfold tailWord_2671614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12180220967900778523796737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64961178495470818793582597 12180220967900778523796737)
  ·
    refine ⟨9135165725925583892847553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12180220967900778523796737 9135165725925583892847553)
    ·
      refine ⟨6851374294444187919635665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9135165725925583892847553 6851374294444187919635665)
      ·
        refine ⟨5138530720833140939726749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6851374294444187919635665 5138530720833140939726749)
        ·
          refine ⟨1926949020312427852397531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5138530720833140939726749 1926949020312427852397531)
          ·
            refine ⟨2890423530468641778596297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926949020312427852397531 2890423530468641778596297)
            ·
              refine ⟨2167817647851481333947223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2890423530468641778596297 2167817647851481333947223)
              ·
                refine ⟨3251726471777222000920835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167817647851481333947223 3251726471777222000920835)
                ·
                  refine ⟨4877589707665833001381253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251726471777222000920835 4877589707665833001381253)
                  ·
                    refine ⟨914548070187343687758985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4877589707665833001381253 914548070187343687758985)
                    ·
                      rfl

theorem cell22_2671614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2671614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671614 prefixEnd_2671614 := by exact prefixLift 2671614
  have htrace : WordTrace (prefixWord ++ tailWord_2671614) baseStart_2671614 baseEnd_2671614 := by
    simpa [prefixWord, tailWord_2671614, baseEnd_2671614] using wordTrace_append hprefix tailTrace_2671614
  have hstable : (prefixWord ++ tailWord_2671614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671614).length < 2 ^ (prefixWord ++ tailWord_2671614).sum := by decide
  have hdescent : baseEnd_2671614 < baseStart_2671614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671621 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2671621 : Nat := 118140960795 + 2671621 * 2 ^ 59
def prefixEnd_2671621 : Nat := 4983230072969 + 3 ^ 40 * 2671621 * 2
def baseEnd_2671621 : Nat := 914550466430398002833963

theorem tailTrace_2671621 : CollatzResearch.WordTrace tailWord_2671621 prefixEnd_2671621 914550466430398002833963 := by
  unfold tailWord_2671621
  simp only [CollatzResearch.WordTrace]
  refine ⟨97442023054180868385878717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64961348702787245590585811 97442023054180868385878717)
  ·
    refine ⟨36540758645317825644704519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97442023054180868385878717 36540758645317825644704519)
    ·
      refine ⟨54811137967976738467056779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36540758645317825644704519 54811137967976738467056779)
      ·
        refine ⟨82216706951965107700585169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54811137967976738467056779 82216706951965107700585169)
        ·
          refine ⟨61662530213973830775438877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82216706951965107700585169 61662530213973830775438877)
          ·
            refine ⟨23123448830240186540789579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61662530213973830775438877 23123448830240186540789579)
            ·
              refine ⟨34685173245360279811184369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23123448830240186540789579 34685173245360279811184369)
              ·
                refine ⟨26013879934020209858388277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34685173245360279811184369 26013879934020209858388277)
                ·
                  refine ⟨2438801243814394674223901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26013879934020209858388277 2438801243814394674223901)
                  ·
                    refine ⟨914550466430398002833963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438801243814394674223901 914550466430398002833963)
                    ·
                      rfl

theorem cell22_2671621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2671621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671621 prefixEnd_2671621 := by exact prefixLift 2671621
  have htrace : WordTrace (prefixWord ++ tailWord_2671621) baseStart_2671621 baseEnd_2671621 := by
    simpa [prefixWord, tailWord_2671621, baseEnd_2671621] using wordTrace_append hprefix tailTrace_2671621
  have hstable : (prefixWord ++ tailWord_2671621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671621).length < 2 ^ (prefixWord ++ tailWord_2671621).sum := by decide
  have hdescent : baseEnd_2671621 < baseStart_2671621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671655 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2671655 : Nat := 118140960795 + 2671655 * 2 ^ 59
def prefixEnd_2671655 : Nat := 4983230072969 + 3 ^ 40 * 2671655 * 2
def baseEnd_2671655 : Nat := 914562105325233247483859

theorem tailTrace_2671655 : CollatzResearch.WordTrace tailWord_2671655 prefixEnd_2671655 914562105325233247483859 := by
  unfold tailWord_2671655
  simp only [CollatzResearch.WordTrace]
  refine ⟨97443263136057692192616419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64962175424038461461744279 97443263136057692192616419)
  ·
    refine ⟨146164894704086538288924629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97443263136057692192616419 146164894704086538288924629)
    ·
      refine ⟨3425739719627028241146671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 146164894704086538288924629 3425739719627028241146671)
      ·
        refine ⟨5138609579440542361720007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425739719627028241146671 5138609579440542361720007)
        ·
          refine ⟨7707914369160813542580011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5138609579440542361720007 7707914369160813542580011)
          ·
            refine ⟨11561871553741220313870017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707914369160813542580011 11561871553741220313870017)
            ·
              refine ⟨8671403665305915235402513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11561871553741220313870017 8671403665305915235402513)
              ·
                refine ⟨6503552748979436426551885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8671403665305915235402513 6503552748979436426551885)
                ·
                  refine ⟨2438832280867288659956957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6503552748979436426551885 2438832280867288659956957)
                  ·
                    refine ⟨914562105325233247483859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438832280867288659956957 914562105325233247483859)
                    ·
                      rfl

theorem cell22_2671655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2671655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671655 prefixEnd_2671655 := by exact prefixLift 2671655
  have htrace : WordTrace (prefixWord ++ tailWord_2671655) baseStart_2671655 baseEnd_2671655 := by
    simpa [prefixWord, tailWord_2671655, baseEnd_2671655] using wordTrace_append hprefix tailTrace_2671655
  have hstable : (prefixWord ++ tailWord_2671655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671655).length < 2 ^ (prefixWord ++ tailWord_2671655).sum := by decide
  have hdescent : baseEnd_2671655 < baseStart_2671655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671668 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2671668 : Nat := 118140960795 + 2671668 * 2 ^ 59
def prefixEnd_2671668 : Nat := 4983230072969 + 3 ^ 40 * 2671668 * 2
def baseEnd_2671668 : Nat := 304855518496968515636273

theorem tailTrace_2671668 : CollatzResearch.WordTrace tailWord_2671668 prefixEnd_2671668 304855518496968515636273 := by
  unfold tailWord_2671668
  simp only [CollatzResearch.WordTrace]
  refine ⟨48721868642505297706419829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64962491523340396941893105 48721868642505297706419829)
  ·
    refine ⟨4567675185234871659976859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48721868642505297706419829 4567675185234871659976859)
    ·
      refine ⟨6851512777852307489965289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4567675185234871659976859 6851512777852307489965289)
      ·
        refine ⟨5138634583389230617473967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6851512777852307489965289 5138634583389230617473967)
        ·
          refine ⟨7707951875083845926210951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5138634583389230617473967 7707951875083845926210951)
          ·
            refine ⟨11561927812625768889316427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707951875083845926210951 11561927812625768889316427)
            ·
              refine ⟨17342891718938653333974641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11561927812625768889316427 17342891718938653333974641)
              ·
                refine ⟨13007168789203990000480981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17342891718938653333974641 13007168789203990000480981)
                ·
                  refine ⟨304855518496968515636273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13007168789203990000480981 304855518496968515636273)
                  ·
                    rfl

theorem cell22_2671668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2671668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671668 prefixEnd_2671668 := by exact prefixLift 2671668
  have htrace : WordTrace (prefixWord ++ tailWord_2671668) baseStart_2671668 baseEnd_2671668 := by
    simpa [prefixWord, tailWord_2671668, baseEnd_2671668] using wordTrace_append hprefix tailTrace_2671668
  have hstable : (prefixWord ++ tailWord_2671668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671668).length < 2 ^ (prefixWord ++ tailWord_2671668).sum := by decide
  have hdescent : baseEnd_2671668 < baseStart_2671668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671672 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 1, 3]
def baseStart_2671672 : Nat := 118140960795 + 2671672 * 2 ^ 59
def prefixEnd_2671672 : Nat := 4983230072969 + 3 ^ 40 * 2671672 * 2
def baseEnd_2671672 : Nat := 914567924772650869808807

theorem tailTrace_2671672 : CollatzResearch.WordTrace tailWord_2671672 prefixEnd_2671672 914567924772650869808807 := by
  unfold tailWord_2671672
  simp only [CollatzResearch.WordTrace]
  refine ⟨48721941588498052047992635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64962588784664069397323513 48721941588498052047992635)
  ·
    refine ⟨73082912382747078071988953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48721941588498052047992635 73082912382747078071988953)
    ·
      refine ⟨54812184287060308553991715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73082912382747078071988953 54812184287060308553991715)
      ·
        refine ⟨82218276430590462830987573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54812184287060308553991715 82218276430590462830987573)
        ·
          refine ⟨7707963415367855890405085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82218276430590462830987573 7707963415367855890405085)
          ·
            refine ⟨2890486280762945958901907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7707963415367855890405085 2890486280762945958901907)
            ·
              refine ⟨4335729421144418938352861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890486280762945958901907 4335729421144418938352861)
              ·
                refine ⟨1625898532929157101882323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4335729421144418938352861 1625898532929157101882323)
                ·
                  refine ⟨2438847799393735652823485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625898532929157101882323 2438847799393735652823485)
                  ·
                    refine ⟨914567924772650869808807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438847799393735652823485 914567924772650869808807)
                    ·
                      rfl

theorem cell22_2671672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_2671672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671672 prefixEnd_2671672 := by exact prefixLift 2671672
  have htrace : WordTrace (prefixWord ++ tailWord_2671672) baseStart_2671672 baseEnd_2671672 := by
    simpa [prefixWord, tailWord_2671672, baseEnd_2671672] using wordTrace_append hprefix tailTrace_2671672
  have hstable : (prefixWord ++ tailWord_2671672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671672).length < 2 ^ (prefixWord ++ tailWord_2671672).sum := by decide
  have hdescent : baseEnd_2671672 < baseStart_2671672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671702 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2671702 : Nat := 118140960795 + 2671702 * 2 ^ 59
def prefixEnd_2671702 : Nat := 4983230072969 + 3 ^ 40 * 2671702 * 2
def baseEnd_2671702 : Nat := 304859398128580263852905

theorem tailTrace_2671702 : CollatzResearch.WordTrace tailWord_2671702 prefixEnd_2671702 304859398128580263852905 := by
  unfold tailWord_2671702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090311085430463701223585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64963318244591612813051573 6090311085430463701223585)
  ·
    refine ⟨4567733314072847775917689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6090311085430463701223585 4567733314072847775917689)
    ·
      refine ⟨3425799985554635831938267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4567733314072847775917689 3425799985554635831938267)
      ·
        refine ⟨5138699978331953747907401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425799985554635831938267 5138699978331953747907401)
        ·
          refine ⟨3854024983748965310930551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5138699978331953747907401 3854024983748965310930551)
          ·
            refine ⟨5781037475623447966395827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854024983748965310930551 5781037475623447966395827)
            ·
              refine ⟨8671556213435171949593741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781037475623447966395827 8671556213435171949593741)
              ·
                refine ⟨3251833580038189481097653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8671556213435171949593741 3251833580038189481097653)
                ·
                  refine ⟨304859398128580263852905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251833580038189481097653 304859398128580263852905)
                  ·
                    rfl

theorem cell22_2671702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2671702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671702 prefixEnd_2671702 := by exact prefixLift 2671702
  have htrace : WordTrace (prefixWord ++ tailWord_2671702) baseStart_2671702 baseEnd_2671702 := by
    simpa [prefixWord, tailWord_2671702, baseEnd_2671702] using wordTrace_append hprefix tailTrace_2671702
  have hstable : (prefixWord ++ tailWord_2671702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671702).length < 2 ^ (prefixWord ++ tailWord_2671702).sum := by decide
  have hdescent : baseEnd_2671702 < baseStart_2671702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671711 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_2671711 : Nat := 118140960795 + 2671711 * 2 ^ 59
def prefixEnd_2671711 : Nat := 4983230072969 + 3 ^ 40 * 2671711 * 2
def baseEnd_2671711 : Nat := 914581275269667768083687

theorem tailTrace_2671711 : CollatzResearch.WordTrace tailWord_2671711 prefixEnd_2671711 914581275269667768083687 := by
  unfold tailWord_2671711
  simp only [CollatzResearch.WordTrace]
  refine ⟨97445305623854813756654987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64963537082569875837769991 97445305623854813756654987)
  ·
    refine ⟨146167958435782220634982481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97445305623854813756654987 146167958435782220634982481)
    ·
      refine ⟨109625968826836665476236861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146167958435782220634982481 109625968826836665476236861)
      ·
        refine ⟨41109738310063749553588823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109625968826836665476236861 41109738310063749553588823)
        ·
          refine ⟨61664607465095624330383235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41109738310063749553588823 61664607465095624330383235)
          ·
            refine ⟨92496911197643436495574853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61664607465095624330383235 92496911197643436495574853)
            ·
              refine ⟨17343170849558144342920285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92496911197643436495574853 17343170849558144342920285)
              ·
                refine ⟨6503689068584304128595107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17343170849558144342920285 6503689068584304128595107)
                ·
                  refine ⟨9755533602876456192892661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503689068584304128595107 9755533602876456192892661)
                  ·
                    refine ⟨914581275269667768083687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9755533602876456192892661 914581275269667768083687)
                    ·
                      rfl

theorem cell22_2671711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_2671711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671711 prefixEnd_2671711 := by exact prefixLift 2671711
  have htrace : WordTrace (prefixWord ++ tailWord_2671711) baseStart_2671711 baseEnd_2671711 := by
    simpa [prefixWord, tailWord_2671711, baseEnd_2671711] using wordTrace_append hprefix tailTrace_2671711
  have hstable : (prefixWord ++ tailWord_2671711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671711).length < 2 ^ (prefixWord ++ tailWord_2671711).sum := by decide
  have hdescent : baseEnd_2671711 < baseStart_2671711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671745 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2671745 : Nat := 118140960795 + 2671745 * 2 ^ 59
def prefixEnd_2671745 : Nat := 4983230072969 + 3 ^ 40 * 2671745 * 2
def baseEnd_2671745 : Nat := 914592914164503012733583

theorem tailTrace_2671745 : CollatzResearch.WordTrace tailWord_2671745 prefixEnd_2671745 914592914164503012733583 := by
  unfold tailWord_2671745
  simp only [CollatzResearch.WordTrace]
  refine ⟨97446545705731637563392689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64964363803821091708928459 97446545705731637563392689)
  ·
    refine ⟨73084909279298728172544517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97446545705731637563392689 73084909279298728172544517)
    ·
      refine ⟨13703420489868511532352097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73084909279298728172544517 13703420489868511532352097)
      ·
        refine ⟨10277565367401383649264073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13703420489868511532352097 10277565367401383649264073)
        ·
          refine ⟨7708174025551037736948055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10277565367401383649264073 7708174025551037736948055)
          ·
            refine ⟨11562261038326556605422083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7708174025551037736948055 11562261038326556605422083)
            ·
              refine ⟨17343391557489834908133125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11562261038326556605422083 17343391557489834908133125)
              ·
                refine ⟨3251885917029344045274961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17343391557489834908133125 3251885917029344045274961)
                ·
                  refine ⟨2438914437772008033956221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3251885917029344045274961 2438914437772008033956221)
                  ·
                    refine ⟨914592914164503012733583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2438914437772008033956221 914592914164503012733583)
                    ·
                      rfl

theorem cell22_2671745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2671745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671745 prefixEnd_2671745 := by exact prefixLift 2671745
  have htrace : WordTrace (prefixWord ++ tailWord_2671745) baseStart_2671745 baseEnd_2671745 := by
    simpa [prefixWord, tailWord_2671745, baseEnd_2671745] using wordTrace_append hprefix tailTrace_2671745
  have hstable : (prefixWord ++ tailWord_2671745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671745).length < 2 ^ (prefixWord ++ tailWord_2671745).sum := by decide
  have hdescent : baseEnd_2671745 < baseStart_2671745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671758 : List Nat := [4, 1, 1, 3, 2, 1, 3, 7]
def baseStart_2671758 : Nat := 118140960795 + 2671758 * 2 ^ 59
def prefixEnd_2671758 : Nat := 4983230072969 + 3 ^ 40 * 2671758 * 2
def baseEnd_2671758 : Nat := 101621929370019479128727

theorem tailTrace_2671758 : CollatzResearch.WordTrace tailWord_2671758 prefixEnd_2671758 101621929370019479128727 := by
  unfold tailWord_2671758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12180877481835567597951991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64964679903123027189077285 12180877481835567597951991)
  ·
    refine ⟨18271316222753351396927987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12180877481835567597951991 18271316222753351396927987)
    ·
      refine ⟨27406974334130027095391981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18271316222753351396927987 27406974334130027095391981)
      ·
        refine ⟨10277615375298760160771993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27406974334130027095391981 10277615375298760160771993)
        ·
          refine ⟨7708211531474070120578995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10277615375298760160771993 7708211531474070120578995)
          ·
            refine ⟨11562317297211105180868493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7708211531474070120578995 11562317297211105180868493)
            ·
              refine ⟨4335868986454164442825685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11562317297211105180868493 4335868986454164442825685)
              ·
                refine ⟨101621929370019479128727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4335868986454164442825685 101621929370019479128727)
                ·
                  rfl

theorem cell22_2671758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_2671758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671758 prefixEnd_2671758 := by exact prefixLift 2671758
  have htrace : WordTrace (prefixWord ++ tailWord_2671758) baseStart_2671758 baseEnd_2671758 := by
    simpa [prefixWord, tailWord_2671758, baseEnd_2671758] using wordTrace_append hprefix tailTrace_2671758
  have hstable : (prefixWord ++ tailWord_2671758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671758).length < 2 ^ (prefixWord ++ tailWord_2671758).sum := by decide
  have hdescent : baseEnd_2671758 < baseStart_2671758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671775 : List Nat := [1, 1, 2, 6, 2, 1, 3, 6]
def baseStart_2671775 : Nat := 118140960795 + 2671775 * 2 ^ 59
def prefixEnd_2671775 : Nat := 4983230072969 + 3 ^ 40 * 2671775 * 2
def baseEnd_2671775 : Nat := 101622575975288103831499

theorem tailTrace_2671775 : CollatzResearch.WordTrace tailWord_2671775 prefixEnd_2671775 101622575975288103831499 := by
  unfold tailWord_2671775
  simp only [CollatzResearch.WordTrace]
  refine ⟨97447639895622952686984779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64965093263748635124656519 97447639895622952686984779)
  ·
    refine ⟨146171459843434429030477169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97447639895622952686984779 146171459843434429030477169)
    ·
      refine ⟨109628594882575821772857877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146171459843434429030477169 109628594882575821772857877)
      ·
        refine ⟨5138840385120741645602713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109628594882575821772857877 5138840385120741645602713)
        ·
          refine ⟨3854130288840556234202035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5138840385120741645602713 3854130288840556234202035)
          ·
            refine ⟨5781195433260834351303053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854130288840556234202035 5781195433260834351303053)
            ·
              refine ⟨2167948287472812881738645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5781195433260834351303053 2167948287472812881738645)
              ·
                refine ⟨101622575975288103831499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2167948287472812881738645 101622575975288103831499)
                ·
                  rfl

theorem cell22_2671775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 6].length) (baseStart_2671775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671775 prefixEnd_2671775 := by exact prefixLift 2671775
  have htrace : WordTrace (prefixWord ++ tailWord_2671775) baseStart_2671775 baseEnd_2671775 := by
    simpa [prefixWord, tailWord_2671775, baseEnd_2671775] using wordTrace_append hprefix tailTrace_2671775
  have hstable : (prefixWord ++ tailWord_2671775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671775).length < 2 ^ (prefixWord ++ tailWord_2671775).sum := by decide
  have hdescent : baseEnd_2671775 < baseStart_2671775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671818 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2671818 : Nat := 118140960795 + 2671818 * 2 ^ 59
def prefixEnd_2671818 : Nat := 4983230072969 + 3 ^ 40 * 2671818 * 2
def baseEnd_2671818 : Nat := 914617903556355155658359

theorem tailTrace_2671818 : CollatzResearch.WordTrace tailWord_2671818 prefixEnd_2671818 914617903556355155658359 := by
  unfold tailWord_2671818
  simp only [CollatzResearch.WordTrace]
  refine ⟨24362302058616792757700027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64966138822978114020533405 24362302058616792757700027)
  ·
    refine ⟨36543453087925189136550041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24362302058616792757700027 36543453087925189136550041)
    ·
      refine ⟨27407589815943891852412531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36543453087925189136550041 27407589815943891852412531)
      ·
        refine ⟨41111384723915837778618797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27407589815943891852412531 41111384723915837778618797)
        ·
          refine ⟨15416769271468439166982049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41111384723915837778618797 15416769271468439166982049)
          ·
            refine ⟨11562576953601329375236537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416769271468439166982049 11562576953601329375236537)
            ·
              refine ⟨8671932715200997031427403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11562576953601329375236537 8671932715200997031427403)
              ·
                refine ⟨13007899072801495547141105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671932715200997031427403 13007899072801495547141105)
                ·
                  refine ⟨9755924304601121660355829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13007899072801495547141105 9755924304601121660355829)
                  ·
                    refine ⟨914617903556355155658359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9755924304601121660355829 914617903556355155658359)
                    ·
                      rfl

theorem cell22_2671818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2671818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671818 prefixEnd_2671818 := by exact prefixLift 2671818
  have htrace : WordTrace (prefixWord ++ tailWord_2671818) baseStart_2671818 baseEnd_2671818 := by
    simpa [prefixWord, tailWord_2671818, baseEnd_2671818] using wordTrace_append hprefix tailTrace_2671818
  have hstable : (prefixWord ++ tailWord_2671818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671818).length < 2 ^ (prefixWord ++ tailWord_2671818).sum := by decide
  have hdescent : baseEnd_2671818 < baseStart_2671818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671850 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2671850 : Nat := 118140960795 + 2671850 * 2 ^ 59
def prefixEnd_2671850 : Nat := 4983230072969 + 3 ^ 40 * 2671850 * 2
def baseEnd_2671850 : Nat := 914628857810317738858261

theorem tailTrace_2671850 : CollatzResearch.WordTrace tailWord_2671850 prefixEnd_2671850 914628857810317738858261 := by
  unfold tailWord_2671850
  simp only [CollatzResearch.WordTrace]
  refine ⟨24362593842587810123991251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64966916913567493663976669 24362593842587810123991251)
  ·
    refine ⟨36543890763881715185986877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24362593842587810123991251 36543890763881715185986877)
    ·
      refine ⟨13703959036455643194745079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36543890763881715185986877 13703959036455643194745079)
      ·
        refine ⟨20555938554683464792117619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13703959036455643194745079 20555938554683464792117619)
        ·
          refine ⟨30833907832025197188176429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20555938554683464792117619 30833907832025197188176429)
          ·
            refine ⟨11562715437009448945566161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30833907832025197188176429 11562715437009448945566161)
            ·
              refine ⟨8672036577757086709174621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11562715437009448945566161 8672036577757086709174621)
              ·
                refine ⟨3252013716658907515940483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8672036577757086709174621 3252013716658907515940483)
                ·
                  refine ⟨4878020574988361273910725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252013716658907515940483 4878020574988361273910725)
                  ·
                    refine ⟨914628857810317738858261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878020574988361273910725 914628857810317738858261)
                    ·
                      rfl

theorem cell22_2671850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2671850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671850 prefixEnd_2671850 := by exact prefixLift 2671850
  have htrace : WordTrace (prefixWord ++ tailWord_2671850) baseStart_2671850 baseEnd_2671850 := by
    simpa [prefixWord, tailWord_2671850, baseEnd_2671850] using wordTrace_append hprefix tailTrace_2671850
  have hstable : (prefixWord ++ tailWord_2671850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671850).length < 2 ^ (prefixWord ++ tailWord_2671850).sum := by decide
  have hdescent : baseEnd_2671850 < baseStart_2671850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671895 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2671895 : Nat := 118140960795 + 2671895 * 2 ^ 59
def prefixEnd_2671895 : Nat := 4983230072969 + 3 ^ 40 * 2671895 * 2
def baseEnd_2671895 : Nat := 914644262229952621483123

theorem tailTrace_2671895 : CollatzResearch.WordTrace tailWord_2671895 prefixEnd_2671895 914644262229952621483123 := by
  unfold tailWord_2671895
  simp only [CollatzResearch.WordTrace]
  refine ⟨97452016655188213181353139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64968011103458808787568759 97452016655188213181353139)
  ·
    refine ⟨146178024982782319772029709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97452016655188213181353139 146178024982782319772029709)
    ·
      refine ⟨54816759368543369914511141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146178024982782319772029709 54816759368543369914511141)
      ·
        refine ⟨10278142381601881858970839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54816759368543369914511141 10278142381601881858970839)
        ·
          refine ⟨15417213572402822788456259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10278142381601881858970839 15417213572402822788456259)
          ·
            refine ⟨23125820358604234182684389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15417213572402822788456259 23125820358604234182684389)
            ·
              refine ⟨4336091317238293909253323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23125820358604234182684389 4336091317238293909253323)
              ·
                refine ⟨6504136975857440863879985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4336091317238293909253323 6504136975857440863879985)
                ·
                  refine ⟨4878102731893080647909989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6504136975857440863879985 4878102731893080647909989)
                  ·
                    refine ⟨914644262229952621483123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878102731893080647909989 914644262229952621483123)
                    ·
                      rfl

theorem cell22_2671895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2671895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671895 prefixEnd_2671895 := by exact prefixLift 2671895
  have htrace : WordTrace (prefixWord ++ tailWord_2671895) baseStart_2671895 baseEnd_2671895 := by
    simpa [prefixWord, tailWord_2671895, baseEnd_2671895] using wordTrace_append hprefix tailTrace_2671895
  have hstable : (prefixWord ++ tailWord_2671895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671895).length < 2 ^ (prefixWord ++ tailWord_2671895).sum := by decide
  have hdescent : baseEnd_2671895 < baseStart_2671895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671914 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2671914 : Nat := 118140960795 + 2671914 * 2 ^ 59
def prefixEnd_2671914 : Nat := 4983230072969 + 3 ^ 40 * 2671914 * 2
def baseEnd_2671914 : Nat := 914650766318242905258065

theorem tailTrace_2671914 : CollatzResearch.WordTrace tailWord_2671914 prefixEnd_2671914 914650766318242905258065 := by
  unfold tailWord_2671914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24363177410529844856573699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64968473094746252950863197 24363177410529844856573699)
  ·
    refine ⟨36544766115794767284860549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24363177410529844856573699 36544766115794767284860549)
    ·
      refine ⟨6852143646711518865911353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36544766115794767284860549 6852143646711518865911353)
      ·
        refine ⟨5139107735033639149433515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6852143646711518865911353 5139107735033639149433515)
        ·
          refine ⟨7708661602550458724150273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139107735033639149433515 7708661602550458724150273)
          ·
            refine ⟨5781496201912844043112705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7708661602550458724150273 5781496201912844043112705)
            ·
              refine ⟨4336122151434633032334529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5781496201912844043112705 4336122151434633032334529)
              ·
                refine ⟨3252091613575974774250897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4336122151434633032334529 3252091613575974774250897)
                ·
                  refine ⟨2439068710181981080688173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252091613575974774250897 2439068710181981080688173)
                  ·
                    refine ⟨914650766318242905258065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439068710181981080688173 914650766318242905258065)
                    ·
                      rfl

theorem cell22_2671914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2671914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671914 prefixEnd_2671914 := by exact prefixLift 2671914
  have htrace : WordTrace (prefixWord ++ tailWord_2671914) baseStart_2671914 baseEnd_2671914 := by
    simpa [prefixWord, tailWord_2671914, baseEnd_2671914] using wordTrace_append hprefix tailTrace_2671914
  have hstable : (prefixWord ++ tailWord_2671914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671914).length < 2 ^ (prefixWord ++ tailWord_2671914).sum := by decide
  have hdescent : baseEnd_2671914 < baseStart_2671914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671923 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_2671923 : Nat := 118140960795 + 2671923 * 2 ^ 59
def prefixEnd_2671923 : Nat := 4983230072969 + 3 ^ 40 * 2671923 * 2
def baseEnd_2671923 : Nat := 914653847202169881783037

theorem tailTrace_2671923 : CollatzResearch.WordTrace tailWord_2671923 prefixEnd_2671923 914653847202169881783037 := by
  unfold tailWord_2671923
  simp only [CollatzResearch.WordTrace]
  refine ⟨97453037899086773963372423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64968691932724515975581615 97453037899086773963372423)
  ·
    refine ⟨146179556848630160945058635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97453037899086773963372423 146179556848630160945058635)
    ·
      refine ⟨219269335272945241417587953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146179556848630160945058635 219269335272945241417587953)
      ·
        refine ⟨164452001454708931063190965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219269335272945241417587953 164452001454708931063190965)
        ·
          refine ⟨15417375136378962287174153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164452001454708931063190965 15417375136378962287174153)
          ·
            refine ⟨11563031352284221715380615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15417375136378962287174153 11563031352284221715380615)
            ·
              refine ⟨17344547028426332573070923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11563031352284221715380615 17344547028426332573070923)
              ·
                refine ⟨26016820542639498859606385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17344547028426332573070923 26016820542639498859606385)
                ·
                  refine ⟨19512615406979624144704789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26016820542639498859606385 19512615406979624144704789)
                  ·
                    refine ⟨914653847202169881783037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19512615406979624144704789 914653847202169881783037)
                    ·
                      rfl

theorem cell22_2671923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_2671923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671923 prefixEnd_2671923 := by exact prefixLift 2671923
  have htrace : WordTrace (prefixWord ++ tailWord_2671923) baseStart_2671923 baseEnd_2671923 := by
    simpa [prefixWord, tailWord_2671923, baseEnd_2671923] using wordTrace_append hprefix tailTrace_2671923
  have hstable : (prefixWord ++ tailWord_2671923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671923).length < 2 ^ (prefixWord ++ tailWord_2671923).sum := by decide
  have hdescent : baseEnd_2671923 < baseStart_2671923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671953 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2671953 : Nat := 118140960795 + 2671953 * 2 ^ 59
def prefixEnd_2671953 : Nat := 4983230072969 + 3 ^ 40 * 2671953 * 2
def baseEnd_2671953 : Nat := 914664116815259803532945

theorem tailTrace_2671953 : CollatzResearch.WordTrace tailWord_2671953 prefixEnd_2671953 914664116815259803532945 := by
  unfold tailWord_2671953
  simp only [CollatzResearch.WordTrace]
  refine ⟨97454132088978089086964513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64969421392652059391309675 97454132088978089086964513)
  ·
    refine ⟨73090599066733566815223385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97454132088978089086964513 73090599066733566815223385)
    ·
      refine ⟨54817949300050175111417539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73090599066733566815223385 54817949300050175111417539)
      ·
        refine ⟨82226923950075262667126309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54817949300050175111417539 82226923950075262667126309)
        ·
          refine ⟨15417548240639111750086183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82226923950075262667126309 15417548240639111750086183)
          ·
            refine ⟨23126322360958667625129275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15417548240639111750086183 23126322360958667625129275)
            ·
              refine ⟨34689483541438001437693913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23126322360958667625129275 34689483541438001437693913)
              ·
                refine ⟨26017112656078501078270435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34689483541438001437693913 26017112656078501078270435)
                ·
                  refine ⟨39025668984117751617405653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26017112656078501078270435 39025668984117751617405653)
                  ·
                    refine ⟨914664116815259803532945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39025668984117751617405653 914664116815259803532945)
                    ·
                      rfl

theorem cell22_2671953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2671953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671953 prefixEnd_2671953 := by exact prefixLift 2671953
  have htrace : WordTrace (prefixWord ++ tailWord_2671953) baseStart_2671953 baseEnd_2671953 := by
    simpa [prefixWord, tailWord_2671953, baseEnd_2671953] using wordTrace_append hprefix tailTrace_2671953
  have hstable : (prefixWord ++ tailWord_2671953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671953).length < 2 ^ (prefixWord ++ tailWord_2671953).sum := by decide
  have hdescent : baseEnd_2671953 < baseStart_2671953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671959 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 1, 3]
def baseStart_2671959 : Nat := 118140960795 + 2671959 * 2 ^ 59
def prefixEnd_2671959 : Nat := 4983230072969 + 3 ^ 40 * 2671959 * 2
def baseEnd_2671959 : Nat := 914666170737877787882927

theorem tailTrace_2671959 : CollatzResearch.WordTrace tailWord_2671959 prefixEnd_2671959 914666170737877787882927 := by
  unfold tailWord_2671959
  simp only [CollatzResearch.WordTrace]
  refine ⟨97454350926956352111682931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64969567284637568074455287 97454350926956352111682931)
  ·
    refine ⟨146181526390434528167524397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97454350926956352111682931 146181526390434528167524397)
    ·
      refine ⟨54818072396412948062821649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146181526390434528167524397 54818072396412948062821649)
      ·
        refine ⟨41113554297309711047116237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54818072396412948062821649 41113554297309711047116237)
        ·
          refine ⟨15417582861491141642668589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41113554297309711047116237 15417582861491141642668589)
          ·
            refine ⟨5781593573059178116000721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15417582861491141642668589 5781593573059178116000721)
            ·
              refine ⟨4336195179794383587000541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5781593573059178116000721 4336195179794383587000541)
              ·
                refine ⟨1626073192422893845125203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336195179794383587000541 1626073192422893845125203)
                ·
                  refine ⟨2439109788634340767687805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626073192422893845125203 2439109788634340767687805)
                  ·
                    refine ⟨914666170737877787882927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439109788634340767687805 914666170737877787882927)
                    ·
                      rfl

theorem cell22_2671959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_2671959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671959 prefixEnd_2671959 := by exact prefixLift 2671959
  have htrace : WordTrace (prefixWord ++ tailWord_2671959) baseStart_2671959 baseEnd_2671959 := by
    simpa [prefixWord, tailWord_2671959, baseEnd_2671959] using wordTrace_append hprefix tailTrace_2671959
  have hstable : (prefixWord ++ tailWord_2671959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671959).length < 2 ^ (prefixWord ++ tailWord_2671959).sum := by decide
  have hdescent : baseEnd_2671959 < baseStart_2671959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671965 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2671965 : Nat := 118140960795 + 2671965 * 2 ^ 59
def prefixEnd_2671965 : Nat := 4983230072969 + 3 ^ 40 * 2671965 * 2
def baseEnd_2671965 : Nat := 914668224660495772232909

theorem tailTrace_2671965 : CollatzResearch.WordTrace tailWord_2671965 prefixEnd_2671965 914668224660495772232909 := by
  unfold tailWord_2671965
  simp only [CollatzResearch.WordTrace]
  refine ⟨97454569764934615136401349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64969713176623076757600899 97454569764934615136401349)
  ·
    refine ⟨18272731830925240338075253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97454569764934615136401349 18272731830925240338075253)
    ·
      refine ⟨1713068609149241281694555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18272731830925240338075253 1713068609149241281694555)
      ·
        refine ⟨2569602913723861922541833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713068609149241281694555 2569602913723861922541833)
        ·
          refine ⟨1927202185292896441906375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2569602913723861922541833 1927202185292896441906375)
          ·
            refine ⟨2890803277939344662859563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927202185292896441906375 2890803277939344662859563)
            ·
              refine ⟨4336204916909016994289345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890803277939344662859563 4336204916909016994289345)
              ·
                refine ⟨3252153687681762745717009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4336204916909016994289345 3252153687681762745717009)
                ·
                  refine ⟨2439115265761322059287757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252153687681762745717009 2439115265761322059287757)
                  ·
                    refine ⟨914668224660495772232909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439115265761322059287757 914668224660495772232909)
                    ·
                      rfl

theorem cell22_2671965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2671965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671965 prefixEnd_2671965 := by exact prefixLift 2671965
  have htrace : WordTrace (prefixWord ++ tailWord_2671965) baseStart_2671965 baseEnd_2671965 := by
    simpa [prefixWord, tailWord_2671965, baseEnd_2671965] using wordTrace_append hprefix tailTrace_2671965
  have hstable : (prefixWord ++ tailWord_2671965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671965).length < 2 ^ (prefixWord ++ tailWord_2671965).sum := by decide
  have hdescent : baseEnd_2671965 < baseStart_2671965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671970 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2671970 : Nat := 118140960795 + 2671970 * 2 ^ 59
def prefixEnd_2671970 : Nat := 4983230072969 + 3 ^ 40 * 2671970 * 2
def baseEnd_2671970 : Nat := 914669936262677425857893

theorem tailTrace_2671970 : CollatzResearch.WordTrace tailWord_2671970 prefixEnd_2671970 914669936262677425857893 := by
  unfold tailWord_2671970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24363688032479125247583341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64969834753277667326888909 24363688032479125247583341)
  ·
    refine ⟨9136383012179671967843753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24363688032479125247583341 9136383012179671967843753)
    ·
      refine ⟨6852287259134753975882815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9136383012179671967843753 6852287259134753975882815)
      ·
        refine ⟨10278430888702130963824223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6852287259134753975882815 10278430888702130963824223)
        ·
          refine ⟨15417646333053196445736335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10278430888702130963824223 15417646333053196445736335)
          ·
            refine ⟨23126469499579794668604503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15417646333053196445736335 23126469499579794668604503)
            ·
              refine ⟨34689704249369692002906755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23126469499579794668604503 34689704249369692002906755)
              ·
                refine ⟨52034556374054538004360133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34689704249369692002906755 52034556374054538004360133)
                ·
                  refine ⟨9756479320135225875817525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52034556374054538004360133 9756479320135225875817525)
                  ·
                    refine ⟨914669936262677425857893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9756479320135225875817525 914669936262677425857893)
                    ·
                      rfl

theorem cell22_2671970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2671970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671970 prefixEnd_2671970 := by exact prefixLift 2671970
  have htrace : WordTrace (prefixWord ++ tailWord_2671970) baseStart_2671970 baseEnd_2671970 := by
    simpa [prefixWord, tailWord_2671970, baseEnd_2671970] using wordTrace_append hprefix tailTrace_2671970
  have hstable : (prefixWord ++ tailWord_2671970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671970).length < 2 ^ (prefixWord ++ tailWord_2671970).sum := by decide
  have hdescent : baseEnd_2671970 < baseStart_2671970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671972 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2671972 : Nat := 118140960795 + 2671972 * 2 ^ 59
def prefixEnd_2671972 : Nat := 4983230072969 + 3 ^ 40 * 2671972 * 2
def baseEnd_2671972 : Nat := 304890206967850029102629

theorem tailTrace_2671972 : CollatzResearch.WordTrace tailWord_2671972 prefixEnd_2671972 304890206967850029102629 := by
  unfold tailWord_2671972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48727412537954627665953085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64969883383939503554604113 48727412537954627665953085)
  ·
    refine ⟨18272779701732985374732407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48727412537954627665953085 18272779701732985374732407)
    ·
      refine ⟨27409169552599478062098611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18272779701732985374732407 27409169552599478062098611)
      ·
        refine ⟨41113754328899217093147917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27409169552599478062098611 41113754328899217093147917)
        ·
          refine ⟨15417657873337206409930469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41113754328899217093147917 15417657873337206409930469)
          ·
            refine ⟨2890810851250726201861963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15417657873337206409930469 2890810851250726201861963)
            ·
              refine ⟨4336216276876089302792945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890810851250726201861963 4336216276876089302792945)
              ·
                refine ⟨3252162207657066977094709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4336216276876089302792945 3252162207657066977094709)
                ·
                  refine ⟨304890206967850029102629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3252162207657066977094709 304890206967850029102629)
                  ·
                    rfl

theorem cell22_2671972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2671972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671972 prefixEnd_2671972 := by exact prefixLift 2671972
  have htrace : WordTrace (prefixWord ++ tailWord_2671972) baseStart_2671972 baseEnd_2671972 := by
    simpa [prefixWord, tailWord_2671972, baseEnd_2671972] using wordTrace_append hprefix tailTrace_2671972
  have hstable : (prefixWord ++ tailWord_2671972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671972).length < 2 ^ (prefixWord ++ tailWord_2671972).sum := by decide
  have hdescent : baseEnd_2671972 < baseStart_2671972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671989 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 5]
def baseStart_2671989 : Nat := 118140960795 + 2671989 * 2 ^ 59
def prefixEnd_2671989 : Nat := 4983230072969 + 3 ^ 40 * 2671989 * 2
def baseEnd_2671989 : Nat := 304892146783655903210945

theorem tailTrace_2671989 : CollatzResearch.WordTrace tailWord_2671989 prefixEnd_2671989 304892146783655903210945 := by
  unfold tailWord_2671989
  simp only [CollatzResearch.WordTrace]
  refine ⟨97455445116847667235275021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64970296744565111490183347 97455445116847667235275021)
  ·
    refine ⟨36545791918817875213228133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97455445116847667235275021 36545791918817875213228133)
    ·
      refine ⟨6852335984778351602480275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36545791918817875213228133 6852335984778351602480275)
      ·
        refine ⟨10278503977167527403720413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6852335984778351602480275 10278503977167527403720413)
        ·
          refine ⟨3854438991437822776395155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10278503977167527403720413 3854438991437822776395155)
          ·
            refine ⟨5781658487156734164592733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854438991437822776395155 5781658487156734164592733)
            ·
              refine ⟨2168121932683775311722275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5781658487156734164592733 2168121932683775311722275)
              ·
                refine ⟨3252182899025662967583413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168121932683775311722275 3252182899025662967583413)
                ·
                  refine ⟨304892146783655903210945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3252182899025662967583413 304892146783655903210945)
                  ·
                    rfl

theorem cell22_2671989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_2671989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2671989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2671989 prefixEnd_2671989 := by exact prefixLift 2671989
  have htrace : WordTrace (prefixWord ++ tailWord_2671989) baseStart_2671989 baseEnd_2671989 := by
    simpa [prefixWord, tailWord_2671989, baseEnd_2671989] using wordTrace_append hprefix tailTrace_2671989
  have hstable : (prefixWord ++ tailWord_2671989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671989).length < 2 ^ (prefixWord ++ tailWord_2671989).sum := by decide
  have hdescent : baseEnd_2671989 < baseStart_2671989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672032 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_2672032 : Nat := 118140960795 + 2672032 * 2 ^ 59
def prefixEnd_2672032 : Nat := 4983230072969 + 3 ^ 40 * 2672032 * 2
def baseEnd_2672032 : Nat := 914691160129729930807703

theorem tailTrace_2672032 : CollatzResearch.WordTrace tailWord_2672032 prefixEnd_2672032 914691160129729930807703 := by
  unfold tailWord_2672032
  simp only [CollatzResearch.WordTrace]
  refine ⟨48728506727845942789545175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64971342303794590386060233 48728506727845942789545175)
  ·
    refine ⟨73092760091768914184317763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48728506727845942789545175 73092760091768914184317763)
    ·
      refine ⟨109639140137653371276476645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73092760091768914184317763 109639140137653371276476645)
      ·
        refine ⟨20557338775810007114339371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109639140137653371276476645 20557338775810007114339371)
        ·
          refine ⟨30836008163715010671509057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20557338775810007114339371 30836008163715010671509057)
          ·
            refine ⟨23127006122786258003631793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30836008163715010671509057 23127006122786258003631793)
            ·
              refine ⟨17345254592089693502723845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23127006122786258003631793 17345254592089693502723845)
              ·
                refine ⟨3252235236016817531760721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17345254592089693502723845 3252235236016817531760721)
                ·
                  refine ⟨2439176427012613148820541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252235236016817531760721 2439176427012613148820541)
                  ·
                    refine ⟨914691160129729930807703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439176427012613148820541 914691160129729930807703)
                    ·
                      rfl

theorem cell22_2672032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_2672032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672032 prefixEnd_2672032 := by exact prefixLift 2672032
  have htrace : WordTrace (prefixWord ++ tailWord_2672032) baseStart_2672032 baseEnd_2672032 := by
    simpa [prefixWord, tailWord_2672032, baseEnd_2672032] using wordTrace_append hprefix tailTrace_2672032
  have hstable : (prefixWord ++ tailWord_2672032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672032).length < 2 ^ (prefixWord ++ tailWord_2672032).sum := by decide
  have hdescent : baseEnd_2672032 < baseStart_2672032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672043 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_2672043 : Nat := 118140960795 + 2672043 * 2 ^ 59
def prefixEnd_2672043 : Nat := 4983230072969 + 3 ^ 40 * 2672043 * 2
def baseEnd_2672043 : Nat := 914694925654529568782669

theorem tailTrace_2672043 : CollatzResearch.WordTrace tailWord_2672043 prefixEnd_2672043 914694925654529568782669 := by
  unfold tailWord_2672043
  simp only [CollatzResearch.WordTrace]
  refine ⟨97457414658652034457740783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64971609772434689638493855 97457414658652034457740783)
  ·
    refine ⟨146186121987978051686611175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97457414658652034457740783 146186121987978051686611175)
    ·
      refine ⟨219279182981967077529916763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146186121987978051686611175 219279182981967077529916763)
      ·
        refine ⟨328918774472950616294875145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219279182981967077529916763 328918774472950616294875145)
        ·
          refine ⟨246689080854712962221156359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328918774472950616294875145 246689080854712962221156359)
          ·
            refine ⟨370033621282069443331734539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246689080854712962221156359 370033621282069443331734539)
            ·
              refine ⟨555050431923104164997601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370033621282069443331734539 555050431923104164997601809)
              ·
                refine ⟨416287823942328123748201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555050431923104164997601809 416287823942328123748201357)
                ·
                  refine ⟨156107933978373046405575509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416287823942328123748201357 156107933978373046405575509)
                  ·
                    refine ⟨914694925654529568782669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156107933978373046405575509 914694925654529568782669)
                    ·
                      rfl

theorem cell22_2672043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_2672043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672043 prefixEnd_2672043 := by exact prefixLift 2672043
  have htrace : WordTrace (prefixWord ++ tailWord_2672043) baseStart_2672043 baseEnd_2672043 := by
    simpa [prefixWord, tailWord_2672043, baseEnd_2672043] using wordTrace_append hprefix tailTrace_2672043
  have hstable : (prefixWord ++ tailWord_2672043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672043).length < 2 ^ (prefixWord ++ tailWord_2672043).sum := by decide
  have hdescent : baseEnd_2672043 < baseStart_2672043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672137 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_2672137 : Nat := 118140960795 + 2672137 * 2 ^ 59
def prefixEnd_2672137 : Nat := 4983230072969 + 3 ^ 40 * 2672137 * 2
def baseEnd_2672137 : Nat := 914727103775544656932381

theorem tailTrace_2672137 : CollatzResearch.WordTrace tailWord_2672137 prefixEnd_2672137 914727103775544656932381 := by
  unfold tailWord_2672137
  simp only [CollatzResearch.WordTrace]
  refine ⟨97460843120311488511662665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64973895413540992341108443 97460843120311488511662665)
  ·
    refine ⟨73095632340233616383746999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97460843120311488511662665 73095632340233616383746999)
    ·
      refine ⟨109643448510350424575620499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73095632340233616383746999 109643448510350424575620499)
      ·
        refine ⟨164465172765525636863430749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109643448510350424575620499 164465172765525636863430749)
        ·
          refine ⟨61674439787072113823786531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164465172765525636863430749 61674439787072113823786531)
          ·
            refine ⟨92511659680608170735679797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61674439787072113823786531 92511659680608170735679797)
            ·
              refine ⟨8672968095057016006469981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92511659680608170735679797 8672968095057016006469981)
              ·
                refine ⟨3252363035646381002426243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8672968095057016006469981 3252363035646381002426243)
                ·
                  refine ⟨4878544553469571503639365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252363035646381002426243 4878544553469571503639365)
                  ·
                    refine ⟨914727103775544656932381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878544553469571503639365 914727103775544656932381)
                    ·
                      rfl

theorem cell22_2672137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_2672137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672137 prefixEnd_2672137 := by exact prefixLift 2672137
  have htrace : WordTrace (prefixWord ++ tailWord_2672137) baseStart_2672137 baseEnd_2672137 := by
    simpa [prefixWord, tailWord_2672137, baseEnd_2672137] using wordTrace_append hprefix tailTrace_2672137
  have hstable : (prefixWord ++ tailWord_2672137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672137).length < 2 ^ (prefixWord ++ tailWord_2672137).sum := by decide
  have hdescent : baseEnd_2672137 < baseStart_2672137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672141 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2672141 : Nat := 118140960795 + 2672141 * 2 ^ 59
def prefixEnd_2672141 : Nat := 4983230072969 + 3 ^ 40 * 2672141 * 2
def baseEnd_2672141 : Nat := 304909491019096659944123

theorem tailTrace_2672141 : CollatzResearch.WordTrace tailWord_2672141 prefixEnd_2672141 304909491019096659944123 := by
  unfold tailWord_2672141
  simp only [CollatzResearch.WordTrace]
  refine ⟨97460989012296997194808277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64973992674864664796538851 97460989012296997194808277)
  ·
    refine ⟨2284241929975710871753319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 97460989012296997194808277 2284241929975710871753319)
    ·
      refine ⟨3426362894963566307629979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284241929975710871753319 3426362894963566307629979)
      ·
        refine ⟨5139544342445349461444969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426362894963566307629979 5139544342445349461444969)
        ·
          refine ⟨3854658256834012096083727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5139544342445349461444969 3854658256834012096083727)
          ·
            refine ⟨5781987385251018144125591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854658256834012096083727 5781987385251018144125591)
            ·
              refine ⟨8672981077876527216188387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781987385251018144125591 8672981077876527216188387)
              ·
                refine ⟨13009471616814790824282581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8672981077876527216188387 13009471616814790824282581)
                ·
                  refine ⟨304909491019096659944123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13009471616814790824282581 304909491019096659944123)
                  ·
                    rfl

theorem cell22_2672141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2672141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672141 prefixEnd_2672141 := by exact prefixLift 2672141
  have htrace : WordTrace (prefixWord ++ tailWord_2672141) baseStart_2672141 baseEnd_2672141 := by
    simpa [prefixWord, tailWord_2672141, baseEnd_2672141] using wordTrace_append hprefix tailTrace_2672141
  have hstable : (prefixWord ++ tailWord_2672141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672141).length < 2 ^ (prefixWord ++ tailWord_2672141).sum := by decide
  have hdescent : baseEnd_2672141 < baseStart_2672141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672199 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2672199 : Nat := 118140960795 + 2672199 * 2 ^ 59
def prefixEnd_2672199 : Nat := 4983230072969 + 3 ^ 40 * 2672199 * 2
def baseEnd_2672199 : Nat := 914748327642597161882191

theorem tailTrace_2672199 : CollatzResearch.WordTrace tailWord_2672199 prefixEnd_2672199 914748327642597161882191 := by
  unfold tailWord_2672199
  simp only [CollatzResearch.WordTrace]
  refine ⟨97463104446086873100419651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64975402964057915400279767 97463104446086873100419651)
  ·
    refine ⟨146194656669130309650629477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97463104446086873100419651 146194656669130309650629477)
    ·
      refine ⟨27411498125461933059493027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146194656669130309650629477 27411498125461933059493027)
      ·
        refine ⟨41117247188192899589239541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27411498125461933059493027 41117247188192899589239541)
        ·
          refine ⟨3854741923893084336491207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41117247188192899589239541 3854741923893084336491207)
          ·
            refine ⟨5782112885839626504736811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854741923893084336491207 5782112885839626504736811)
            ·
              refine ⟨8673169328759439757105217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782112885839626504736811 8673169328759439757105217)
              ·
                refine ⟨6504876996569579817828913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8673169328759439757105217 6504876996569579817828913)
                ·
                  refine ⟨4878657747427184863371685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6504876996569579817828913 4878657747427184863371685)
                  ·
                    refine ⟨914748327642597161882191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878657747427184863371685 914748327642597161882191)
                    ·
                      rfl

theorem cell22_2672199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2672199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672199 prefixEnd_2672199 := by exact prefixLift 2672199
  have htrace : WordTrace (prefixWord ++ tailWord_2672199) baseStart_2672199 baseEnd_2672199 := by
    simpa [prefixWord, tailWord_2672199, baseEnd_2672199] using wordTrace_append hprefix tailTrace_2672199
  have hstable : (prefixWord ++ tailWord_2672199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672199).length < 2 ^ (prefixWord ++ tailWord_2672199).sum := by decide
  have hdescent : baseEnd_2672199 < baseStart_2672199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672263 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2672263 : Nat := 118140960795 + 2672263 * 2 ^ 59
def prefixEnd_2672263 : Nat := 4983230072969 + 3 ^ 40 * 2672263 * 2
def baseEnd_2672263 : Nat := 914770236150522328281995

theorem tailTrace_2672263 : CollatzResearch.WordTrace tailWord_2672263 prefixEnd_2672263 914770236150522328281995 := by
  unfold tailWord_2672263
  simp only [CollatzResearch.WordTrace]
  refine ⟨97465438717855012030749443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64976959145236674687166295 97465438717855012030749443)
  ·
    refine ⟨146198158076782518046124165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97465438717855012030749443 146198158076782518046124165)
    ·
      refine ⟨27412154639396722133648281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146198158076782518046124165 27412154639396722133648281)
      ·
        refine ⟨20559115979547541600236211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27412154639396722133648281 20559115979547541600236211)
        ·
          refine ⟨30838673969321312400354317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20559115979547541600236211 30838673969321312400354317)
          ·
            refine ⟨11564502738495492150132869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30838673969321312400354317 11564502738495492150132869)
            ·
              refine ⟨2168344263467904778149913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11564502738495492150132869 2168344263467904778149913)
              ·
                refine ⟨1626258197600928583612435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168344263467904778149913 1626258197600928583612435)
                ·
                  refine ⟨2439387296401392875418653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626258197600928583612435 2439387296401392875418653)
                  ·
                    refine ⟨914770236150522328281995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439387296401392875418653 914770236150522328281995)
                    ·
                      rfl

theorem cell22_2672263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2672263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672263 prefixEnd_2672263 := by exact prefixLift 2672263
  have htrace : WordTrace (prefixWord ++ tailWord_2672263) baseStart_2672263 baseEnd_2672263 := by
    simpa [prefixWord, tailWord_2672263, baseEnd_2672263] using wordTrace_append hprefix tailTrace_2672263
  have hstable : (prefixWord ++ tailWord_2672263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672263).length < 2 ^ (prefixWord ++ tailWord_2672263).sum := by decide
  have hdescent : baseEnd_2672263 < baseStart_2672263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672289 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2672289 : Nat := 118140960795 + 2672289 * 2 ^ 59
def prefixEnd_2672289 : Nat := 4983230072969 + 3 ^ 40 * 2672289 * 2
def baseEnd_2672289 : Nat := 914779136481866927131915

theorem tailTrace_2672289 : CollatzResearch.WordTrace tailWord_2672289 prefixEnd_2672289 914779136481866927131915 := by
  unfold tailWord_2672289
  simp only [CollatzResearch.WordTrace]
  refine ⟨97466387015760818471195921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64977591343840545647463947 97466387015760818471195921)
  ·
    refine ⟨73099790261820613853396941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97466387015760818471195921 73099790261820613853396941)
    ·
      refine ⟨27412421348182730195023853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73099790261820613853396941 27412421348182730195023853)
      ·
        refine ⟨10279658005568523823133945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27412421348182730195023853 10279658005568523823133945)
        ·
          refine ⟨7709743504176392867350459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10279658005568523823133945 7709743504176392867350459)
          ·
            refine ⟨11564615256264589301025689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7709743504176392867350459 11564615256264589301025689)
            ·
              refine ⟨8673461442198441975769267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11564615256264589301025689 8673461442198441975769267)
              ·
                refine ⟨13010192163297662963653901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8673461442198441975769267 13010192163297662963653901)
                ·
                  refine ⟨4878822061236623611370213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13010192163297662963653901 4878822061236623611370213)
                  ·
                    refine ⟨914779136481866927131915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878822061236623611370213 914779136481866927131915)
                    ·
                      rfl

theorem cell22_2672289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2672289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672289 prefixEnd_2672289 := by exact prefixLift 2672289
  have htrace : WordTrace (prefixWord ++ tailWord_2672289) baseStart_2672289 baseEnd_2672289 := by
    simpa [prefixWord, tailWord_2672289, baseEnd_2672289] using wordTrace_append hprefix tailTrace_2672289
  have hstable : (prefixWord ++ tailWord_2672289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672289).length < 2 ^ (prefixWord ++ tailWord_2672289).sum := by decide
  have hdescent : baseEnd_2672289 < baseStart_2672289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672304 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_2672304 : Nat := 118140960795 + 2672304 * 2 ^ 59
def prefixEnd_2672304 : Nat := 4983230072969 + 3 ^ 40 * 2672304 * 2
def baseEnd_2672304 : Nat := 304928090429470629335623

theorem tailTrace_2672304 : CollatzResearch.WordTrace tailWord_2672304 prefixEnd_2672304 304928090429470629335623 := by
  unfold tailWord_2672304
  simp only [CollatzResearch.WordTrace]
  refine ⟨48733467055353238016495983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64977956073804317355327977 48733467055353238016495983)
  ·
    refine ⟨73100200583029857024743975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48733467055353238016495983 73100200583029857024743975)
    ·
      refine ⟨109650300874544785537115963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73100200583029857024743975 109650300874544785537115963)
      ·
        refine ⟨164475451311817178305673945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109650300874544785537115963 164475451311817178305673945)
        ·
          refine ⟨123356588483862883729255459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164475451311817178305673945 123356588483862883729255459)
          ·
            refine ⟨185034882725794325593883189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123356588483862883729255459 185034882725794325593883189)
            ·
              refine ⟨17347020255543218024426549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185034882725794325593883189 17347020255543218024426549)
              ·
                refine ⟨1626283148957176689789989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17347020255543218024426549 1626283148957176689789989)
                ·
                  refine ⟨304928090429470629335623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626283148957176689789989 304928090429470629335623)
                  ·
                    rfl

theorem cell22_2672304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_2672304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672304 prefixEnd_2672304 := by exact prefixLift 2672304
  have htrace : WordTrace (prefixWord ++ tailWord_2672304) baseStart_2672304 baseEnd_2672304 := by
    simpa [prefixWord, tailWord_2672304, baseEnd_2672304] using wordTrace_append hprefix tailTrace_2672304
  have hstable : (prefixWord ++ tailWord_2672304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672304).length < 2 ^ (prefixWord ++ tailWord_2672304).sum := by decide
  have hdescent : baseEnd_2672304 < baseStart_2672304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672306 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_2672306 : Nat := 118140960795 + 2672306 * 2 ^ 59
def prefixEnd_2672306 : Nat := 4983230072969 + 3 ^ 40 * 2672306 * 2
def baseEnd_2672306 : Nat := 914784955929284549456863

theorem tailTrace_2672306 : CollatzResearch.WordTrace tailWord_2672306 prefixEnd_2672306 914784955929284549456863 := by
  unfold tailWord_2672306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24366751764174807593641193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64978004704466153583043181 24366751764174807593641193)
  ·
    refine ⟨18275063823131105695230895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24366751764174807593641193 18275063823131105695230895)
    ·
      refine ⟨27412595734696658542846343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18275063823131105695230895 27412595734696658542846343)
      ·
        refine ⟨41118893602044987814269515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27412595734696658542846343 41118893602044987814269515)
        ·
          refine ⟨61678340403067481721404273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41118893602044987814269515 61678340403067481721404273)
          ·
            refine ⟨46258755302300611291053205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61678340403067481721404273 46258755302300611291053205)
            ·
              refine ⟨2168379154795341154268119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46258755302300611291053205 2168379154795341154268119)
              ·
                refine ⟨3252568732193011731402179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168379154795341154268119 3252568732193011731402179)
                ·
                  refine ⟨4878853098289517597103269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252568732193011731402179 4878853098289517597103269)
                  ·
                    refine ⟨914784955929284549456863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878853098289517597103269 914784955929284549456863)
                    ·
                      rfl

theorem cell22_2672306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_2672306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672306 prefixEnd_2672306 := by exact prefixLift 2672306
  have htrace : WordTrace (prefixWord ++ tailWord_2672306) baseStart_2672306 baseEnd_2672306 := by
    simpa [prefixWord, tailWord_2672306, baseEnd_2672306] using wordTrace_append hprefix tailTrace_2672306
  have hstable : (prefixWord ++ tailWord_2672306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672306).length < 2 ^ (prefixWord ++ tailWord_2672306).sum := by decide
  have hdescent : baseEnd_2672306 < baseStart_2672306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672319 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 4, 3]
def baseStart_2672319 : Nat := 118140960795 + 2672319 * 2 ^ 59
def prefixEnd_2672319 : Nat := 4983230072969 + 3 ^ 40 * 2672319 * 2
def baseEnd_2672319 : Nat := 914789406094956848881823

theorem tailTrace_2672319 : CollatzResearch.WordTrace tailWord_2672319 prefixEnd_2672319 914789406094956848881823 := by
  unfold tailWord_2672319
  simp only [CollatzResearch.WordTrace]
  refine ⟨97467481205652133594788011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64978320803768089063192007 97467481205652133594788011)
  ·
    refine ⟨146201221808478200392182017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97467481205652133594788011 146201221808478200392182017)
    ·
      refine ⟨109650916356358650294136513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146201221808478200392182017 109650916356358650294136513)
      ·
        refine ⟨82238187267268987720602385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109650916356358650294136513 82238187267268987720602385)
        ·
          refine ⟨61678640450451740790451789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82238187267268987720602385 61678640450451740790451789)
          ·
            refine ⟨23129490168919402796419421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61678640450451740790451789 23129490168919402796419421)
            ·
              refine ⟨8673558813344776048657283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23129490168919402796419421 8673558813344776048657283)
              ·
                refine ⟨13010338220017164072985925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8673558813344776048657283 13010338220017164072985925)
                ·
                  refine ⟨2439438416253218263684861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13010338220017164072985925 2439438416253218263684861)
                  ·
                    refine ⟨914789406094956848881823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439438416253218263684861 914789406094956848881823)
                    ·
                      rfl

theorem cell22_2672319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_2672319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672319 prefixEnd_2672319 := by exact prefixLift 2672319
  have htrace : WordTrace (prefixWord ++ tailWord_2672319) baseStart_2672319 baseEnd_2672319 := by
    simpa [prefixWord, tailWord_2672319, baseEnd_2672319] using wordTrace_append hprefix tailTrace_2672319
  have hstable : (prefixWord ++ tailWord_2672319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672319).length < 2 ^ (prefixWord ++ tailWord_2672319).sum := by decide
  have hdescent : baseEnd_2672319 < baseStart_2672319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672355 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 4]
def baseStart_2672355 : Nat := 118140960795 + 2672355 * 2 ^ 59
def prefixEnd_2672355 : Nat := 4983230072969 + 3 ^ 40 * 2672355 * 2
def baseEnd_2672355 : Nat := 304933909876888251660571

theorem tailTrace_2672355 : CollatzResearch.WordTrace tailWord_2672355 prefixEnd_2672355 304933909876888251660571 := by
  unfold tailWord_2672355
  simp only [CollatzResearch.WordTrace]
  refine ⟨97468794233521711743098519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64979196155681141162065679 97468794233521711743098519)
  ·
    refine ⟨146203191350282567614647779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97468794233521711743098519 146203191350282567614647779)
    ·
      refine ⟨219304787025423851421971669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146203191350282567614647779 219304787025423851421971669)
      ·
        refine ⟨5139955945908371517702461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 219304787025423851421971669 5139955945908371517702461)
        ·
          refine ⟨1927483479715639319138423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5139955945908371517702461 1927483479715639319138423)
          ·
            refine ⟨2891225219573458978707635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927483479715639319138423 2891225219573458978707635)
            ·
              refine ⟨4336837829360188468061453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891225219573458978707635 4336837829360188468061453)
              ·
                refine ⟨1626314186010070675523045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336837829360188468061453 1626314186010070675523045)
                ·
                  refine ⟨304933909876888251660571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626314186010070675523045 304933909876888251660571)
                  ·
                    rfl

theorem cell22_2672355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 4].length) (baseStart_2672355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672355 prefixEnd_2672355 := by exact prefixLift 2672355
  have htrace : WordTrace (prefixWord ++ tailWord_2672355) baseStart_2672355 baseEnd_2672355 := by
    simpa [prefixWord, tailWord_2672355, baseEnd_2672355] using wordTrace_append hprefix tailTrace_2672355
  have hstable : (prefixWord ++ tailWord_2672355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672355).length < 2 ^ (prefixWord ++ tailWord_2672355).sum := by decide
  have hdescent : baseEnd_2672355 < baseStart_2672355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672364 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_2672364 : Nat := 118140960795 + 2672364 * 2 ^ 59
def prefixEnd_2672364 : Nat := 4983230072969 + 3 ^ 40 * 2672364 * 2
def baseEnd_2672364 : Nat := 914804810514591731506685

theorem tailTrace_2672364 : CollatzResearch.WordTrace tailWord_2672364 prefixEnd_2672364 914804810514591731506685 := by
  unfold tailWord_2672364
  simp only [CollatzResearch.WordTrace]
  refine ⟨48734561245244553140088073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64979414993659404186784097 48734561245244553140088073)
  ·
    refine ⟨36550920933933414855066055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48734561245244553140088073 36550920933933414855066055)
    ·
      refine ⟨54826381400900122282599083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36550920933933414855066055 54826381400900122282599083)
      ·
        refine ⟨82239572101350183423898625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54826381400900122282599083 82239572101350183423898625)
        ·
          refine ⟨61679679076012637567923969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82239572101350183423898625 61679679076012637567923969)
          ·
            refine ⟨46259759307009478175942977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61679679076012637567923969 46259759307009478175942977)
            ·
              refine ⟨34694819480257108631957233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46259759307009478175942977 34694819480257108631957233)
              ·
                refine ⟨26021114610192831473967925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34694819480257108631957233 26021114610192831473967925)
                ·
                  refine ⟨2439479494705577950684493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26021114610192831473967925 2439479494705577950684493)
                  ·
                    refine ⟨914804810514591731506685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439479494705577950684493 914804810514591731506685)
                    ·
                      rfl

theorem cell22_2672364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_2672364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672364 prefixEnd_2672364 := by exact prefixLift 2672364
  have htrace : WordTrace (prefixWord ++ tailWord_2672364) baseStart_2672364 baseEnd_2672364 := by
    simpa [prefixWord, tailWord_2672364, baseEnd_2672364] using wordTrace_append hprefix tailTrace_2672364
  have hstable : (prefixWord ++ tailWord_2672364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672364).length < 2 ^ (prefixWord ++ tailWord_2672364).sum := by decide
  have hdescent : baseEnd_2672364 < baseStart_2672364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672372 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2672372 : Nat := 118140960795 + 2672372 * 2 ^ 59
def prefixEnd_2672372 : Nat := 4983230072969 + 3 ^ 40 * 2672372 * 2
def baseEnd_2672372 : Nat := 304935849692694125768887

theorem tailTrace_2672372 : CollatzResearch.WordTrace tailWord_2672372 prefixEnd_2672372 304935849692694125768887 := by
  unfold tailWord_2672372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48734707137230061823233685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64979609516306749097644913 48734707137230061823233685)
  ·
    refine ⟨2284439397057659147964079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48734707137230061823233685 2284439397057659147964079)
    ·
      refine ⟨3426659095586488721946119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284439397057659147964079 3426659095586488721946119)
      ·
        refine ⟨5139988643379733082919179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426659095586488721946119 5139988643379733082919179)
        ·
          refine ⟨7709982965069599624378769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139988643379733082919179 7709982965069599624378769)
          ·
            refine ⟨5782487223802199718284077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7709982965069599624378769 5782487223802199718284077)
            ·
              refine ⟨2168432708925824894356529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5782487223802199718284077 2168432708925824894356529)
              ·
                refine ⟨1626324531694368670767397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168432708925824894356529 1626324531694368670767397)
                ·
                  refine ⟨304935849692694125768887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626324531694368670767397 304935849692694125768887)
                  ·
                    rfl

theorem cell22_2672372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2672372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672372 prefixEnd_2672372 := by exact prefixLift 2672372
  have htrace : WordTrace (prefixWord ++ tailWord_2672372) baseStart_2672372 baseEnd_2672372 := by
    simpa [prefixWord, tailWord_2672372, baseEnd_2672372] using wordTrace_append hprefix tailTrace_2672372
  have hstable : (prefixWord ++ tailWord_2672372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672372).length < 2 ^ (prefixWord ++ tailWord_2672372).sum := by decide
  have hdescent : baseEnd_2672372 < baseStart_2672372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672529 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 7]
def baseStart_2672529 : Nat := 118140960795 + 2672529 * 2 ^ 59
def prefixEnd_2672529 : Nat := 4983230072969 + 3 ^ 40 * 2672529 * 2
def baseEnd_2672529 : Nat := 304953764462195433710393

theorem tailTrace_2672529 : CollatzResearch.WordTrace tailWord_2672529 prefixEnd_2672529 304953764462195433710393 := by
  unfold tailWord_2672529
  simp only [CollatzResearch.WordTrace]
  refine ⟨97475140534891339459932641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64983427023260892973288427 97475140534891339459932641)
  ·
    refine ⟨73106355401168504594949481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97475140534891339459932641 73106355401168504594949481)
    ·
      refine ⟨54829766550876378446212111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73106355401168504594949481 54829766550876378446212111)
      ·
        refine ⟨82244649826314567669318167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54829766550876378446212111 82244649826314567669318167)
        ·
          refine ⟨123366974739471851503977251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82244649826314567669318167 123366974739471851503977251)
          ·
            refine ⟨185050462109207777255965877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123366974739471851503977251 185050462109207777255965877)
            ·
              refine ⟨17348480822738229117746801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185050462109207777255965877 17348480822738229117746801)
              ·
                refine ⟨13011360617053671838310101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17348480822738229117746801 13011360617053671838310101)
                ·
                  refine ⟨304953764462195433710393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13011360617053671838310101 304953764462195433710393)
                  ·
                    rfl

theorem cell22_2672529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_2672529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672529 prefixEnd_2672529 := by exact prefixLift 2672529
  have htrace : WordTrace (prefixWord ++ tailWord_2672529) baseStart_2672529 baseEnd_2672529 := by
    simpa [prefixWord, tailWord_2672529, baseEnd_2672529] using wordTrace_append hprefix tailTrace_2672529
  have hstable : (prefixWord ++ tailWord_2672529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672529).length < 2 ^ (prefixWord ++ tailWord_2672529).sum := by decide
  have hdescent : baseEnd_2672529 < baseStart_2672529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672576 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_2672576 : Nat := 118140960795 + 2672576 * 2 ^ 59
def prefixEnd_2672576 : Nat := 4983230072969 + 3 ^ 40 * 2672576 * 2
def baseEnd_2672576 : Nat := 914877382447093845206035

theorem tailTrace_2672576 : CollatzResearch.WordTrace tailWord_2672576 prefixEnd_2672576 914877382447093845206035 := by
  unfold tailWord_2672576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48738427382860533243446791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64984569843814044324595721 48738427382860533243446791)
  ·
    refine ⟨73107641074290799865170187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48738427382860533243446791 73107641074290799865170187)
    ·
      refine ⟨109661461611436199797755281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73107641074290799865170187 109661461611436199797755281)
      ·
        refine ⟨82246096208577149848316461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109661461611436199797755281 82246096208577149848316461)
        ·
          refine ⟨30842286078216431193118673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82246096208577149848316461 30842286078216431193118673)
          ·
            refine ⟨23131714558662323394839005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30842286078216431193118673 23131714558662323394839005)
            ·
              refine ⟨8674392959498371273064627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23131714558662323394839005 8674392959498371273064627)
              ·
                refine ⟨13011589439247556909596941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8674392959498371273064627 13011589439247556909596941)
                ·
                  refine ⟨4879346039717833841098853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13011589439247556909596941 4879346039717833841098853)
                  ·
                    refine ⟨914877382447093845206035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879346039717833841098853 914877382447093845206035)
                    ·
                      rfl

theorem cell22_2672576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_2672576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672576 prefixEnd_2672576 := by exact prefixLift 2672576
  have htrace : WordTrace (prefixWord ++ tailWord_2672576) baseStart_2672576 baseEnd_2672576 := by
    simpa [prefixWord, tailWord_2672576, baseEnd_2672576] using wordTrace_append hprefix tailTrace_2672576
  have hstable : (prefixWord ++ tailWord_2672576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672576).length < 2 ^ (prefixWord ++ tailWord_2672576).sum := by decide
  have hdescent : baseEnd_2672576 < baseStart_2672576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672623 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 2, 3]
def baseStart_2672623 : Nat := 118140960795 + 2672623 * 2 ^ 59
def prefixEnd_2672623 : Nat := 4983230072969 + 3 ^ 40 * 2672623 * 2
def baseEnd_2672623 : Nat := 914893471507601389280891

theorem tailTrace_2672623 : CollatzResearch.WordTrace tailWord_2672623 prefixEnd_2672623 914893471507601389280891 := by
  unfold tailWord_2672623
  simp only [CollatzResearch.WordTrace]
  refine ⟨97478568996550793513854523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64985712664367195675903015 97478568996550793513854523)
  ·
    refine ⟨146217853494826190270781785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97478568996550793513854523 146217853494826190270781785)
    ·
      refine ⟨109663390121119642703086339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146217853494826190270781785 109663390121119642703086339)
      ·
        refine ⟨164495085181679464054629509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109663390121119642703086339 164495085181679464054629509)
        ·
          refine ⟨30842828471564899510243033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164495085181679464054629509 30842828471564899510243033)
          ·
            refine ⟨23132121353673674632682275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30842828471564899510243033 23132121353673674632682275)
            ·
              refine ⟨34698182030510511949023413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23132121353673674632682275 34698182030510511949023413)
              ·
                refine ⟨3252954565360360495220945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34698182030510511949023413 3252954565360360495220945)
                ·
                  refine ⟨2439715924020270371415709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252954565360360495220945 2439715924020270371415709)
                  ·
                    refine ⟨914893471507601389280891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439715924020270371415709 914893471507601389280891)
                    ·
                      rfl

theorem cell22_2672623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_2672623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672623 prefixEnd_2672623 := by exact prefixLift 2672623
  have htrace : WordTrace (prefixWord ++ tailWord_2672623) baseStart_2672623 baseEnd_2672623 := by
    simpa [prefixWord, tailWord_2672623, baseEnd_2672623] using wordTrace_append hprefix tailTrace_2672623
  have hstable : (prefixWord ++ tailWord_2672623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672623).length < 2 ^ (prefixWord ++ tailWord_2672623).sum := by decide
  have hdescent : baseEnd_2672623 < baseStart_2672623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672644 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2672644 : Nat := 118140960795 + 2672644 * 2 ^ 59
def prefixEnd_2672644 : Nat := 4983230072969 + 3 ^ 40 * 2672644 * 2
def baseEnd_2672644 : Nat := 914900660236764334505827

theorem tailTrace_2672644 : CollatzResearch.WordTrace tailWord_2672644 prefixEnd_2672644 914900660236764334505827 := by
  unfold tailWord_2672644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48739667464737357050184493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64986223286316476066912657 48739667464737357050184493)
  ·
    refine ⟨18277375299276508893819185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48739667464737357050184493 18277375299276508893819185)
    ·
      refine ⟨13708031474457381670364389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18277375299276508893819185 13708031474457381670364389)
      ·
        refine ⟨2570255901460759063193323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13708031474457381670364389 2570255901460759063193323)
        ·
          refine ⟨3855383852191138594789985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570255901460759063193323 3855383852191138594789985)
          ·
            refine ⟨2891537889143353946092489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855383852191138594789985 2891537889143353946092489)
            ·
              refine ⟨2168653416857515459569367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891537889143353946092489 2168653416857515459569367)
              ·
                refine ⟨3252980125286273189354051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168653416857515459569367 3252980125286273189354051)
                ·
                  refine ⟨4879470187929409784031077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252980125286273189354051 4879470187929409784031077)
                  ·
                    refine ⟨914900660236764334505827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879470187929409784031077 914900660236764334505827)
                    ·
                      rfl

theorem cell22_2672644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2672644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672644 prefixEnd_2672644 := by exact prefixLift 2672644
  have htrace : WordTrace (prefixWord ++ tailWord_2672644) baseStart_2672644 baseEnd_2672644 := by
    simpa [prefixWord, tailWord_2672644, baseEnd_2672644] using wordTrace_append hprefix tailTrace_2672644
  have hstable : (prefixWord ++ tailWord_2672644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672644).length < 2 ^ (prefixWord ++ tailWord_2672644).sum := by decide
  have hdescent : baseEnd_2672644 < baseStart_2672644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672732 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_2672732 : Nat := 118140960795 + 2672732 * 2 ^ 59
def prefixEnd_2672732 : Nat := 4983230072969 + 3 ^ 40 * 2672732 * 2
def baseEnd_2672732 : Nat := 304976928145053812768519

theorem tailTrace_2672732 : CollatzResearch.WordTrace tailWord_2672732 prefixEnd_2672732 304976928145053812768519 := by
  unfold tailWord_2672732
  simp only [CollatzResearch.WordTrace]
  refine ⟨48741272276577952564786225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64988363035437270086381633 48741272276577952564786225)
  ·
    refine ⟨36555954207433464423589669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48741272276577952564786225 36555954207433464423589669)
    ·
      refine ⟨6854241413893774579423063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36555954207433464423589669 6854241413893774579423063)
      ·
        refine ⟨10281362120840661869134595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854241413893774579423063 10281362120840661869134595)
        ·
          refine ⟨15422043181260992803701893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10281362120840661869134595 15422043181260992803701893)
          ·
            refine ⟨2891633096486436150694105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15422043181260992803701893 2891633096486436150694105)
            ·
              refine ⟨2168724822364827113020579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891633096486436150694105 2168724822364827113020579)
              ·
                refine ⟨3253087233547240669530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168724822364827113020579 3253087233547240669530869)
                ·
                  refine ⟨304976928145053812768519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3253087233547240669530869 304976928145053812768519)
                  ·
                    rfl

theorem cell22_2672732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_2672732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672732 prefixEnd_2672732 := by exact prefixLift 2672732
  have htrace : WordTrace (prefixWord ++ tailWord_2672732) baseStart_2672732 baseEnd_2672732 := by
    simpa [prefixWord, tailWord_2672732, baseEnd_2672732] using wordTrace_append hprefix tailTrace_2672732
  have hstable : (prefixWord ++ tailWord_2672732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672732).length < 2 ^ (prefixWord ++ tailWord_2672732).sum := by decide
  have hdescent : baseEnd_2672732 < baseStart_2672732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672771 : List Nat := [1, 1, 1, 3, 3, 13]
def baseStart_2672771 : Nat := 118140960795 + 2672771 * 2 ^ 59
def prefixEnd_2672771 : Nat := 4983230072969 + 3 ^ 40 * 2672771 * 2
def baseEnd_2672771 : Nat := 11295606604100967118277

theorem tailTrace_2672771 : CollatzResearch.WordTrace tailWord_2672771 prefixEnd_2672771 11295606604100967118277 := by
  unfold tailWord_2672771
  simp only [CollatzResearch.WordTrace]
  refine ⟨97483967000014614790242167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64989311333343076526828111 97483967000014614790242167)
  ·
    refine ⟨146225950500021922185363251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97483967000014614790242167 146225950500021922185363251)
    ·
      refine ⟨219338925750032883278044877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146225950500021922185363251 219338925750032883278044877)
      ·
        refine ⟨82252097156262331229266829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219338925750032883278044877 82252097156262331229266829)
        ·
          refine ⟨30844536433598374210975061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82252097156262331229266829 30844536433598374210975061)
          ·
            refine ⟨11295606604100967118277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 30844536433598374210975061 11295606604100967118277)
            ·
              rfl

theorem cell22_2672771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 13].length) (baseStart_2672771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672771 prefixEnd_2672771 := by exact prefixLift 2672771
  have htrace : WordTrace (prefixWord ++ tailWord_2672771) baseStart_2672771 baseEnd_2672771 := by
    simpa [prefixWord, tailWord_2672771, baseEnd_2672771] using wordTrace_append hprefix tailTrace_2672771
  have hstable : (prefixWord ++ tailWord_2672771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672771).length < 2 ^ (prefixWord ++ tailWord_2672771).sum := by decide
  have hdescent : baseEnd_2672771 < baseStart_2672771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672775 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 2, 3]
def baseStart_2672775 : Nat := 118140960795 + 2672775 * 2 ^ 59
def prefixEnd_2672775 : Nat := 4983230072969 + 3 ^ 40 * 2672775 * 2
def baseEnd_2672775 : Nat := 914945504213923659480425

theorem tailTrace_2672775 : CollatzResearch.WordTrace tailWord_2672775 prefixEnd_2672775 914945504213923659480425 := by
  unfold tailWord_2672775
  simp only [CollatzResearch.WordTrace]
  refine ⟨97484112892000123473387779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64989408594666748982258519 97484112892000123473387779)
  ·
    refine ⟨146226169338000185210081669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97484112892000123473387779 146226169338000185210081669)
    ·
      refine ⟨27417406750875034726890313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146226169338000185210081669 27417406750875034726890313)
      ·
        refine ⟨20563055063156276045167735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27417406750875034726890313 20563055063156276045167735)
        ·
          refine ⟨30844582594734414067751603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20563055063156276045167735 30844582594734414067751603)
          ·
            refine ⟨46266873892101621101627405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30844582594734414067751603 46266873892101621101627405)
            ·
              refine ⟨17350077709538107913110277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46266873892101621101627405 17350077709538107913110277)
              ·
                refine ⟨3253139570538395233708177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17350077709538107913110277 3253139570538395233708177)
                ·
                  refine ⟨2439854677903796425281133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253139570538395233708177 2439854677903796425281133)
                  ·
                    refine ⟨914945504213923659480425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439854677903796425281133 914945504213923659480425)
                    ·
                      rfl

theorem cell22_2672775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_2672775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672775 prefixEnd_2672775 := by exact prefixLift 2672775
  have htrace : WordTrace (prefixWord ++ tailWord_2672775) baseStart_2672775 baseEnd_2672775 := by
    simpa [prefixWord, tailWord_2672775, baseEnd_2672775] using wordTrace_append hprefix tailTrace_2672775
  have hstable : (prefixWord ++ tailWord_2672775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672775).length < 2 ^ (prefixWord ++ tailWord_2672775).sum := by decide
  have hdescent : baseEnd_2672775 < baseStart_2672775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672837 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_2672837 : Nat := 118140960795 + 2672837 * 2 ^ 59
def prefixEnd_2672837 : Nat := 4983230072969 + 3 ^ 40 * 2672837 * 2
def baseEnd_2672837 : Nat := 914966728080976164430235

theorem tailTrace_2672837 : CollatzResearch.WordTrace tailWord_2672837 prefixEnd_2672837 914966728080976164430235 := by
  unfold tailWord_2672837
  simp only [CollatzResearch.WordTrace]
  refine ⟨97486374217775508062144765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64990916145183672041429843 97486374217775508062144765)
  ·
    refine ⟨36557390331665815523304287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97486374217775508062144765 36557390331665815523304287)
    ·
      refine ⟨54836085497498723284956431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36557390331665815523304287 54836085497498723284956431)
      ·
        refine ⟨82254128246248084927434647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54836085497498723284956431 82254128246248084927434647)
        ·
          refine ⟨123381192369372127391151971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82254128246248084927434647 123381192369372127391151971)
          ·
            refine ⟨185071788554058191086727957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123381192369372127391151971 185071788554058191086727957)
            ·
              refine ⟨8675240088471477707190373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185071788554058191086727957 8675240088471477707190373)
              ·
                refine ⟨1626607516588402070098195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8675240088471477707190373 1626607516588402070098195)
                ·
                  refine ⟨2439911274882603105147293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626607516588402070098195 2439911274882603105147293)
                  ·
                    refine ⟨914966728080976164430235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439911274882603105147293 914966728080976164430235)
                    ·
                      rfl

theorem cell22_2672837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_2672837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672837 prefixEnd_2672837 := by exact prefixLift 2672837
  have htrace : WordTrace (prefixWord ++ tailWord_2672837) baseStart_2672837 baseEnd_2672837 := by
    simpa [prefixWord, tailWord_2672837, baseEnd_2672837] using wordTrace_append hprefix tailTrace_2672837
  have hstable : (prefixWord ++ tailWord_2672837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672837).length < 2 ^ (prefixWord ++ tailWord_2672837).sum := by decide
  have hdescent : baseEnd_2672837 < baseStart_2672837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672854 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2672854 : Nat := 118140960795 + 2672854 * 2 ^ 59
def prefixEnd_2672854 : Nat := 4983230072969 + 3 ^ 40 * 2672854 * 2
def baseEnd_2672854 : Nat := 914972547528393786755183

theorem tailTrace_2672854 : CollatzResearch.WordTrace tailWord_2672854 prefixEnd_2672854 914972547528393786755183 := by
  unfold tailWord_2672854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092937141169619997844601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64991329505809279977009077 6092937141169619997844601)
  ·
    refine ⟨4569702855877214998383451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6092937141169619997844601 4569702855877214998383451)
    ·
      refine ⟨6854554283815822497575177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4569702855877214998383451 6854554283815822497575177)
      ·
        refine ⟨5140915712861866873181383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6854554283815822497575177 5140915712861866873181383)
        ·
          refine ⟨7711373569292800309772075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140915712861866873181383 7711373569292800309772075)
          ·
            refine ⟨11567060353939200464658113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711373569292800309772075 11567060353939200464658113)
            ·
              refine ⟨8675295265454400348493585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11567060353939200464658113 8675295265454400348493585)
              ·
                refine ⟨6506471449090800261370189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8675295265454400348493585 6506471449090800261370189)
                ·
                  refine ⟨2439926793409050098013821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6506471449090800261370189 2439926793409050098013821)
                  ·
                    refine ⟨914972547528393786755183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439926793409050098013821 914972547528393786755183)
                    ·
                      rfl

theorem cell22_2672854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2672854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672854 prefixEnd_2672854 := by exact prefixLift 2672854
  have htrace : WordTrace (prefixWord ++ tailWord_2672854) baseStart_2672854 baseEnd_2672854 := by
    simpa [prefixWord, tailWord_2672854, baseEnd_2672854] using wordTrace_append hprefix tailTrace_2672854
  have hstable : (prefixWord ++ tailWord_2672854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672854).length < 2 ^ (prefixWord ++ tailWord_2672854).sum := by decide
  have hdescent : baseEnd_2672854 < baseStart_2672854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672871 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2672871 : Nat := 118140960795 + 2672871 * 2 ^ 59
def prefixEnd_2672871 : Nat := 4983230072969 + 3 ^ 40 * 2672871 * 2
def baseEnd_2672871 : Nat := 914978366975811409080131

theorem tailTrace_2672871 : CollatzResearch.WordTrace tailWord_2672871 prefixEnd_2672871 914978366975811409080131 := by
  unfold tailWord_2672871
  simp only [CollatzResearch.WordTrace]
  refine ⟨97487614299652331868882467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64991742866434887912588311 97487614299652331868882467)
  ·
    refine ⟨146231421449478497803323701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97487614299652331868882467 146231421449478497803323701)
    ·
      refine ⟨13709195760888609169061597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146231421449478497803323701 13709195760888609169061597)
      ·
        refine ⟨5140948410333228438398099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13709195760888609169061597 5140948410333228438398099)
        ·
          refine ⟨7711422615499842657597149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140948410333228438398099 7711422615499842657597149)
          ·
            refine ⟨2891783480812440996598931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7711422615499842657597149 2891783480812440996598931)
            ·
              refine ⟨4337675221218661494898397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891783480812440996598931 4337675221218661494898397)
              ·
                refine ⟨1626628207956998060586899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4337675221218661494898397 1626628207956998060586899)
                ·
                  refine ⟨2439942311935497090880349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626628207956998060586899 2439942311935497090880349)
                  ·
                    refine ⟨914978366975811409080131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2439942311935497090880349 914978366975811409080131)
                    ·
                      rfl

theorem cell22_2672871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2672871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672871 prefixEnd_2672871 := by exact prefixLift 2672871
  have htrace : WordTrace (prefixWord ++ tailWord_2672871) baseStart_2672871 baseEnd_2672871 := by
    simpa [prefixWord, tailWord_2672871, baseEnd_2672871] using wordTrace_append hprefix tailTrace_2672871
  have hstable : (prefixWord ++ tailWord_2672871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672871).length < 2 ^ (prefixWord ++ tailWord_2672871).sum := by decide
  have hdescent : baseEnd_2672871 < baseStart_2672871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672910 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2672910 : Nat := 118140960795 + 2672910 * 2 ^ 59
def prefixEnd_2672910 : Nat := 4983230072969 + 3 ^ 40 * 2672910 * 2
def baseEnd_2672910 : Nat := 914991717472828307355011

theorem tailTrace_2672910 : CollatzResearch.WordTrace tailWord_2672910 prefixEnd_2672910 914991717472828307355011 := by
  unfold tailWord_2672910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186129593313880191194023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64992691164340694353034789 12186129593313880191194023)
  ·
    refine ⟨18279194389970820286791035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186129593313880191194023 18279194389970820286791035)
    ·
      refine ⟨27418791584956230430186553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279194389970820286791035 27418791584956230430186553)
      ·
        refine ⟨20564093688717172822639915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27418791584956230430186553 20564093688717172822639915)
        ·
          refine ⟨30846140533075759233959873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20564093688717172822639915 30846140533075759233959873)
          ·
            refine ⟨23134605399806819425469905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30846140533075759233959873 23134605399806819425469905)
            ·
              refine ⟨17350954049855114569102429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23134605399806819425469905 17350954049855114569102429)
              ·
                refine ⟨6506607768695667963413411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17350954049855114569102429 6506607768695667963413411)
                ·
                  refine ⟨9759911653043501945120117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506607768695667963413411 9759911653043501945120117)
                  ·
                    refine ⟨914991717472828307355011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9759911653043501945120117 914991717472828307355011)
                    ·
                      rfl

theorem cell22_2672910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2672910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672910 prefixEnd_2672910 := by exact prefixLift 2672910
  have htrace : WordTrace (prefixWord ++ tailWord_2672910) baseStart_2672910 baseEnd_2672910 := by
    simpa [prefixWord, tailWord_2672910, baseEnd_2672910] using wordTrace_append hprefix tailTrace_2672910
  have hstable : (prefixWord ++ tailWord_2672910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672910).length < 2 ^ (prefixWord ++ tailWord_2672910).sum := by decide
  have hdescent : baseEnd_2672910 < baseStart_2672910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672923 : List Nat := [1, 1, 1, 1, 1, 1, 8, 8]
def baseStart_2672923 : Nat := 118140960795 + 2672923 * 2 ^ 59
def prefixEnd_2672923 : Nat := 4983230072969 + 3 ^ 40 * 2672923 * 2
def baseEnd_2672923 : Nat := 101666240848722289642219

theorem tailTrace_2672923 : CollatzResearch.WordTrace tailWord_2672923 prefixEnd_2672923 101666240848722289642219 := by
  unfold tailWord_2672923
  simp only [CollatzResearch.WordTrace]
  refine ⟨97489510895463944749775423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64993007263642629833183615 97489510895463944749775423)
  ·
    refine ⟨146234266343195917124663135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97489510895463944749775423 146234266343195917124663135)
    ·
      refine ⟨219351399514793875686994703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146234266343195917124663135 219351399514793875686994703)
      ·
        refine ⟨329027099272190813530492055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219351399514793875686994703 329027099272190813530492055)
        ·
          refine ⟨493540648908286220295738083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329027099272190813530492055 493540648908286220295738083)
          ·
            refine ⟨740310973362429330443607125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493540648908286220295738083 740310973362429330443607125)
            ·
              refine ⟨8675519219090968716136021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 740310973362429330443607125 8675519219090968716136021)
              ·
                refine ⟨101666240848722289642219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8675519219090968716136021 101666240848722289642219)
                ·
                  rfl

theorem cell22_2672923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 8].length) (baseStart_2672923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672923 prefixEnd_2672923 := by exact prefixLift 2672923
  have htrace : WordTrace (prefixWord ++ tailWord_2672923) baseStart_2672923 baseEnd_2672923 := by
    simpa [prefixWord, tailWord_2672923, baseEnd_2672923] using wordTrace_append hprefix tailTrace_2672923
  have hstable : (prefixWord ++ tailWord_2672923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672923).length < 2 ^ (prefixWord ++ tailWord_2672923).sum := by decide
  have hdescent : baseEnd_2672923 < baseStart_2672923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672946 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_2672946 : Nat := 118140960795 + 2672946 * 2 ^ 59
def prefixEnd_2672946 : Nat := 4983230072969 + 3 ^ 40 * 2672946 * 2
def baseEnd_2672946 : Nat := 305001347002845404484967

theorem tailTrace_2672946 : CollatzResearch.WordTrace tailWord_2672946 prefixEnd_2672946 305001347002845404484967 := by
  unfold tailWord_2672946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372587443595154919465673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64993566516253746451908461 24372587443595154919465673)
  ·
    refine ⟨18279440582696366189599255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24372587443595154919465673 18279440582696366189599255)
    ·
      refine ⟨27419160874044549284398883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279440582696366189599255 27419160874044549284398883)
      ·
        refine ⟨41128741311066823926598325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27419160874044549284398883 41128741311066823926598325)
        ·
          refine ⟨3855819497912514743118593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41128741311066823926598325 3855819497912514743118593)
          ·
            refine ⟨2891864623434386057338945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855819497912514743118593 2891864623434386057338945)
            ·
              refine ⟨2168898467575789543004209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891864623434386057338945 2168898467575789543004209)
              ·
                refine ⟨1626673850681842157253157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168898467575789543004209 1626673850681842157253157)
                ·
                  refine ⟨305001347002845404484967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626673850681842157253157 305001347002845404484967)
                  ·
                    rfl

theorem cell22_2672946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_2672946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672946 prefixEnd_2672946 := by exact prefixLift 2672946
  have htrace : WordTrace (prefixWord ++ tailWord_2672946) baseStart_2672946 baseEnd_2672946 := by
    simpa [prefixWord, tailWord_2672946, baseEnd_2672946] using wordTrace_append hprefix tailTrace_2672946
  have hstable : (prefixWord ++ tailWord_2672946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672946).length < 2 ^ (prefixWord ++ tailWord_2672946).sum := by decide
  have hdescent : baseEnd_2672946 < baseStart_2672946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672972 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_2672972 : Nat := 118140960795 + 2672972 * 2 ^ 59
def prefixEnd_2672972 : Nat := 4983230072969 + 3 ^ 40 * 2672972 * 2
def baseEnd_2672972 : Nat := 915012941339880812304821

theorem tailTrace_2672972 : CollatzResearch.WordTrace tailWord_2672972 prefixEnd_2672972 915012941339880812304821 := by
  unfold tailWord_2672972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48745649036143213059154585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64994198714857617412206113 48745649036143213059154585)
  ·
    refine ⟨36559236777107409794365939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48745649036143213059154585 36559236777107409794365939)
    ·
      refine ⟨54838855165661114691548909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36559236777107409794365939 54838855165661114691548909)
      ·
        refine ⟨20564570687122918009330841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54838855165661114691548909 20564570687122918009330841)
        ·
          refine ⟨15423428015342188506998131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20564570687122918009330841 15423428015342188506998131)
          ·
            refine ⟨23135142023013282760497197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15423428015342188506998131 23135142023013282760497197)
            ·
              refine ⟨8675678258629981035186449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23135142023013282760497197 8675678258629981035186449)
              ·
                refine ⟨6506758693972485776389837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8675678258629981035186449 6506758693972485776389837)
                ·
                  refine ⟨2440034510239682166146189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6506758693972485776389837 2440034510239682166146189)
                  ·
                    refine ⟨915012941339880812304821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440034510239682166146189 915012941339880812304821)
                    ·
                      rfl

theorem cell22_2672972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_2672972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2672972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2672972 prefixEnd_2672972 := by exact prefixLift 2672972
  have htrace : WordTrace (prefixWord ++ tailWord_2672972) baseStart_2672972 baseEnd_2672972 := by
    simpa [prefixWord, tailWord_2672972, baseEnd_2672972] using wordTrace_append hprefix tailTrace_2672972
  have hstable : (prefixWord ++ tailWord_2672972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672972).length < 2 ^ (prefixWord ++ tailWord_2672972).sum := by decide
  have hdescent : baseEnd_2672972 < baseStart_2672972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673002 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_2673002 : Nat := 118140960795 + 2673002 * 2 ^ 59
def prefixEnd_2673002 : Nat := 4983230072969 + 3 ^ 40 * 2673002 * 2
def baseEnd_2673002 : Nat := 305007736984323578018243

theorem tailTrace_2673002 : CollatzResearch.WordTrace tailWord_2673002 prefixEnd_2673002 305007736984323578018243 := by
  unfold tailWord_2673002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24373098065544435310475315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64994928174785160827934173 24373098065544435310475315)
  ·
    refine ⟨36559647098316652965712973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24373098065544435310475315 36559647098316652965712973)
    ·
      refine ⟨13709867661868744862142365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36559647098316652965712973 13709867661868744862142365)
      ·
        refine ⟨5141200373200779323303387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13709867661868744862142365 5141200373200779323303387)
        ·
          refine ⟨7711800559801168984955081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141200373200779323303387 7711800559801168984955081)
          ·
            refine ⟨5783850419850876738716311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711800559801168984955081 5783850419850876738716311)
            ·
              refine ⟨8675775629776315108074467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783850419850876738716311 8675775629776315108074467)
              ·
                refine ⟨13013663444664472662111701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675775629776315108074467 13013663444664472662111701)
                ·
                  refine ⟨305007736984323578018243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13013663444664472662111701 305007736984323578018243)
                  ·
                    rfl

theorem cell22_2673002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_2673002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673002 prefixEnd_2673002 := by exact prefixLift 2673002
  have htrace : WordTrace (prefixWord ++ tailWord_2673002) baseStart_2673002 baseEnd_2673002 := by
    simpa [prefixWord, tailWord_2673002, baseEnd_2673002] using wordTrace_append hprefix tailTrace_2673002
  have hstable : (prefixWord ++ tailWord_2673002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673002).length < 2 ^ (prefixWord ++ tailWord_2673002).sum := by decide
  have hdescent : baseEnd_2673002 < baseStart_2673002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673015 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2673015 : Nat := 118140960795 + 2673015 * 2 ^ 59
def prefixEnd_2673015 : Nat := 4983230072969 + 3 ^ 40 * 2673015 * 2
def baseEnd_2673015 : Nat := 915027661118643033479689

theorem tailTrace_2673015 : CollatzResearch.WordTrace tailWord_2673015 prefixEnd_2673015 915027661118643033479689 := by
  unfold tailWord_2673015
  simp only [CollatzResearch.WordTrace]
  refine ⟨97492866411130644462124499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64995244274087096308082999 97492866411130644462124499)
  ·
    refine ⟨146239299616695966693186749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97492866411130644462124499 146239299616695966693186749)
    ·
      refine ⟨54839737356260987509945031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146239299616695966693186749 54839737356260987509945031)
      ·
        refine ⟨82259606034391481264917547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54839737356260987509945031 82259606034391481264917547)
        ·
          refine ⟨123389409051587221897376321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82259606034391481264917547 123389409051587221897376321)
          ·
            refine ⟨92542056788690416423032241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123389409051587221897376321 92542056788690416423032241)
            ·
              refine ⟨69406542591517812317274181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92542056788690416423032241 69406542591517812317274181)
              ·
                refine ⟨13013726735909589809488909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69406542591517812317274181 13013726735909589809488909)
                ·
                  refine ⟨4880147525966096178558341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13013726735909589809488909 4880147525966096178558341)
                  ·
                    refine ⟨915027661118643033479689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4880147525966096178558341 915027661118643033479689)
                    ·
                      rfl

theorem cell22_2673015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2673015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673015 prefixEnd_2673015 := by exact prefixLift 2673015
  have htrace : WordTrace (prefixWord ++ tailWord_2673015) baseStart_2673015 baseEnd_2673015 := by
    simpa [prefixWord, tailWord_2673015, baseEnd_2673015] using wordTrace_append hprefix tailTrace_2673015
  have hstable : (prefixWord ++ tailWord_2673015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673015).length < 2 ^ (prefixWord ++ tailWord_2673015).sum := by decide
  have hdescent : baseEnd_2673015 < baseStart_2673015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673045 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2673045 : Nat := 118140960795 + 2673045 * 2 ^ 59
def prefixEnd_2673045 : Nat := 4983230072969 + 3 ^ 40 * 2673045 * 2
def baseEnd_2673045 : Nat := 915037930731732955229597

theorem tailTrace_2673045 : CollatzResearch.WordTrace tailWord_2673045 prefixEnd_2673045 915037930731732955229597 := by
  unfold tailWord_2673045
  simp only [CollatzResearch.WordTrace]
  refine ⟨97493960601021959585716589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64995973734014639723811059 97493960601021959585716589)
  ·
    refine ⟨36560235225383234844643721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97493960601021959585716589 36560235225383234844643721)
    ·
      refine ⟨27420176419037426133482791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36560235225383234844643721 27420176419037426133482791)
      ·
        refine ⟨41130264628556139200224187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27420176419037426133482791 41130264628556139200224187)
        ·
          refine ⟨61695396942834208800336281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41130264628556139200224187 61695396942834208800336281)
          ·
            refine ⟨46271547707125656600252211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61695396942834208800336281 46271547707125656600252211)
            ·
              refine ⟨69407321560688484900378317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46271547707125656600252211 69407321560688484900378317)
              ·
                refine ⟨26027745585258181837641869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69407321560688484900378317 26027745585258181837641869)
                ·
                  refine ⟨9760404594471818189115701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26027745585258181837641869 9760404594471818189115701)
                  ·
                    refine ⟨915037930731732955229597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9760404594471818189115701 915037930731732955229597)
                    ·
                      rfl

theorem cell22_2673045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2673045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673045 prefixEnd_2673045 := by exact prefixLift 2673045
  have htrace : WordTrace (prefixWord ++ tailWord_2673045) baseStart_2673045 baseEnd_2673045 := by
    simpa [prefixWord, tailWord_2673045, baseEnd_2673045] using wordTrace_append hprefix tailTrace_2673045
  have hstable : (prefixWord ++ tailWord_2673045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673045).length < 2 ^ (prefixWord ++ tailWord_2673045).sum := by decide
  have hdescent : baseEnd_2673045 < baseStart_2673045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673064 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_2673064 : Nat := 118140960795 + 2673064 * 2 ^ 59
def prefixEnd_2673064 : Nat := 4983230072969 + 3 ^ 40 * 2673064 * 2
def baseEnd_2673064 : Nat := 305014811606674413001513

theorem tailTrace_2673064 : CollatzResearch.WordTrace tailWord_2673064 prefixEnd_2673064 305014811606674413001513 := by
  unfold tailWord_2673064
  simp only [CollatzResearch.WordTrace]
  refine ⟨48747326793976562915329123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64996435725302083887105497 48747326793976562915329123)
  ·
    refine ⟨73120990190964844372993685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48747326793976562915329123 73120990190964844372993685)
    ·
      refine ⟨3427546415201477079984079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73120990190964844372993685 3427546415201477079984079)
      ·
        refine ⟨5141319622802215619976119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427546415201477079984079 5141319622802215619976119)
        ·
          refine ⟨7711979434203323429964179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141319622802215619976119 7711979434203323429964179)
          ·
            refine ⟨11567969151304985144946269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711979434203323429964179 11567969151304985144946269)
            ·
              refine ⟨4337988431739369429354851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11567969151304985144946269 4337988431739369429354851)
              ·
                refine ⟨6506982647609054144032277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337988431739369429354851 6506982647609054144032277)
                ·
                  refine ⟨305014811606674413001513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6506982647609054144032277 305014811606674413001513)
                  ·
                    rfl

theorem cell22_2673064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_2673064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673064 prefixEnd_2673064 := by exact prefixLift 2673064
  have htrace : WordTrace (prefixWord ++ tailWord_2673064) baseStart_2673064 baseEnd_2673064 := by
    simpa [prefixWord, tailWord_2673064, baseEnd_2673064] using wordTrace_append hprefix tailTrace_2673064
  have hstable : (prefixWord ++ tailWord_2673064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673064).length < 2 ^ (prefixWord ++ tailWord_2673064).sum := by decide
  have hdescent : baseEnd_2673064 < baseStart_2673064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673079 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 2, 3]
def baseStart_2673079 : Nat := 118140960795 + 2673079 * 2 ^ 59
def prefixEnd_2673079 : Nat := 4983230072969 + 3 ^ 40 * 2673079 * 2
def baseEnd_2673079 : Nat := 915049569626568199879493

theorem tailTrace_2673079 : CollatzResearch.WordTrace tailWord_2673079 prefixEnd_2673079 915049569626568199879493 := by
  unfold tailWord_2673079
  simp only [CollatzResearch.WordTrace]
  refine ⟨97495200682898783392454291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64996800455265855594969527 97495200682898783392454291)
  ·
    refine ⟨146242801024348175088681437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97495200682898783392454291 146242801024348175088681437)
    ·
      refine ⟨54841050384130565658255539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146242801024348175088681437 54841050384130565658255539)
      ·
        refine ⟨82261575576195848487383309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54841050384130565658255539 82261575576195848487383309)
        ·
          refine ⟨30848090841073443182768741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82261575576195848487383309 30848090841073443182768741)
          ·
            refine ⟨5784017032701270596769139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30848090841073443182768741 5784017032701270596769139)
            ·
              refine ⟨8676025549051905895153709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5784017032701270596769139 8676025549051905895153709)
              ·
                refine ⟨3253509580894464710682641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8676025549051905895153709 3253509580894464710682641)
                ·
                  refine ⟨2440132185670848533011981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253509580894464710682641 2440132185670848533011981)
                  ·
                    refine ⟨915049569626568199879493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440132185670848533011981 915049569626568199879493)
                    ·
                      rfl

theorem cell22_2673079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_2673079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673079 prefixEnd_2673079 := by exact prefixLift 2673079
  have htrace : WordTrace (prefixWord ++ tailWord_2673079) baseStart_2673079 baseEnd_2673079 := by
    simpa [prefixWord, tailWord_2673079, baseEnd_2673079] using wordTrace_append hprefix tailTrace_2673079
  have hstable : (prefixWord ++ tailWord_2673079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673079).length < 2 ^ (prefixWord ++ tailWord_2673079).sum := by decide
  have hdescent : baseEnd_2673079 < baseStart_2673079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673105 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2673105 : Nat := 118140960795 + 2673105 * 2 ^ 59
def prefixEnd_2673105 : Nat := 4983230072969 + 3 ^ 40 * 2673105 * 2
def baseEnd_2673105 : Nat := 915058469957912798729413

theorem tailTrace_2673105 : CollatzResearch.WordTrace tailWord_2673105 prefixEnd_2673105 915058469957912798729413 := by
  unfold tailWord_2673105
  simp only [CollatzResearch.WordTrace]
  refine ⟨97496148980804589832900769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64997432653869726555267179 97496148980804589832900769)
  ·
    refine ⟨73122111735603442374675577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97496148980804589832900769 73122111735603442374675577)
    ·
      refine ⟨54841583801702581781006683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73122111735603442374675577 54841583801702581781006683)
      ·
        refine ⟨82262375702553872671510025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54841583801702581781006683 82262375702553872671510025)
        ·
          refine ⟨61696781776915404503632519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82262375702553872671510025 61696781776915404503632519)
          ·
            refine ⟨92545172665373106755448779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61696781776915404503632519 92545172665373106755448779)
            ·
              refine ⟨138817758998059660133173169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92545172665373106755448779 138817758998059660133173169)
              ·
                refine ⟨104113319248544745099879877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138817758998059660133173169 104113319248544745099879877)
                ·
                  refine ⟨19521247359102139706227477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104113319248544745099879877 19521247359102139706227477)
                  ·
                    refine ⟨915058469957912798729413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19521247359102139706227477 915058469957912798729413)
                    ·
                      rfl

theorem cell22_2673105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2673105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673105 prefixEnd_2673105 := by exact prefixLift 2673105
  have htrace : WordTrace (prefixWord ++ tailWord_2673105) baseStart_2673105 baseEnd_2673105 := by
    simpa [prefixWord, tailWord_2673105, baseEnd_2673105] using wordTrace_append hprefix tailTrace_2673105
  have hstable : (prefixWord ++ tailWord_2673105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673105).length < 2 ^ (prefixWord ++ tailWord_2673105).sum := by decide
  have hdescent : baseEnd_2673105 < baseStart_2673105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673137 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 5]
def baseStart_2673137 : Nat := 118140960795 + 2673137 * 2 ^ 59
def prefixEnd_2673137 : Nat := 4983230072969 + 3 ^ 40 * 2673137 * 2
def baseEnd_2673137 : Nat := 305023141403958460643105

theorem tailTrace_2673137 : CollatzResearch.WordTrace tailWord_2673137 prefixEnd_2673137 305023141403958460643105 := by
  unfold tailWord_2673137
  simp only [CollatzResearch.WordTrace]
  refine ⟨97497316116688659298065665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64998210744459106198710443 97497316116688659298065665)
  ·
    refine ⟨73122987087516494473549249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97497316116688659298065665 73122987087516494473549249)
    ·
      refine ⟨54842240315637370855161937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73122987087516494473549249 54842240315637370855161937)
      ·
        refine ⟨41131680236728028141371453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54842240315637370855161937 41131680236728028141371453)
        ·
          refine ⟨15424380088773010553014295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41131680236728028141371453 15424380088773010553014295)
          ·
            refine ⟨23136570133159515829521443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15424380088773010553014295 23136570133159515829521443)
            ·
              refine ⟨34704855199739273744282165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23136570133159515829521443 34704855199739273744282165)
              ·
                refine ⟨3253580174975556913526453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34704855199739273744282165 3253580174975556913526453)
                ·
                  refine ⟨305023141403958460643105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3253580174975556913526453 305023141403958460643105)
                  ·
                    rfl

theorem cell22_2673137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_2673137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673137 prefixEnd_2673137 := by exact prefixLift 2673137
  have htrace : WordTrace (prefixWord ++ tailWord_2673137) baseStart_2673137 baseEnd_2673137 := by
    simpa [prefixWord, tailWord_2673137, baseEnd_2673137] using wordTrace_append hprefix tailTrace_2673137
  have hstable : (prefixWord ++ tailWord_2673137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673137).length < 2 ^ (prefixWord ++ tailWord_2673137).sum := by decide
  have hdescent : baseEnd_2673137 < baseStart_2673137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673188 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2673188 : Nat := 118140960795 + 2673188 * 2 ^ 59
def prefixEnd_2673188 : Nat := 4983230072969 + 3 ^ 40 * 2673188 * 2
def baseEnd_2673188 : Nat := 305028960851376082968053

theorem tailTrace_2673188 : CollatzResearch.WordTrace tailWord_2673188 prefixEnd_2673188 305028960851376082968053 := by
  unfold tailWord_2673188
  simp only [CollatzResearch.WordTrace]
  refine ⟨48749588119751947504086109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64999450826335930005448145 48749588119751947504086109)
  ·
    refine ⟨18281095544906980314032291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48749588119751947504086109 18281095544906980314032291)
    ·
      refine ⟨27421643317360470471048437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18281095544906980314032291 27421643317360470471048437)
      ·
        refine ⟨2570779061002544106660791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27421643317360470471048437 2570779061002544106660791)
        ·
          refine ⟨3856168591503816159991187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570779061002544106660791 3856168591503816159991187)
          ·
            refine ⟨5784252887255724239986781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856168591503816159991187 5784252887255724239986781)
            ·
              refine ⟨2169094832720896589995043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5784252887255724239986781 2169094832720896589995043)
              ·
                refine ⟨3253642249081344884992565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169094832720896589995043 3253642249081344884992565)
                ·
                  refine ⟨305028960851376082968053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3253642249081344884992565 305028960851376082968053)
                  ·
                    rfl

theorem cell22_2673188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2673188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673188 prefixEnd_2673188 := by exact prefixLift 2673188
  have htrace : WordTrace (prefixWord ++ tailWord_2673188) baseStart_2673188 baseEnd_2673188 := by
    simpa [prefixWord, tailWord_2673188, baseEnd_2673188] using wordTrace_append hprefix tailTrace_2673188
  have hstable : (prefixWord ++ tailWord_2673188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673188).length < 2 ^ (prefixWord ++ tailWord_2673188).sum := by decide
  have hdescent : baseEnd_2673188 < baseStart_2673188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673304 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_2673304 : Nat := 118140960795 + 2673304 * 2 ^ 59
def prefixEnd_2673304 : Nat := 4983230072969 + 3 ^ 40 * 2673304 * 2
def baseEnd_2673304 : Nat := 915126591724742613003803

theorem tailTrace_2673304 : CollatzResearch.WordTrace tailWord_2673304 prefixEnd_2673304 915126591724742613003803 := by
  unfold tailWord_2673304
  simp only [CollatzResearch.WordTrace]
  refine ⟨48751703553541823409697483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65002271404722431212929977 48751703553541823409697483)
  ·
    refine ⟨73127555330312735114546225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48751703553541823409697483 73127555330312735114546225)
    ·
      refine ⟨54845666497734551335909669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73127555330312735114546225 54845666497734551335909669)
      ·
        refine ⟨10283562468325228375483063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54845666497734551335909669 10283562468325228375483063)
        ·
          refine ⟨15425343702487842563224595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10283562468325228375483063 15425343702487842563224595)
          ·
            refine ⟨23138015553731763844836893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15425343702487842563224595 23138015553731763844836893)
            ·
              refine ⟨8676755832649411441813835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23138015553731763844836893 8676755832649411441813835)
              ·
                refine ⟨13015133748974117162720753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8676755832649411441813835 13015133748974117162720753)
                ·
                  refine ⟨9761350311730587872040565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13015133748974117162720753 9761350311730587872040565)
                  ·
                    refine ⟨915126591724742613003803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9761350311730587872040565 915126591724742613003803)
                    ·
                      rfl

theorem cell22_2673304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_2673304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673304 prefixEnd_2673304 := by exact prefixLift 2673304
  have htrace : WordTrace (prefixWord ++ tailWord_2673304) baseStart_2673304 baseEnd_2673304 := by
    simpa [prefixWord, tailWord_2673304, baseEnd_2673304] using wordTrace_append hprefix tailTrace_2673304
  have hstable : (prefixWord ++ tailWord_2673304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673304).length < 2 ^ (prefixWord ++ tailWord_2673304).sum := by decide
  have hdescent : baseEnd_2673304 < baseStart_2673304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673409 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2673409 : Nat := 118140960795 + 2673409 * 2 ^ 59
def prefixEnd_2673409 : Nat := 4983230072969 + 3 ^ 40 * 2673409 * 2
def baseEnd_2673409 : Nat := 915162535370557339128481

theorem tailTrace_2673409 : CollatzResearch.WordTrace tailWord_2673409 prefixEnd_2673409 915162535370557339128481 := by
  unfold tailWord_2673409
  simp only [CollatzResearch.WordTrace]
  refine ⟨97507236771703249751967281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65004824514468833167978187 97507236771703249751967281)
  ·
    refine ⟨73130427578777437313975461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97507236771703249751967281 73130427578777437313975461)
    ·
      refine ⟨13711955171020769496370399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73130427578777437313975461 13711955171020769496370399)
      ·
        refine ⟨20567932756531154244555599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13711955171020769496370399 20567932756531154244555599)
        ·
          refine ⟨30851899134796731366833399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20567932756531154244555599 30851899134796731366833399)
          ·
            refine ⟨46277848702195097050250099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30851899134796731366833399 46277848702195097050250099)
            ·
              refine ⟨69416773053292645575375149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46277848702195097050250099 69416773053292645575375149)
              ·
                refine ⟨26031289894984742090765681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69416773053292645575375149 26031289894984742090765681)
                ·
                  refine ⟨19523467421238556568074261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26031289894984742090765681 19523467421238556568074261)
                  ·
                    refine ⟨915162535370557339128481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19523467421238556568074261 915162535370557339128481)
                    ·
                      rfl

theorem cell22_2673409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2673409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673409 prefixEnd_2673409 := by exact prefixLift 2673409
  have htrace : WordTrace (prefixWord ++ tailWord_2673409) baseStart_2673409 baseEnd_2673409 := by
    simpa [prefixWord, tailWord_2673409, baseEnd_2673409] using wordTrace_append hprefix tailTrace_2673409
  have hstable : (prefixWord ++ tailWord_2673409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673409).length < 2 ^ (prefixWord ++ tailWord_2673409).sum := by decide
  have hdescent : baseEnd_2673409 < baseStart_2673409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673471 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_2673471 : Nat := 118140960795 + 2673471 * 2 ^ 59
def prefixEnd_2673471 : Nat := 4983230072969 + 3 ^ 40 * 2673471 * 2
def baseEnd_2673471 : Nat := 915183759237609844078291

theorem tailTrace_2673471 : CollatzResearch.WordTrace tailWord_2673471 prefixEnd_2673471 915183759237609844078291 := by
  unfold tailWord_2673471
  simp only [CollatzResearch.WordTrace]
  refine ⟨97509498097478634340724267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65006332064985756227149511 97509498097478634340724267)
  ·
    refine ⟨146264247146217951511086401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97509498097478634340724267 146264247146217951511086401)
    ·
      refine ⟨109698185359663463633314801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146264247146217951511086401 109698185359663463633314801)
      ·
        refine ⟨82273639019747597724986101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109698185359663463633314801 82273639019747597724986101)
        ·
          refine ⟨7713153658101337286717447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82273639019747597724986101 7713153658101337286717447)
          ·
            refine ⟨11569730487152005930076171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713153658101337286717447 11569730487152005930076171)
            ·
              refine ⟨17354595730728008895114257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11569730487152005930076171 17354595730728008895114257)
              ·
                refine ⟨13015946798046006671335693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17354595730728008895114257 13015946798046006671335693)
                ·
                  refine ⟨4880980049267252501750885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13015946798046006671335693 4880980049267252501750885)
                  ·
                    refine ⟨915183759237609844078291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4880980049267252501750885 915183759237609844078291)
                    ·
                      rfl

theorem cell22_2673471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_2673471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673471 prefixEnd_2673471 := by exact prefixLift 2673471
  have htrace : WordTrace (prefixWord ++ tailWord_2673471) baseStart_2673471 baseEnd_2673471 := by
    simpa [prefixWord, tailWord_2673471, baseEnd_2673471] using wordTrace_append hprefix tailTrace_2673471
  have hstable : (prefixWord ++ tailWord_2673471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673471).length < 2 ^ (prefixWord ++ tailWord_2673471).sum := by decide
  have hdescent : baseEnd_2673471 < baseStart_2673471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673503 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 4]
def baseStart_2673503 : Nat := 118140960795 + 2673503 * 2 ^ 59
def prefixEnd_2673503 : Nat := 4983230072969 + 3 ^ 40 * 2673503 * 2
def baseEnd_2673503 : Nat := 305064904497190809092731

theorem tailTrace_2673503 : CollatzResearch.WordTrace tailWord_2673503 prefixEnd_2673503 305064904497190809092731 := by
  unfold tailWord_2673503
  simp only [CollatzResearch.WordTrace]
  refine ⟨97510665233362703805889163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65007110155575135870592775 97510665233362703805889163)
  ·
    refine ⟨146265997850044055708833745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97510665233362703805889163 146265997850044055708833745)
    ·
      refine ⟨109699498387533041781625309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146265997850044055708833745 109699498387533041781625309)
      ·
        refine ⟨41137311895324890668109491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109699498387533041781625309 41137311895324890668109491)
        ·
          refine ⟨61705967842987336002164237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41137311895324890668109491 61705967842987336002164237)
          ·
            refine ⟨23139737941120251000811589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61705967842987336002164237 23139737941120251000811589)
            ·
              refine ⟨4338700863960047062652173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23139737941120251000811589 4338700863960047062652173)
              ·
                refine ⟨1627012823985017648494565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4338700863960047062652173 1627012823985017648494565)
                ·
                  refine ⟨305064904497190809092731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627012823985017648494565 305064904497190809092731)
                  ·
                    rfl

theorem cell22_2673503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 4].length) (baseStart_2673503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673503 prefixEnd_2673503 := by exact prefixLift 2673503
  have htrace : WordTrace (prefixWord ++ tailWord_2673503) baseStart_2673503 baseEnd_2673503 := by
    simpa [prefixWord, tailWord_2673503, baseEnd_2673503] using wordTrace_append hprefix tailTrace_2673503
  have hstable : (prefixWord ++ tailWord_2673503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673503).length < 2 ^ (prefixWord ++ tailWord_2673503).sum := by decide
  have hdescent : baseEnd_2673503 < baseStart_2673503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673516 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_2673516 : Nat := 118140960795 + 2673516 * 2 ^ 59
def prefixEnd_2673516 : Nat := 4983230072969 + 3 ^ 40 * 2673516 * 2
def baseEnd_2673516 : Nat := 915199163657244726703153

theorem tailTrace_2673516 : CollatzResearch.WordTrace tailWord_2673516 prefixEnd_2673516 915199163657244726703153 := by
  unfold tailWord_2673516
  simp only [CollatzResearch.WordTrace]
  refine ⟨48755569691157803513056201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65007426254877071350741601 48755569691157803513056201)
  ·
    refine ⟨36566677268368352634792151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48755569691157803513056201 36566677268368352634792151)
    ·
      refine ⟨54850015902552528952188227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36566677268368352634792151 54850015902552528952188227)
      ·
        refine ⟨82275023853828793428282341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54850015902552528952188227 82275023853828793428282341)
        ·
          refine ⟨15426566972592898767802939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82275023853828793428282341 15426566972592898767802939)
          ·
            refine ⟨23139850458889348151704409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15426566972592898767802939 23139850458889348151704409)
            ·
              refine ⟨17354887844167011113778307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23139850458889348151704409 17354887844167011113778307)
              ·
                refine ⟨26032331766250516670667461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17354887844167011113778307 26032331766250516670667461)
                ·
                  refine ⟨4881062206171971875750149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26032331766250516670667461 4881062206171971875750149)
                  ·
                    refine ⟨915199163657244726703153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4881062206171971875750149 915199163657244726703153)
                    ·
                      rfl

theorem cell22_2673516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_2673516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673516 prefixEnd_2673516 := by exact prefixLift 2673516
  have htrace : WordTrace (prefixWord ++ tailWord_2673516) baseStart_2673516 baseEnd_2673516 := by
    simpa [prefixWord, tailWord_2673516, baseEnd_2673516] using wordTrace_append hprefix tailTrace_2673516
  have hstable : (prefixWord ++ tailWord_2673516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673516).length < 2 ^ (prefixWord ++ tailWord_2673516).sum := by decide
  have hdescent : baseEnd_2673516 < baseStart_2673516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673554 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_2673554 : Nat := 118140960795 + 2673554 * 2 ^ 59
def prefixEnd_2673554 : Nat := 4983230072969 + 3 ^ 40 * 2673554 * 2
def baseEnd_2673554 : Nat := 305070723944608431417679

theorem tailTrace_2673554 : CollatzResearch.WordTrace tailWord_2673554 prefixEnd_2673554 305070723944608431417679 := by
  unfold tailWord_2673554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378131339044484878998929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65008350237451959677330477 24378131339044484878998929)
  ·
    refine ⟨18283598504283363659249197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24378131339044484878998929 18283598504283363659249197)
    ·
      refine ⟨6856349439106261372218449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18283598504283363659249197 6856349439106261372218449)
      ·
        refine ⟨5142262079329696029163837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6856349439106261372218449 5142262079329696029163837)
        ·
          refine ⟨1928348279748636010936439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5142262079329696029163837 1928348279748636010936439)
          ·
            refine ⟨2892522419622954016404659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928348279748636010936439 2892522419622954016404659)
            ·
              refine ⟨4338783629434431024606989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892522419622954016404659 4338783629434431024606989)
              ·
                refine ⟨1627043861037911634227621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4338783629434431024606989 1627043861037911634227621)
                ·
                  refine ⟨305070723944608431417679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627043861037911634227621 305070723944608431417679)
                  ·
                    rfl

theorem cell22_2673554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_2673554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673554 prefixEnd_2673554 := by exact prefixLift 2673554
  have htrace : WordTrace (prefixWord ++ tailWord_2673554) baseStart_2673554 baseEnd_2673554 := by
    simpa [prefixWord, tailWord_2673554, baseEnd_2673554] using wordTrace_append hprefix tailTrace_2673554
  have hstable : (prefixWord ++ tailWord_2673554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673554).length < 2 ^ (prefixWord ++ tailWord_2673554).sum := by decide
  have hdescent : baseEnd_2673554 < baseStart_2673554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673591 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2673591 : Nat := 118140960795 + 2673591 * 2 ^ 59
def prefixEnd_2673591 : Nat := 4983230072969 + 3 ^ 40 * 2673591 * 2
def baseEnd_2673591 : Nat := 915224837689969531077923

theorem tailTrace_2673591 : CollatzResearch.WordTrace tailWord_2673591 prefixEnd_2673591 915224837689969531077923 := by
  unfold tailWord_2673591
  simp only [CollatzResearch.WordTrace]
  refine ⟨97513874857043894835092627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65009249904695929890061751 97513874857043894835092627)
  ·
    refine ⟨146270812285565842252638941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97513874857043894835092627 146270812285565842252638941)
    ·
      refine ⟨54851554607087190844739603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146270812285565842252638941 54851554607087190844739603)
      ·
        refine ⟨82277331910630786267109405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54851554607087190844739603 82277331910630786267109405)
        ·
          refine ⟨30853999466486544850166027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82277331910630786267109405 30853999466486544850166027)
          ·
            refine ⟨46280999199729817275249041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30853999466486544850166027 46280999199729817275249041)
            ·
              refine ⟨34710749399797362956436781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46280999199729817275249041 34710749399797362956436781)
              ·
                refine ⟨13016531024924011108663793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34710749399797362956436781 13016531024924011108663793)
                ·
                  refine ⟨9762398268693008331497845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13016531024924011108663793 9762398268693008331497845)
                  ·
                    refine ⟨915224837689969531077923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9762398268693008331497845 915224837689969531077923)
                    ·
                      rfl

theorem cell22_2673591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2673591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673591 prefixEnd_2673591 := by exact prefixLift 2673591
  have htrace : WordTrace (prefixWord ++ tailWord_2673591) baseStart_2673591 baseEnd_2673591 := by
    simpa [prefixWord, tailWord_2673591, baseEnd_2673591] using wordTrace_append hprefix tailTrace_2673591
  have hstable : (prefixWord ++ tailWord_2673591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673591).length < 2 ^ (prefixWord ++ tailWord_2673591).sum := by decide
  have hdescent : baseEnd_2673591 < baseStart_2673591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673593 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 5]
def baseStart_2673593 : Nat := 118140960795 + 2673593 * 2 ^ 59
def prefixEnd_2673593 : Nat := 4983230072969 + 3 ^ 40 * 2673593 * 2
def baseEnd_2673593 : Nat := 305075174110280730842639

theorem tailTrace_2673593 : CollatzResearch.WordTrace tailWord_2673593 prefixEnd_2673593 305075174110280730842639 := by
  unfold tailWord_2673593
  simp only [CollatzResearch.WordTrace]
  refine ⟨97513947803036649176665433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65009298535357766117776955 97513947803036649176665433)
  ·
    refine ⟨73135460852277486882499075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97513947803036649176665433 73135460852277486882499075)
    ·
      refine ⟨109703191278416230323748613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73135460852277486882499075 109703191278416230323748613)
      ·
        refine ⟨20569348364703043185702865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109703191278416230323748613 20569348364703043185702865)
        ·
          refine ⟨15427011273527282389277149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20569348364703043185702865 15427011273527282389277149)
          ·
            refine ⟨5785129227572730895978931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15427011273527282389277149 5785129227572730895978931)
            ·
              refine ⟨8677693841359096343968397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785129227572730895978931 8677693841359096343968397)
              ·
                refine ⟨3254135190509661128988149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8677693841359096343968397 3254135190509661128988149)
                ·
                  refine ⟨305075174110280730842639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3254135190509661128988149 305075174110280730842639)
                  ·
                    rfl

theorem cell22_2673593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_2673593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673593 prefixEnd_2673593 := by exact prefixLift 2673593
  have htrace : WordTrace (prefixWord ++ tailWord_2673593) baseStart_2673593 baseEnd_2673593 := by
    simpa [prefixWord, tailWord_2673593, baseEnd_2673593] using wordTrace_append hprefix tailTrace_2673593
  have hstable : (prefixWord ++ tailWord_2673593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673593).length < 2 ^ (prefixWord ++ tailWord_2673593).sum := by decide
  have hdescent : baseEnd_2673593 < baseStart_2673593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673631 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 1, 3]
def baseStart_2673631 : Nat := 118140960795 + 2673631 * 2 ^ 59
def prefixEnd_2673631 : Nat := 4983230072969 + 3 ^ 40 * 2673631 * 2
def baseEnd_2673631 : Nat := 915238530507422760077801

theorem tailTrace_2673631 : CollatzResearch.WordTrace tailWord_2673631 prefixEnd_2673631 915238530507422760077801 := by
  unfold tailWord_2673631
  simp only [CollatzResearch.WordTrace]
  refine ⟨97515333776898981666548747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65010222517932654444365831 97515333776898981666548747)
  ·
    refine ⟨146273000665348472499823121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97515333776898981666548747 146273000665348472499823121)
    ·
      refine ⟨109704750499011354374867341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146273000665348472499823121 109704750499011354374867341)
      ·
        refine ⟨41139281437129257890575253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109704750499011354374867341 41139281437129257890575253)
        ·
          refine ⟨1928403817365433963620715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41139281437129257890575253 1928403817365433963620715)
          ·
            refine ⟨2892605726048150945431073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928403817365433963620715 2892605726048150945431073)
            ·
              refine ⟨2169454294536113209073305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892605726048150945431073 2169454294536113209073305)
              ·
                refine ⟨1627090720902084906804979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169454294536113209073305 1627090720902084906804979)
                ·
                  refine ⟨2440636081353127360207469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627090720902084906804979 2440636081353127360207469)
                  ·
                    refine ⟨915238530507422760077801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440636081353127360207469 915238530507422760077801)
                    ·
                      rfl

theorem cell22_2673631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_2673631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673631 prefixEnd_2673631 := by exact prefixLift 2673631
  have htrace : WordTrace (prefixWord ++ tailWord_2673631) baseStart_2673631 baseEnd_2673631 := by
    simpa [prefixWord, tailWord_2673631, baseEnd_2673631] using wordTrace_append hprefix tailTrace_2673631
  have hstable : (prefixWord ++ tailWord_2673631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673631).length < 2 ^ (prefixWord ++ tailWord_2673631).sum := by decide
  have hdescent : baseEnd_2673631 < baseStart_2673631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673681 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2673681 : Nat := 118140960795 + 2673681 * 2 ^ 59
def prefixEnd_2673681 : Nat := 4983230072969 + 3 ^ 40 * 2673681 * 2
def baseEnd_2673681 : Nat := 915255646529239296327647

theorem tailTrace_2673681 : CollatzResearch.WordTrace tailWord_2673681 prefixEnd_2673681 915255646529239296327647 := by
  unfold tailWord_2673681
  simp only [CollatzResearch.WordTrace]
  refine ⟨97517157426717840205868897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65011438284478560137245931 97517157426717840205868897)
  ·
    refine ⟨73137868070038380154401673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97517157426717840205868897 73137868070038380154401673)
    ·
      refine ⟨54853401052528785115801255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73137868070038380154401673 54853401052528785115801255)
      ·
        refine ⟨82280101578793177673701883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54853401052528785115801255 82280101578793177673701883)
        ·
          refine ⟨123420152368189766510552825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82280101578793177673701883 123420152368189766510552825)
          ·
            refine ⟨92565114276142324882914619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123420152368189766510552825 92565114276142324882914619)
            ·
              refine ⟨138847671414213487324371929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92565114276142324882914619 138847671414213487324371929)
              ·
                refine ⟨104135753560660115493278947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138847671414213487324371929 104135753560660115493278947)
                ·
                  refine ⟨156203630340990173239918421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104135753560660115493278947 156203630340990173239918421)
                  ·
                    refine ⟨915255646529239296327647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156203630340990173239918421 915255646529239296327647)
                    ·
                      rfl

theorem cell22_2673681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2673681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673681 prefixEnd_2673681 := by exact prefixLift 2673681
  have htrace : WordTrace (prefixWord ++ tailWord_2673681) baseStart_2673681 baseEnd_2673681 := by
    simpa [prefixWord, tailWord_2673681, baseEnd_2673681] using wordTrace_append hprefix tailTrace_2673681
  have hstable : (prefixWord ++ tailWord_2673681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673681).length < 2 ^ (prefixWord ++ tailWord_2673681).sum := by decide
  have hdescent : baseEnd_2673681 < baseStart_2673681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673687 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 2, 3]
def baseStart_2673687 : Nat := 118140960795 + 2673687 * 2 ^ 59
def prefixEnd_2673687 : Nat := 4983230072969 + 3 ^ 40 * 2673687 * 2
def baseEnd_2673687 : Nat := 915257700451857280677629

theorem tailTrace_2673687 : CollatzResearch.WordTrace tailWord_2673687 prefixEnd_2673687 915257700451857280677629 := by
  unfold tailWord_2673687
  simp only [CollatzResearch.WordTrace]
  refine ⟨97517376264696103230587315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65011584176464068820391543 97517376264696103230587315)
  ·
    refine ⟨146276064397044154845880973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97517376264696103230587315 146276064397044154845880973)
    ·
      refine ⟨54853524148891558067205365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146276064397044154845880973 54853524148891558067205365)
      ·
        refine ⟨5142517888958583568800503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54853524148891558067205365 5142517888958583568800503)
        ·
          refine ⟨7713776833437875353200755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142517888958583568800503 7713776833437875353200755)
          ·
            refine ⟨11570665250156813029801133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713776833437875353200755 11570665250156813029801133)
            ·
              refine ⟨4338999468808804886175425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11570665250156813029801133 4338999468808804886175425)
              ·
                refine ⟨3254249601606603664631569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338999468808804886175425 3254249601606603664631569)
                ·
                  refine ⟨2440687201204952748473677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254249601606603664631569 2440687201204952748473677)
                  ·
                    refine ⟨915257700451857280677629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440687201204952748473677 915257700451857280677629)
                    ·
                      rfl

theorem cell22_2673687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_2673687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673687 prefixEnd_2673687 := by exact prefixLift 2673687
  have htrace : WordTrace (prefixWord ++ tailWord_2673687) baseStart_2673687 baseEnd_2673687 := by
    simpa [prefixWord, tailWord_2673687, baseEnd_2673687] using wordTrace_append hprefix tailTrace_2673687
  have hstable : (prefixWord ++ tailWord_2673687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673687).length < 2 ^ (prefixWord ++ tailWord_2673687).sum := by decide
  have hdescent : baseEnd_2673687 < baseStart_2673687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673749 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2673749 : Nat := 118140960795 + 2673749 * 2 ^ 59
def prefixEnd_2673749 : Nat := 4983230072969 + 3 ^ 40 * 2673749 * 2
def baseEnd_2673749 : Nat := 915278924318909785627439

theorem tailTrace_2673749 : CollatzResearch.WordTrace tailWord_2673749 prefixEnd_2673749 915278924318909785627439 := by
  unfold tailWord_2673749
  simp only [CollatzResearch.WordTrace]
  refine ⟨97519637590471487819344301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65013091726980991879562867 97519637590471487819344301)
  ·
    refine ⟨36569864096426807932254113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97519637590471487819344301 36569864096426807932254113)
    ·
      refine ⟨27427398072320105949190585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36569864096426807932254113 27427398072320105949190585)
      ·
        refine ⟨20570548554240079461892939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27427398072320105949190585 20570548554240079461892939)
        ·
          refine ⟨30855822831360119192839409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20570548554240079461892939 30855822831360119192839409)
          ·
            refine ⟨23141867123520089394629557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30855822831360119192839409 23141867123520089394629557)
            ·
              refine ⟨2169550042830008380746521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23141867123520089394629557 2169550042830008380746521)
              ·
                refine ⟨1627162532122506285559891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169550042830008380746521 1627162532122506285559891)
                ·
                  refine ⟨2440743798183759428339837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627162532122506285559891 2440743798183759428339837)
                  ·
                    refine ⟨915278924318909785627439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440743798183759428339837 915278924318909785627439)
                    ·
                      rfl

theorem cell22_2673749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2673749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673749 prefixEnd_2673749 := by exact prefixLift 2673749
  have htrace : WordTrace (prefixWord ++ tailWord_2673749) baseStart_2673749 baseEnd_2673749 := by
    simpa [prefixWord, tailWord_2673749, baseEnd_2673749] using wordTrace_append hprefix tailTrace_2673749
  have hstable : (prefixWord ++ tailWord_2673749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673749).length < 2 ^ (prefixWord ++ tailWord_2673749).sum := by decide
  have hdescent : baseEnd_2673749 < baseStart_2673749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673762 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2673762 : Nat := 118140960795 + 2673762 * 2 ^ 59
def prefixEnd_2673762 : Nat := 4983230072969 + 3 ^ 40 * 2673762 * 2
def baseEnd_2673762 : Nat := 305094458161527361684133

theorem tailTrace_2673762 : CollatzResearch.WordTrace tailWord_2673762 prefixEnd_2673762 305094458161527361684133 := by
  unfold tailWord_2673762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24380027934856097759891885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65013407826282927359711693 24380027934856097759891885)
  ·
    refine ⟨9142510475571036659959457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24380027934856097759891885 9142510475571036659959457)
    ·
      refine ⟨6856882856678277494969593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9142510475571036659959457 6856882856678277494969593)
      ·
        refine ⟨5142662142508708121227195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6856882856678277494969593 5142662142508708121227195)
        ·
          refine ⟨7713993213763062181840793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142662142508708121227195 7713993213763062181840793)
          ·
            refine ⟨5785494910322296636380595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7713993213763062181840793 5785494910322296636380595)
            ·
              refine ⟨8678242365483444954570893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785494910322296636380595 8678242365483444954570893)
              ·
                refine ⟨3254340887056291857964085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8678242365483444954570893 3254340887056291857964085)
                ·
                  refine ⟨305094458161527361684133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3254340887056291857964085 305094458161527361684133)
                  ·
                    rfl

theorem cell22_2673762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2673762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673762 prefixEnd_2673762 := by exact prefixLift 2673762
  have htrace : WordTrace (prefixWord ++ tailWord_2673762) baseStart_2673762 baseEnd_2673762 := by
    simpa [prefixWord, tailWord_2673762, baseEnd_2673762] using wordTrace_append hprefix tailTrace_2673762
  have hstable : (prefixWord ++ tailWord_2673762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673762).length < 2 ^ (prefixWord ++ tailWord_2673762).sum := by decide
  have hdescent : baseEnd_2673762 < baseStart_2673762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673822 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2673822 : Nat := 118140960795 + 2673822 * 2 ^ 59
def prefixEnd_2673822 : Nat := 4983230072969 + 3 ^ 40 * 2673822 * 2
def baseEnd_2673822 : Nat := 915303913710761928552215

theorem tailTrace_2673822 : CollatzResearch.WordTrace tailWord_2673822 prefixEnd_2673822 915303913710761928552215 := by
  unfold tailWord_2673822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190287514900877660843965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65014866746138014191167813 12190287514900877660843965)
  ·
    refine ⟨4571357818087829122816487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12190287514900877660843965 4571357818087829122816487)
    ·
      refine ⟨6857036727131743684224731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4571357818087829122816487 6857036727131743684224731)
      ·
        refine ⟨10285555090697615526337097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857036727131743684224731 10285555090697615526337097)
        ·
          refine ⟨7714166318023211644752823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10285555090697615526337097 7714166318023211644752823)
          ·
            refine ⟨11571249477034817467129235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7714166318023211644752823 11571249477034817467129235)
            ·
              refine ⟨17356874215552226200693853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11571249477034817467129235 17356874215552226200693853)
              ·
                refine ⟨6508827830832084825260195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17356874215552226200693853 6508827830832084825260195)
                ·
                  refine ⟨9763241746248127237890293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6508827830832084825260195 9763241746248127237890293)
                  ·
                    refine ⟨915303913710761928552215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9763241746248127237890293 915303913710761928552215)
                    ·
                      rfl

theorem cell22_2673822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2673822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673822 prefixEnd_2673822 := by exact prefixLift 2673822
  have htrace : WordTrace (prefixWord ++ tailWord_2673822) baseStart_2673822 baseEnd_2673822 := by
    simpa [prefixWord, tailWord_2673822, baseEnd_2673822] using wordTrace_append hprefix tailTrace_2673822
  have hstable : (prefixWord ++ tailWord_2673822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673822).length < 2 ^ (prefixWord ++ tailWord_2673822).sum := by decide
  have hdescent : baseEnd_2673822 < baseStart_2673822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673837 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2673837 : Nat := 118140960795 + 2673837 * 2 ^ 59
def prefixEnd_2673837 : Nat := 4983230072969 + 3 ^ 40 * 2673837 * 2
def baseEnd_2673837 : Nat := 915309048517306889427169

theorem tailTrace_2673837 : CollatzResearch.WordTrace tailWord_2673837 prefixEnd_2673837 915309048517306889427169 := by
  unfold tailWord_2673837
  simp only [CollatzResearch.WordTrace]
  refine ⟨97522847214152678848547765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65015231476101785899031843 97522847214152678848547765)
  ·
    refine ⟨9142766926326813642051353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97522847214152678848547765 9142766926326813642051353)
    ·
      refine ⟨6857075194745110231538515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9142766926326813642051353 6857075194745110231538515)
      ·
        refine ⟨10285612792117665347307773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857075194745110231538515 10285612792117665347307773)
        ·
          refine ⟨3857104797044124505240415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10285612792117665347307773 3857104797044124505240415)
          ·
            refine ⟨5785657195566186757860623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857104797044124505240415 5785657195566186757860623)
            ·
              refine ⟨8678485793349280136790935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785657195566186757860623 8678485793349280136790935)
              ·
                refine ⟨13017728690023920205186403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8678485793349280136790935 13017728690023920205186403)
                ·
                  refine ⟨19526593035035880307779605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017728690023920205186403 19526593035035880307779605)
                  ·
                    refine ⟨915309048517306889427169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19526593035035880307779605 915309048517306889427169)
                    ·
                      rfl

theorem cell22_2673837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2673837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673837 prefixEnd_2673837 := by exact prefixLift 2673837
  have htrace : WordTrace (prefixWord ++ tailWord_2673837) baseStart_2673837 baseEnd_2673837 := by
    simpa [prefixWord, tailWord_2673837, baseEnd_2673837] using wordTrace_append hprefix tailTrace_2673837
  have hstable : (prefixWord ++ tailWord_2673837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673837).length < 2 ^ (prefixWord ++ tailWord_2673837).sum := by decide
  have hdescent : baseEnd_2673837 < baseStart_2673837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673848 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2673848 : Nat := 118140960795 + 2673848 * 2 ^ 59
def prefixEnd_2673848 : Nat := 4983230072969 + 3 ^ 40 * 2673848 * 2
def baseEnd_2673848 : Nat := 915312814042106527402135

theorem tailTrace_2673848 : CollatzResearch.WordTrace tailWord_2673848 prefixEnd_2673848 915312814042106527402135 := by
  unfold tailWord_2673848
  simp only [CollatzResearch.WordTrace]
  refine ⟨48761624208556413863599099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65015498944741885151465465 48761624208556413863599099)
  ·
    refine ⟨73142436312834620795398649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48761624208556413863599099 73142436312834620795398649)
    ·
      refine ⟨54856827234625965596548987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73142436312834620795398649 54856827234625965596548987)
      ·
        refine ⟨82285240851938948394823481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54856827234625965596548987 82285240851938948394823481)
        ·
          refine ⟨61713930638954211296117611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82285240851938948394823481 61713930638954211296117611)
          ·
            refine ⟨92570895958431316944176417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61713930638954211296117611 92570895958431316944176417)
            ·
              refine ⟨69428171968823487708132313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92570895958431316944176417 69428171968823487708132313)
              ·
                refine ⟨52071128976617615781099235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69428171968823487708132313 52071128976617615781099235)
                ·
                  refine ⟨78106693464926423671648853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52071128976617615781099235 78106693464926423671648853)
                  ·
                    refine ⟨915312814042106527402135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78106693464926423671648853 915312814042106527402135)
                    ·
                      rfl

theorem cell22_2673848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2673848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673848 prefixEnd_2673848 := by exact prefixLift 2673848
  have htrace : WordTrace (prefixWord ++ tailWord_2673848) baseStart_2673848 baseEnd_2673848 := by
    simpa [prefixWord, tailWord_2673848, baseEnd_2673848] using wordTrace_append hprefix tailTrace_2673848
  have hstable : (prefixWord ++ tailWord_2673848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673848).length < 2 ^ (prefixWord ++ tailWord_2673848).sum := by decide
  have hdescent : baseEnd_2673848 < baseStart_2673848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673850 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_2673850 : Nat := 118140960795 + 2673850 * 2 ^ 59
def prefixEnd_2673850 : Nat := 4983230072969 + 3 ^ 40 * 2673850 * 2
def baseEnd_2673850 : Nat := 915313498682979188852129

theorem tailTrace_2673850 : CollatzResearch.WordTrace tailWord_2673850 prefixEnd_2673850 915313498682979188852129 := by
  unfold tailWord_2673850
  simp only [CollatzResearch.WordTrace]
  refine ⟨24380830340776395517192751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65015547575403721379180669 24380830340776395517192751)
  ·
    refine ⟨36571245511164593275789127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24380830340776395517192751 36571245511164593275789127)
    ·
      refine ⟨54856868266746889913683691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36571245511164593275789127 54856868266746889913683691)
      ·
        refine ⟨82285302400120334870525537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54856868266746889913683691 82285302400120334870525537)
        ·
          refine ⟨61713976800090251152894153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82285302400120334870525537 61713976800090251152894153)
          ·
            refine ⟨46285482600067688364670615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61713976800090251152894153 46285482600067688364670615)
            ·
              refine ⟨69428223900101532547005923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46285482600067688364670615 69428223900101532547005923)
              ·
                refine ⟨104142335850152298820508885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69428223900101532547005923 104142335850152298820508885)
                ·
                  refine ⟨2440835996487944503605677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104142335850152298820508885 2440835996487944503605677)
                  ·
                    refine ⟨915313498682979188852129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440835996487944503605677 915313498682979188852129)
                    ·
                      rfl

theorem cell22_2673850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_2673850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673850 prefixEnd_2673850 := by exact prefixLift 2673850
  have htrace : WordTrace (prefixWord ++ tailWord_2673850) baseStart_2673850 baseEnd_2673850 := by
    simpa [prefixWord, tailWord_2673850, baseEnd_2673850] using wordTrace_append hprefix tailTrace_2673850
  have hstable : (prefixWord ++ tailWord_2673850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673850).length < 2 ^ (prefixWord ++ tailWord_2673850).sum := by decide
  have hdescent : baseEnd_2673850 < baseStart_2673850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673856 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_2673856 : Nat := 118140960795 + 2673856 * 2 ^ 59
def prefixEnd_2673856 : Nat := 4983230072969 + 3 ^ 40 * 2673856 * 2
def baseEnd_2673856 : Nat := 915315552605597173202111

theorem tailTrace_2673856 : CollatzResearch.WordTrace tailWord_2673856 prefixEnd_2673856 915315552605597173202111 := by
  unfold tailWord_2673856
  simp only [CollatzResearch.WordTrace]
  refine ⟨48761770100541922546744711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65015693467389230062326281 48761770100541922546744711)
  ·
    refine ⟨73142655150812883820117067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48761770100541922546744711 73142655150812883820117067)
    ·
      refine ⟨109713982726219325730175601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73142655150812883820117067 109713982726219325730175601)
      ·
        refine ⟨82285487044664494297631701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109713982726219325730175601 82285487044664494297631701)
        ·
          refine ⟨1928566102609324085100743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82285487044664494297631701 1928566102609324085100743)
          ·
            refine ⟨2892849153913986127651115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928566102609324085100743 2892849153913986127651115)
            ·
              refine ⟨4339273730870979191476673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892849153913986127651115 4339273730870979191476673)
              ·
                refine ⟨3254455298153234393607505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339273730870979191476673 3254455298153234393607505)
                ·
                  refine ⟨2440841473614925795205629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254455298153234393607505 2440841473614925795205629)
                  ·
                    refine ⟨915315552605597173202111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440841473614925795205629 915315552605597173202111)
                    ·
                      rfl

theorem cell22_2673856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_2673856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673856 prefixEnd_2673856 := by exact prefixLift 2673856
  have htrace : WordTrace (prefixWord ++ tailWord_2673856) baseStart_2673856 baseEnd_2673856 := by
    simpa [prefixWord, tailWord_2673856, baseEnd_2673856] using wordTrace_append hprefix tailTrace_2673856
  have hstable : (prefixWord ++ tailWord_2673856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673856).length < 2 ^ (prefixWord ++ tailWord_2673856).sum := by decide
  have hdescent : baseEnd_2673856 < baseStart_2673856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673901 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2673901 : Nat := 118140960795 + 2673901 * 2 ^ 59
def prefixEnd_2673901 : Nat := 4983230072969 + 3 ^ 40 * 2673901 * 2
def baseEnd_2673901 : Nat := 915330957025232055826973

theorem tailTrace_2673901 : CollatzResearch.WordTrace tailWord_2673901 prefixEnd_2673901 915330957025232055826973 := by
  unfold tailWord_2673901
  simp only [CollatzResearch.WordTrace]
  refine ⟨97525181485920817778877557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65016787657280545185918371 97525181485920817778877557)
  ·
    refine ⟨9142985764305076666769771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97525181485920817778877557 9142985764305076666769771)
    ·
      refine ⟨13714478646457615000154657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9142985764305076666769771 13714478646457615000154657)
      ·
        refine ⟨10285858984843211250115993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13714478646457615000154657 10285858984843211250115993)
        ·
          refine ⟨7714394238632408437586995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10285858984843211250115993 7714394238632408437586995)
          ·
            refine ⟨11571591357948612656380493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7714394238632408437586995 11571591357948612656380493)
            ·
              refine ⟨4339346759230729746142685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11571591357948612656380493 4339346759230729746142685)
              ·
                refine ⟨1627255034711523654803507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4339346759230729746142685 1627255034711523654803507)
                ·
                  refine ⟨2440882552067285482205261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627255034711523654803507 2440882552067285482205261)
                  ·
                    refine ⟨915330957025232055826973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440882552067285482205261 915330957025232055826973)
                    ·
                      rfl

theorem cell22_2673901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2673901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673901 prefixEnd_2673901 := by exact prefixLift 2673901
  have htrace : WordTrace (prefixWord ++ tailWord_2673901) baseStart_2673901 baseEnd_2673901 := by
    simpa [prefixWord, tailWord_2673901, baseEnd_2673901] using wordTrace_append hprefix tailTrace_2673901
  have hstable : (prefixWord ++ tailWord_2673901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673901).length < 2 ^ (prefixWord ++ tailWord_2673901).sum := by decide
  have hdescent : baseEnd_2673901 < baseStart_2673901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673918 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2673918 : Nat := 118140960795 + 2673918 * 2 ^ 59
def prefixEnd_2673918 : Nat := 4983230072969 + 3 ^ 40 * 2673918 * 2
def baseEnd_2673918 : Nat := 915336776472649678151921

theorem tailTrace_2673918 : CollatzResearch.WordTrace tailWord_2673918 prefixEnd_2673918 915336776472649678151921 := by
  unfold tailWord_2673918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190725190857403710280801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65017201017906153121497605 12190725190857403710280801)
  ·
    refine ⟨9143043893143052782710601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12190725190857403710280801 9143043893143052782710601)
    ·
      refine ⟨6857282919857289587032951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9143043893143052782710601 6857282919857289587032951)
      ·
        refine ⟨10285924379785934380549427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857282919857289587032951 10285924379785934380549427)
        ·
          refine ⟨15428886569678901570824141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10285924379785934380549427 15428886569678901570824141)
          ·
            refine ⟨5785832463629588089059053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15428886569678901570824141 5785832463629588089059053)
            ·
              refine ⟨2169687173861095533397145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5785832463629588089059053 2169687173861095533397145)
              ·
                refine ⟨1627265380395821650047859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169687173861095533397145 1627265380395821650047859)
                ·
                  refine ⟨2440898070593732475071789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627265380395821650047859 2440898070593732475071789)
                  ·
                    refine ⟨915336776472649678151921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440898070593732475071789 915336776472649678151921)
                    ·
                      rfl

theorem cell22_2673918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2673918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673918 prefixEnd_2673918 := by exact prefixLift 2673918
  have htrace : WordTrace (prefixWord ++ tailWord_2673918) baseStart_2673918 baseEnd_2673918 := by
    simpa [prefixWord, tailWord_2673918, baseEnd_2673918] using wordTrace_append hprefix tailTrace_2673918
  have hstable : (prefixWord ++ tailWord_2673918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673918).length < 2 ^ (prefixWord ++ tailWord_2673918).sum := by decide
  have hdescent : baseEnd_2673918 < baseStart_2673918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673944 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_2673944 : Nat := 118140960795 + 2673944 * 2 ^ 59
def prefixEnd_2673944 : Nat := 4983230072969 + 3 ^ 40 * 2673944 * 2
def baseEnd_2673944 : Nat := 915345676803994277001841

theorem tailTrace_2673944 : CollatzResearch.WordTrace tailWord_2673944 prefixEnd_2673944 915345676803994277001841 := by
  unfold tailWord_2673944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48763374912382518061346443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65017833216510024081795257 48763374912382518061346443)
  ·
    refine ⟨73145062368573777092019665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48763374912382518061346443 73145062368573777092019665)
    ·
      refine ⟨54858796776430332819014749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73145062368573777092019665 54858796776430332819014749)
      ·
        refine ⟨20572048791161374807130531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54858796776430332819014749 20572048791161374807130531)
        ·
          refine ⟨30858073186742062210695797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20572048791161374807130531 30858073186742062210695797)
          ·
            refine ⟨2892944361257068332252731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30858073186742062210695797 2892944361257068332252731)
            ·
              refine ⟨4339416541885602498379097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892944361257068332252731 4339416541885602498379097)
              ·
                refine ⟨3254562406414201873784323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339416541885602498379097 3254562406414201873784323)
                ·
                  refine ⟨4881843609621302810676485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254562406414201873784323 4881843609621302810676485)
                  ·
                    refine ⟨915345676803994277001841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4881843609621302810676485 915345676803994277001841)
                    ·
                      rfl

theorem cell22_2673944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_2673944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673944 prefixEnd_2673944 := by exact prefixLift 2673944
  have htrace : WordTrace (prefixWord ++ tailWord_2673944) baseStart_2673944 baseEnd_2673944 := by
    simpa [prefixWord, tailWord_2673944, baseEnd_2673944] using wordTrace_append hprefix tailTrace_2673944
  have hstable : (prefixWord ++ tailWord_2673944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673944).length < 2 ^ (prefixWord ++ tailWord_2673944).sum := by decide
  have hdescent : baseEnd_2673944 < baseStart_2673944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673957 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2673957 : Nat := 118140960795 + 2673957 * 2 ^ 59
def prefixEnd_2673957 : Nat := 4983230072969 + 3 ^ 40 * 2673957 * 2
def baseEnd_2673957 : Nat := 915350126969666576426801

theorem tailTrace_2673957 : CollatzResearch.WordTrace tailWord_2673957 prefixEnd_2673957 915350126969666576426801 := by
  unfold tailWord_2673957
  simp only [CollatzResearch.WordTrace]
  refine ⟨97527223973717939342916125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65018149315811959561944083 97527223973717939342916125)
  ·
    refine ⟨36572708990144227253593547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97527223973717939342916125 36572708990144227253593547)
    ·
      refine ⟨54859063485216340880390321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36572708990144227253593547 54859063485216340880390321)
      ·
        refine ⟨41144297613912255660292741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54859063485216340880390321 41144297613912255660292741)
        ·
          refine ⟨7714555802608547936304889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41144297613912255660292741 7714555802608547936304889)
          ·
            refine ⟨5785916851956410952228667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7714555802608547936304889 5785916851956410952228667)
            ·
              refine ⟨8678875277934616428343001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785916851956410952228667 8678875277934616428343001)
              ·
                refine ⟨6509156458450962321257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8678875277934616428343001 6509156458450962321257251)
                ·
                  refine ⟨9763734687676443481885877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509156458450962321257251 9763734687676443481885877)
                  ·
                    refine ⟨915350126969666576426801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9763734687676443481885877 915350126969666576426801)
                    ·
                      rfl

theorem cell22_2673957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2673957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673957 prefixEnd_2673957 := by exact prefixLift 2673957
  have htrace : WordTrace (prefixWord ++ tailWord_2673957) baseStart_2673957 baseEnd_2673957 := by
    simpa [prefixWord, tailWord_2673957, baseEnd_2673957] using wordTrace_append hprefix tailTrace_2673957
  have hstable : (prefixWord ++ tailWord_2673957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673957).length < 2 ^ (prefixWord ++ tailWord_2673957).sum := by decide
  have hdescent : baseEnd_2673957 < baseStart_2673957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673970 : List Nat := [3, 2, 1, 1, 4, 11]
def baseStart_2673970 : Nat := 118140960795 + 2673970 * 2 ^ 59
def prefixEnd_2673970 : Nat := 4983230072969 + 3 ^ 40 * 2673970 * 2
def baseEnd_2673970 : Nat := 11300673791794307109281

theorem tailTrace_2673970 : CollatzResearch.WordTrace tailWord_2673970 prefixEnd_2673970 11300673791794307109281 := by
  unfold tailWord_2673970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381924530667710640784841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65018465415113895042092909 24381924530667710640784841)
  ·
    refine ⟨18286443398000782980588631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24381924530667710640784841 18286443398000782980588631)
    ·
      refine ⟨27429665097001174470882947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18286443398000782980588631 27429665097001174470882947)
      ·
        refine ⟨41144497645501761706324421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27429665097001174470882947 41144497645501761706324421)
        ·
          refine ⟨7714593308531580319935829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41144497645501761706324421 7714593308531580319935829)
          ·
            refine ⟨11300673791794307109281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7714593308531580319935829 11300673791794307109281)
            ·
              rfl

theorem cell22_2673970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 11].length) (baseStart_2673970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2673970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2673970 prefixEnd_2673970 := by exact prefixLift 2673970
  have htrace : WordTrace (prefixWord ++ tailWord_2673970) baseStart_2673970 baseEnd_2673970 := by
    simpa [prefixWord, tailWord_2673970, baseEnd_2673970] using wordTrace_append hprefix tailTrace_2673970
  have hstable : (prefixWord ++ tailWord_2673970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673970).length < 2 ^ (prefixWord ++ tailWord_2673970).sum := by decide
  have hdescent : baseEnd_2673970 < baseStart_2673970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674000 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_2674000 : Nat := 118140960795 + 2674000 * 2 ^ 59
def prefixEnd_2674000 : Nat := 4983230072969 + 3 ^ 40 * 2674000 * 2
def baseEnd_2674000 : Nat := 915364846748428797601669

theorem tailTrace_2674000 : CollatzResearch.WordTrace tailWord_2674000 prefixEnd_2674000 915364846748428797601669 := by
  unfold tailWord_2674000
  simp only [CollatzResearch.WordTrace]
  refine ⟨48764396156281078843365727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65019194875041438457820969 48764396156281078843365727)
  ·
    refine ⟨73146594234421618265048591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48764396156281078843365727 73146594234421618265048591)
    ·
      refine ⟨109719891351632427397572887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73146594234421618265048591 109719891351632427397572887)
      ·
        refine ⟨164579837027448641096359331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109719891351632427397572887 164579837027448641096359331)
        ·
          refine ⟨246869755541172961644538997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164579837027448641096359331 246869755541172961644538997)
          ·
            refine ⟨23144039581984965154175531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246869755541172961644538997 23144039581984965154175531)
            ·
              refine ⟨34716059372977447731263297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23144039581984965154175531 34716059372977447731263297)
              ·
                refine ⟨26037044529733085798447473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34716059372977447731263297 26037044529733085798447473)
                ·
                  refine ⟨19527783397299814348835605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26037044529733085798447473 19527783397299814348835605)
                  ·
                    refine ⟨915364846748428797601669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19527783397299814348835605 915364846748428797601669)
                    ·
                      rfl

theorem cell22_2674000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_2674000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674000 prefixEnd_2674000 := by exact prefixLift 2674000
  have htrace : WordTrace (prefixWord ++ tailWord_2674000) baseStart_2674000 baseEnd_2674000 := by
    simpa [prefixWord, tailWord_2674000, baseEnd_2674000] using wordTrace_append hprefix tailTrace_2674000
  have hstable : (prefixWord ++ tailWord_2674000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674000).length < 2 ^ (prefixWord ++ tailWord_2674000).sum := by decide
  have hdescent : baseEnd_2674000 < baseStart_2674000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674015 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 7]
def baseStart_2674015 : Nat := 118140960795 + 2674015 * 2 ^ 59
def prefixEnd_2674015 : Nat := 4983230072969 + 3 ^ 40 * 2674015 * 2
def baseEnd_2674015 : Nat := 305123327184991252825541

theorem tailTrace_2674015 : CollatzResearch.WordTrace tailWord_2674015 prefixEnd_2674015 305123327184991252825541 := by
  unfold tailWord_2674015
  simp only [CollatzResearch.WordTrace]
  refine ⟨97529339407507815248527499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65019559605005210165684999 97529339407507815248527499)
  ·
    refine ⟨146294009111261722872791249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97529339407507815248527499 146294009111261722872791249)
    ·
      refine ⟨109720506833446292154593437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146294009111261722872791249 109720506833446292154593437)
      ·
        refine ⟨41145190062542359557972539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109720506833446292154593437 41145190062542359557972539)
        ·
          refine ⟨61717785093813539336958809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41145190062542359557972539 61717785093813539336958809)
          ·
            refine ⟨46288338820360154502719107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61717785093813539336958809 46288338820360154502719107)
            ·
              refine ⟨69432508230540231754078661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46288338820360154502719107 69432508230540231754078661)
              ·
                refine ⟨13018595293226293453889749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69432508230540231754078661 13018595293226293453889749)
                ·
                  refine ⟨305123327184991252825541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13018595293226293453889749 305123327184991252825541)
                  ·
                    rfl

theorem cell22_2674015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_2674015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674015 prefixEnd_2674015 := by exact prefixLift 2674015
  have htrace : WordTrace (prefixWord ++ tailWord_2674015) baseStart_2674015 baseEnd_2674015 := by
    simpa [prefixWord, tailWord_2674015, baseEnd_2674015] using wordTrace_append hprefix tailTrace_2674015
  have hstable : (prefixWord ++ tailWord_2674015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674015).length < 2 ^ (prefixWord ++ tailWord_2674015).sum := by decide
  have hdescent : baseEnd_2674015 < baseStart_2674015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_2674075 : Nat := 118140960795 + 2674075 * 2 ^ 59
def prefixEnd_2674075 : Nat := 4983230072969 + 3 ^ 40 * 2674075 * 2
def baseEnd_2674075 : Nat := 915390520781153601976439

theorem tailTrace_2674075 : CollatzResearch.WordTrace tailWord_2674075 prefixEnd_2674075 915390520781153601976439 := by
  unfold tailWord_2674075
  simp only [CollatzResearch.WordTrace]
  refine ⟨97531527787290445495711679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65021018524860296997141119 97531527787290445495711679)
  ·
    refine ⟨146297291680935668243567519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97531527787290445495711679 146297291680935668243567519)
    ·
      refine ⟨219445937521403502365351279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146297291680935668243567519 219445937521403502365351279)
      ·
        refine ⟨329168906282105253548026919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219445937521403502365351279 329168906282105253548026919)
        ·
          refine ⟨493753359423157880322040379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329168906282105253548026919 493753359423157880322040379)
          ·
            refine ⟨740630039134736820483060569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493753359423157880322040379 740630039134736820483060569)
            ·
              refine ⟨555472529351052615362295427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740630039134736820483060569 555472529351052615362295427)
              ·
                refine ⟨833208794026578923043443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555472529351052615362295427 833208794026578923043443141)
                ·
                  refine ⟨156226648879983548070645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833208794026578923043443141 156226648879983548070645589)
                  ·
                    refine ⟨915390520781153601976439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156226648879983548070645589 915390520781153601976439)
                    ·
                      rfl

theorem cell22_2674075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_2674075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674075 prefixEnd_2674075 := by exact prefixLift 2674075
  have htrace : WordTrace (prefixWord ++ tailWord_2674075) baseStart_2674075 baseEnd_2674075 := by
    simpa [prefixWord, tailWord_2674075, baseEnd_2674075] using wordTrace_append hprefix tailTrace_2674075
  have hstable : (prefixWord ++ tailWord_2674075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674075).length < 2 ^ (prefixWord ++ tailWord_2674075).sum := by decide
  have hdescent : baseEnd_2674075 < baseStart_2674075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674079 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 1, 4]
def baseStart_2674079 : Nat := 118140960795 + 2674079 * 2 ^ 59
def prefixEnd_2674079 : Nat := 4983230072969 + 3 ^ 40 * 2674079 * 2
def baseEnd_2674079 : Nat := 915391890062898924876427

theorem tailTrace_2674079 : CollatzResearch.WordTrace tailWord_2674079 prefixEnd_2674079 915391890062898924876427 := by
  unfold tailWord_2674079
  simp only [CollatzResearch.WordTrace]
  refine ⟨97531673679275954178857291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65021115786183969452571527 97531673679275954178857291)
  ·
    refine ⟨146297510518913931268285937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97531673679275954178857291 146297510518913931268285937)
    ·
      refine ⟨109723132889185448451214453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146297510518913931268285937 109723132889185448451214453)
      ·
        refine ⟨10286543708361135792301355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109723132889185448451214453 10286543708361135792301355)
        ·
          refine ⟨15429815562541703688452033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286543708361135792301355 15429815562541703688452033)
          ·
            refine ⟨11572361671906277766339025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15429815562541703688452033 11572361671906277766339025)
            ·
              refine ⟨8679271253929708324754269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11572361671906277766339025 8679271253929708324754269)
              ·
                refine ⟨3254726720223640621782851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8679271253929708324754269 3254726720223640621782851)
                ·
                  refine ⟨4882090080335460932674277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254726720223640621782851 4882090080335460932674277)
                  ·
                    refine ⟨915391890062898924876427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882090080335460932674277 915391890062898924876427)
                    ·
                      rfl

theorem cell22_2674079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_2674079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674079 prefixEnd_2674079 := by exact prefixLift 2674079
  have htrace : WordTrace (prefixWord ++ tailWord_2674079) baseStart_2674079 baseEnd_2674079 := by
    simpa [prefixWord, tailWord_2674079, baseEnd_2674079] using wordTrace_append hprefix tailTrace_2674079
  have hstable : (prefixWord ++ tailWord_2674079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674079).length < 2 ^ (prefixWord ++ tailWord_2674079).sum := by decide
  have hdescent : baseEnd_2674079 < baseStart_2674079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674122 : List Nat := [3, 1, 2, 1, 2, 3, 2, 8]
def baseStart_2674122 : Nat := 118140960795 + 2674122 * 2 ^ 59
def prefixEnd_2674122 : Nat := 4983230072969 + 3 ^ 40 * 2674122 * 2
def baseEnd_2674122 : Nat := 101711845537962349561255

theorem tailTrace_2674122 : CollatzResearch.WordTrace tailWord_2674122 prefixEnd_2674122 101711845537962349561255 := by
  unfold tailWord_2674122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24383310504530043130668155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65022161345413448348448413 24383310504530043130668155)
  ·
    refine ⟨36574965756795064696002233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24383310504530043130668155 36574965756795064696002233)
    ·
      refine ⟨27431224317596298522001675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36574965756795064696002233 27431224317596298522001675)
      ·
        refine ⟨41146836476394447783002513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27431224317596298522001675 41146836476394447783002513)
        ·
          refine ⟨30860127357295835837251885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41146836476394447783002513 30860127357295835837251885)
          ·
            refine ⟨11572547758985938438969457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30860127357295835837251885 11572547758985938438969457)
            ·
              refine ⟨8679410819239453829227093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11572547758985938438969457 8679410819239453829227093)
              ·
                refine ⟨101711845537962349561255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8679410819239453829227093 101711845537962349561255)
                ·
                  rfl

theorem cell22_2674122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_2674122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674122 prefixEnd_2674122 := by exact prefixLift 2674122
  have htrace : WordTrace (prefixWord ++ tailWord_2674122) baseStart_2674122 baseEnd_2674122 := by
    simpa [prefixWord, tailWord_2674122, baseEnd_2674122] using wordTrace_append hprefix tailTrace_2674122
  have hstable : (prefixWord ++ tailWord_2674122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674122).length < 2 ^ (prefixWord ++ tailWord_2674122).sum := by decide
  have hdescent : baseEnd_2674122 < baseStart_2674122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674124 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_2674124 : Nat := 118140960795 + 2674124 * 2 ^ 59
def prefixEnd_2674124 : Nat := 4983230072969 + 3 ^ 40 * 2674124 * 2
def baseEnd_2674124 : Nat := 915407294482533807501289

theorem tailTrace_2674124 : CollatzResearch.WordTrace tailWord_2674124 prefixEnd_2674124 915407294482533807501289 := by
  unfold tailWord_2674124
  simp only [CollatzResearch.WordTrace]
  refine ⟨48766657482056463432122713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65022209976075284576163617 48766657482056463432122713)
  ·
    refine ⟨36574993111542347574092035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48766657482056463432122713 36574993111542347574092035)
    ·
      refine ⟨54862489667313521361138053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36574993111542347574092035 54862489667313521361138053)
      ·
        refine ⟨10286716812621285255213385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54862489667313521361138053 10286716812621285255213385)
        ·
          refine ⟨7715037609465963941410039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10286716812621285255213385 7715037609465963941410039)
          ·
            refine ⟨11572556414198945912115059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715037609465963941410039 11572556414198945912115059)
            ·
              refine ⟨17358834621298418868172589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11572556414198945912115059 17358834621298418868172589)
              ·
                refine ⟨6509562982986907075564721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17358834621298418868172589 6509562982986907075564721)
                ·
                  refine ⟨4882172237240180306673541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6509562982986907075564721 4882172237240180306673541)
                  ·
                    refine ⟨915407294482533807501289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882172237240180306673541 915407294482533807501289)
                    ·
                      rfl

theorem cell22_2674124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_2674124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674124 prefixEnd_2674124 := by exact prefixLift 2674124
  have htrace : WordTrace (prefixWord ++ tailWord_2674124) baseStart_2674124 baseEnd_2674124 := by
    simpa [prefixWord, tailWord_2674124, baseEnd_2674124] using wordTrace_append hprefix tailTrace_2674124
  have hstable : (prefixWord ++ tailWord_2674124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674124).length < 2 ^ (prefixWord ++ tailWord_2674124).sum := by decide
  have hdescent : baseEnd_2674124 < baseStart_2674124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674152 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2674152 : Nat := 118140960795 + 2674152 * 2 ^ 59
def prefixEnd_2674152 : Nat := 4983230072969 + 3 ^ 40 * 2674152 * 2
def baseEnd_2674152 : Nat := 915416879454751067801203

theorem tailTrace_2674152 : CollatzResearch.WordTrace tailWord_2674152 prefixEnd_2674152 915416879454751067801203 := by
  unfold tailWord_2674152
  simp only [CollatzResearch.WordTrace]
  refine ⟨48767168104005743823132355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65022890805340991764176473 48767168104005743823132355)
  ·
    refine ⟨73150752156008615734698533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48767168104005743823132355 73150752156008615734698533)
    ·
      refine ⟨13715766029251615450255975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73150752156008615734698533 13715766029251615450255975)
      ·
        refine ⟨20573649043877423175383963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13715766029251615450255975 20573649043877423175383963)
        ·
          refine ⟨30860473565816134763075945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20573649043877423175383963 30860473565816134763075945)
          ·
            refine ⟨23145355174362101072306959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30860473565816134763075945 23145355174362101072306959)
            ·
              refine ⟨34718032761543151608460439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23145355174362101072306959 34718032761543151608460439)
              ·
                refine ⟨52077049142314727412690659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34718032761543151608460439 52077049142314727412690659)
                ·
                  refine ⟨78115573713472091119035989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52077049142314727412690659 78115573713472091119035989)
                  ·
                    refine ⟨915416879454751067801203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78115573713472091119035989 915416879454751067801203)
                    ·
                      rfl

theorem cell22_2674152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2674152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674152 prefixEnd_2674152 := by exact prefixLift 2674152
  have htrace : WordTrace (prefixWord ++ tailWord_2674152) baseStart_2674152 baseEnd_2674152 := by
    simpa [prefixWord, tailWord_2674152, baseEnd_2674152] using wordTrace_append hprefix tailTrace_2674152
  have hstable : (prefixWord ++ tailWord_2674152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674152).length < 2 ^ (prefixWord ++ tailWord_2674152).sum := by decide
  have hdescent : baseEnd_2674152 < baseStart_2674152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674229 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 6]
def baseStart_2674229 : Nat := 118140960795 + 2674229 * 2 ^ 59
def prefixEnd_2674229 : Nat := 4983230072969 + 3 ^ 40 * 2674229 * 2
def baseEnd_2674229 : Nat := 305147746042782844541989

theorem tailTrace_2674229 : CollatzResearch.WordTrace tailWord_2674229 prefixEnd_2674229 305147746042782844541989 := by
  unfold tailWord_2674229
  simp only [CollatzResearch.WordTrace]
  refine ⟨97537144628732529796817741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65024763085821686531211827 97537144628732529796817741)
  ·
    refine ⟨36576429235774698673806653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97537144628732529796817741 36576429235774698673806653)
    ·
      refine ⟨13716160963415512002677495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36576429235774698673806653 13716160963415512002677495)
      ·
        refine ⟨20574241445123268004016243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13716160963415512002677495 20574241445123268004016243)
        ·
          refine ⟨30861362167684902006024365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20574241445123268004016243 30861362167684902006024365)
          ·
            refine ⟨11573010812881838252259137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30861362167684902006024365 11573010812881838252259137)
            ·
              refine ⟨8679758109661378689194353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11573010812881838252259137 8679758109661378689194353)
              ·
                refine ⟨6509818582246034016895765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8679758109661378689194353 6509818582246034016895765)
                ·
                  refine ⟨305147746042782844541989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6509818582246034016895765 305147746042782844541989)
                  ·
                    rfl

theorem cell22_2674229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_2674229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674229 prefixEnd_2674229 := by exact prefixLift 2674229
  have htrace : WordTrace (prefixWord ++ tailWord_2674229) baseStart_2674229 baseEnd_2674229 := by
    simpa [prefixWord, tailWord_2674229, baseEnd_2674229] using wordTrace_append hprefix tailTrace_2674229
  have hstable : (prefixWord ++ tailWord_2674229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674229).length < 2 ^ (prefixWord ++ tailWord_2674229).sum := by decide
  have hdescent : baseEnd_2674229 < baseStart_2674229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674231 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2674231 : Nat := 118140960795 + 2674231 * 2 ^ 59
def prefixEnd_2674231 : Nat := 4983230072969 + 3 ^ 40 * 2674231 * 2
def baseEnd_2674231 : Nat := 915443922769221195075961

theorem tailTrace_2674231 : CollatzResearch.WordTrace tailWord_2674231 prefixEnd_2674231 915443922769221195075961 := by
  unfold tailWord_2674231
  simp only [CollatzResearch.WordTrace]
  refine ⟨97537217574725284138390547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65024811716483522758927031 97537217574725284138390547)
  ·
    refine ⟨146305826362087926207585821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97537217574725284138390547 146305826362087926207585821)
    ·
      refine ⟨54864684885782972327844683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146305826362087926207585821 54864684885782972327844683)
      ·
        refine ⟨82297027328674458491767025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54864684885782972327844683 82297027328674458491767025)
        ·
          refine ⟨61722770496505843868825269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82297027328674458491767025 61722770496505843868825269)
          ·
            refine ⟨5786509734047422862702369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61722770496505843868825269 5786509734047422862702369)
            ·
              refine ⟨4339882300535567147026777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5786509734047422862702369 4339882300535567147026777)
              ·
                refine ⟨3254911725401675360270083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339882300535567147026777 3254911725401675360270083)
                ·
                  refine ⟨4882367588102513040405125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254911725401675360270083 4882367588102513040405125)
                  ·
                    refine ⟨915443922769221195075961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882367588102513040405125 915443922769221195075961)
                    ·
                      rfl

theorem cell22_2674231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2674231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674231 prefixEnd_2674231 := by exact prefixLift 2674231
  have htrace : WordTrace (prefixWord ++ tailWord_2674231) baseStart_2674231 baseEnd_2674231 := by
    simpa [prefixWord, tailWord_2674231, baseEnd_2674231] using wordTrace_append hprefix tailTrace_2674231
  have hstable : (prefixWord ++ tailWord_2674231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674231).length < 2 ^ (prefixWord ++ tailWord_2674231).sum := by decide
  have hdescent : baseEnd_2674231 < baseStart_2674231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674261 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2674261 : Nat := 118140960795 + 2674261 * 2 ^ 59
def prefixEnd_2674261 : Nat := 4983230072969 + 3 ^ 40 * 2674261 * 2
def baseEnd_2674261 : Nat := 915454192382311116825869

theorem tailTrace_2674261 : CollatzResearch.WordTrace tailWord_2674261 prefixEnd_2674261 915454192382311116825869 := by
  unfold tailWord_2674261
  simp only [CollatzResearch.WordTrace]
  refine ⟨97538311764616599261982637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65025541176411066174655091 97538311764616599261982637)
  ·
    refine ⟨36576866911731224723243489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97538311764616599261982637 36576866911731224723243489)
    ·
      refine ⟨27432650183798418542432617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36576866911731224723243489 27432650183798418542432617)
      ·
        refine ⟨20574487637848813906824463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27432650183798418542432617 20574487637848813906824463)
        ·
          refine ⟨30861731456773220860236695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20574487637848813906824463 30861731456773220860236695)
          ·
            refine ⟨46292597185159831290355043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30861731456773220860236695 46292597185159831290355043)
            ·
              refine ⟨69438895777739746935532565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46292597185159831290355043 69438895777739746935532565)
              ·
                refine ⟨3254948239581550637603089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69438895777739746935532565 3254948239581550637603089)
                ·
                  refine ⟨2441211179686162978202317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254948239581550637603089 2441211179686162978202317)
                  ·
                    refine ⟨915454192382311116825869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441211179686162978202317 915454192382311116825869)
                    ·
                      rfl

theorem cell22_2674261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2674261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674261 prefixEnd_2674261 := by exact prefixLift 2674261
  have htrace : WordTrace (prefixWord ++ tailWord_2674261) baseStart_2674261 baseEnd_2674261 := by
    simpa [prefixWord, tailWord_2674261, baseEnd_2674261] using wordTrace_append hprefix tailTrace_2674261
  have hstable : (prefixWord ++ tailWord_2674261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674261).length < 2 ^ (prefixWord ++ tailWord_2674261).sum := by decide
  have hdescent : baseEnd_2674261 < baseStart_2674261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674263 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 4]
def baseStart_2674263 : Nat := 118140960795 + 2674263 * 2 ^ 59
def prefixEnd_2674263 : Nat := 4983230072969 + 3 ^ 40 * 2674263 * 2
def baseEnd_2674263 : Nat := 305151625674394592758621

theorem tailTrace_2674263 : CollatzResearch.WordTrace tailWord_2674263 prefixEnd_2674263 305151625674394592758621 := by
  unfold tailWord_2674263
  simp only [CollatzResearch.WordTrace]
  refine ⟨97538384710609353603555443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65025589807072902402370295 97538384710609353603555443)
  ·
    refine ⟨146307577065914030405333165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97538384710609353603555443 146307577065914030405333165)
    ·
      refine ⟨54865341399717761401999937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146307577065914030405333165 54865341399717761401999937)
      ·
        refine ⟨41149006049788321051499953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54865341399717761401999937 41149006049788321051499953)
        ·
          refine ⟨30861754537341240788624965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41149006049788321051499953 30861754537341240788624965)
          ·
            refine ⟨5786578975751482647867181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30861754537341240788624965 5786578975751482647867181)
            ·
              refine ⟨2169967115906805992950193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5786578975751482647867181 2169967115906805992950193)
              ·
                refine ⟨1627475336930104494712645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169967115906805992950193 1627475336930104494712645)
                ·
                  refine ⟨305151625674394592758621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627475336930104494712645 305151625674394592758621)
                  ·
                    rfl

theorem cell22_2674263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 4].length) (baseStart_2674263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674263 prefixEnd_2674263 := by exact prefixLift 2674263
  have htrace : WordTrace (prefixWord ++ tailWord_2674263) baseStart_2674263 baseEnd_2674263 := by
    simpa [prefixWord, tailWord_2674263, baseEnd_2674263] using wordTrace_append hprefix tailTrace_2674263
  have hstable : (prefixWord ++ tailWord_2674263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674263).length < 2 ^ (prefixWord ++ tailWord_2674263).sum := by decide
  have hdescent : baseEnd_2674263 < baseStart_2674263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674293 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2674293 : Nat := 118140960795 + 2674293 * 2 ^ 59
def prefixEnd_2674293 : Nat := 4983230072969 + 3 ^ 40 * 2674293 * 2
def baseEnd_2674293 : Nat := 915465146636273700025771

theorem tailTrace_2674293 : CollatzResearch.WordTrace tailWord_2674293 prefixEnd_2674293 915465146636273700025771 := by
  unfold tailWord_2674293
  simp only [CollatzResearch.WordTrace]
  refine ⟨97539478900500668727147533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65026319267000445818098355 97539478900500668727147533)
  ·
    refine ⟨36577304587687750772680325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97539478900500668727147533 36577304587687750772680325)
    ·
      refine ⟨6858244610191453269877561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36577304587687750772680325 6858244610191453269877561)
      ·
        refine ⟨5143683457643589952408171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6858244610191453269877561 5143683457643589952408171)
        ·
          refine ⟨7715525186465384928612257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143683457643589952408171 7715525186465384928612257)
          ·
            refine ⟨5786643889849038696459193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7715525186465384928612257 5786643889849038696459193)
            ·
              refine ⟨4339982917386779022344395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5786643889849038696459193 4339982917386779022344395)
              ·
                refine ⟨6509974376080168533516593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339982917386779022344395 6509974376080168533516593)
                ·
                  refine ⟨4882480782060126400137445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6509974376080168533516593 4882480782060126400137445)
                  ·
                    refine ⟨915465146636273700025771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882480782060126400137445 915465146636273700025771)
                    ·
                      rfl

theorem cell22_2674293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2674293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674293 prefixEnd_2674293 := by exact prefixLift 2674293
  have htrace : WordTrace (prefixWord ++ tailWord_2674293) baseStart_2674293 baseEnd_2674293 := by
    simpa [prefixWord, tailWord_2674293, baseEnd_2674293] using wordTrace_append hprefix tailTrace_2674293
  have hstable : (prefixWord ++ tailWord_2674293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674293).length < 2 ^ (prefixWord ++ tailWord_2674293).sum := by decide
  have hdescent : baseEnd_2674293 < baseStart_2674293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674336 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_2674336 : Nat := 118140960795 + 2674336 * 2 ^ 59
def prefixEnd_2674336 : Nat := 4983230072969 + 3 ^ 40 * 2674336 * 2
def baseEnd_2674336 : Nat := 305159955471678640400213

theorem tailTrace_2674336 : CollatzResearch.WordTrace tailWord_2674336 prefixEnd_2674336 305159955471678640400213 := by
  unfold tailWord_2674336
  simp only [CollatzResearch.WordTrace]
  refine ⟨48770523619672443535481431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65027364826229924713975241 48770523619672443535481431)
  ·
    refine ⟨73155785429508665303222147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48770523619672443535481431 73155785429508665303222147)
    ·
      refine ⟨109733678144262997954833221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73155785429508665303222147 109733678144262997954833221)
      ·
        refine ⟨20575064652049312116531229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109733678144262997954833221 20575064652049312116531229)
        ·
          refine ⟨7715649244518492043699211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20575064652049312116531229 7715649244518492043699211)
          ·
            refine ⟨11573473866777738065548817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715649244518492043699211 11573473866777738065548817)
            ·
              refine ⟨8680105400083303549161613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11573473866777738065548817 8680105400083303549161613)
              ·
                refine ⟨3255039525031238830935605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8680105400083303549161613 3255039525031238830935605)
                ·
                  refine ⟨305159955471678640400213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3255039525031238830935605 305159955471678640400213)
                  ·
                    rfl

theorem cell22_2674336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_2674336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674336 prefixEnd_2674336 := by exact prefixLift 2674336
  have htrace : WordTrace (prefixWord ++ tailWord_2674336) baseStart_2674336 baseEnd_2674336 := by
    simpa [prefixWord, tailWord_2674336, baseEnd_2674336] using wordTrace_append hprefix tailTrace_2674336
  have hstable : (prefixWord ++ tailWord_2674336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674336).length < 2 ^ (prefixWord ++ tailWord_2674336).sum := by decide
  have hdescent : baseEnd_2674336 < baseStart_2674336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674344 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2674344 : Nat := 118140960795 + 2674344 * 2 ^ 59
def prefixEnd_2674344 : Nat := 4983230072969 + 3 ^ 40 * 2674344 * 2
def baseEnd_2674344 : Nat := 915482604978526567000615

theorem tailTrace_2674344 : CollatzResearch.WordTrace tailWord_2674344 prefixEnd_2674344 915482604978526567000615 := by
  unfold tailWord_2674344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48770669511657952218627043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65027559348877269624836057 48770669511657952218627043)
  ·
    refine ⟨73156004267486928327940565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48770669511657952218627043 73156004267486928327940565)
    ·
      refine ⟨1714593850019224882686107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 73156004267486928327940565 1714593850019224882686107)
      ·
        refine ⟨2571890775028837324029161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714593850019224882686107 2571890775028837324029161)
        ·
          refine ⟨1928918081271627993021871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2571890775028837324029161 1928918081271627993021871)
          ·
            refine ⟨2893377121907441989532807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928918081271627993021871 2893377121907441989532807)
            ·
              refine ⟨4340065682861162984299211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893377121907441989532807 4340065682861162984299211)
              ·
                refine ⟨6510098524291744476448817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340065682861162984299211 6510098524291744476448817)
                ·
                  refine ⟨4882573893218808357336613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6510098524291744476448817 4882573893218808357336613)
                  ·
                    refine ⟨915482604978526567000615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882573893218808357336613 915482604978526567000615)
                    ·
                      rfl

theorem cell22_2674344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2674344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674344 prefixEnd_2674344 := by exact prefixLift 2674344
  have htrace : WordTrace (prefixWord ++ tailWord_2674344) baseStart_2674344 baseEnd_2674344 := by
    simpa [prefixWord, tailWord_2674344, baseEnd_2674344] using wordTrace_append hprefix tailTrace_2674344
  have hstable : (prefixWord ++ tailWord_2674344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674344).length < 2 ^ (prefixWord ++ tailWord_2674344).sum := by decide
  have hdescent : baseEnd_2674344 < baseStart_2674344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674357 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2674357 : Nat := 118140960795 + 2674357 * 2 ^ 59
def prefixEnd_2674357 : Nat := 4983230072969 + 3 ^ 40 * 2674357 * 2
def baseEnd_2674357 : Nat := 915487055144198866425575

theorem tailTrace_2674357 : CollatzResearch.WordTrace tailWord_2674357 prefixEnd_2674357 915487055144198866425575 := by
  unfold tailWord_2674357
  simp only [CollatzResearch.WordTrace]
  refine ⟨97541813172268807657477325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65027875448179205104984883 97541813172268807657477325)
  ·
    refine ⟨36578179939600802871553997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97541813172268807657477325 36578179939600802871553997)
    ·
      refine ⟨13716817477350301076832749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36578179939600802871553997 13716817477350301076832749)
      ·
        refine ⟨5143806554006362903812281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13716817477350301076832749 5143806554006362903812281)
        ·
          refine ⟨3857854915504772177859211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5143806554006362903812281 3857854915504772177859211)
          ·
            refine ⟨5786782373257158266788817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857854915504772177859211 5786782373257158266788817)
            ·
              refine ⟨4340086779942868700091613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5786782373257158266788817 4340086779942868700091613)
              ·
                refine ⟨1627532542478575762534355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4340086779942868700091613 1627532542478575762534355)
                ·
                  refine ⟨2441298813717863643801533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627532542478575762534355 2441298813717863643801533)
                  ·
                    refine ⟨915487055144198866425575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441298813717863643801533 915487055144198866425575)
                    ·
                      rfl

theorem cell22_2674357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2674357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674357 prefixEnd_2674357 := by exact prefixLift 2674357
  have htrace : WordTrace (prefixWord ++ tailWord_2674357) baseStart_2674357 baseEnd_2674357 := by
    simpa [prefixWord, tailWord_2674357, baseEnd_2674357] using wordTrace_append hprefix tailTrace_2674357
  have hstable : (prefixWord ++ tailWord_2674357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674357).length < 2 ^ (prefixWord ++ tailWord_2674357).sum := by decide
  have hdescent : baseEnd_2674357 < baseStart_2674357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674374 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2674374 : Nat := 118140960795 + 2674374 * 2 ^ 59
def prefixEnd_2674374 : Nat := 4983230072969 + 3 ^ 40 * 2674374 * 2
def baseEnd_2674374 : Nat := 915492874591616488750523

theorem tailTrace_2674374 : CollatzResearch.WordTrace tailWord_2674374 prefixEnd_2674374 915492874591616488750523 := by
  unfold tailWord_2674374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048201037912725611276443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65028288808804813040564117 3048201037912725611276443)
  ·
    refine ⟨4572301556869088416914665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048201037912725611276443 4572301556869088416914665)
    ·
      refine ⟨3429226167651816312685999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4572301556869088416914665 3429226167651816312685999)
      ·
        refine ⟨5143839251477724469028999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429226167651816312685999 5143839251477724469028999)
        ·
          refine ⟨7715758877216586703543499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143839251477724469028999 7715758877216586703543499)
          ·
            refine ⟨11573638315824880055315249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715758877216586703543499 11573638315824880055315249)
            ·
              refine ⟨8680228736868660041486437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11573638315824880055315249 8680228736868660041486437)
              ·
                refine ⟨1627542888162873757778707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8680228736868660041486437 1627542888162873757778707)
                ·
                  refine ⟨2441314332244310636668061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627542888162873757778707 2441314332244310636668061)
                  ·
                    refine ⟨915492874591616488750523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441314332244310636668061 915492874591616488750523)
                    ·
                      rfl

theorem cell22_2674374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2674374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674374 prefixEnd_2674374 := by exact prefixLift 2674374
  have htrace : WordTrace (prefixWord ++ tailWord_2674374) baseStart_2674374 baseEnd_2674374 := by
    simpa [prefixWord, tailWord_2674374, baseEnd_2674374] using wordTrace_append hprefix tailTrace_2674374
  have hstable : (prefixWord ++ tailWord_2674374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674374).length < 2 ^ (prefixWord ++ tailWord_2674374).sum := by decide
  have hdescent : baseEnd_2674374 < baseStart_2674374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674379 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_2674379 : Nat := 118140960795 + 2674379 * 2 ^ 59
def prefixEnd_2674379 : Nat := 4983230072969 + 3 ^ 40 * 2674379 * 2
def baseEnd_2674379 : Nat := 915494586193798142375507

theorem tailTrace_2674379 : CollatzResearch.WordTrace tailWord_2674379 prefixEnd_2674379 915494586193798142375507 := by
  unfold tailWord_2674379
  simp only [CollatzResearch.WordTrace]
  refine ⟨97542615578189105414778191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65028410385459403609852127 97542615578189105414778191)
  ·
    refine ⟨146313923367283658122167287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97542615578189105414778191 146313923367283658122167287)
    ·
      refine ⟨219470885050925487183250931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146313923367283658122167287 219470885050925487183250931)
      ·
        refine ⟨329206327576388230774876397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219470885050925487183250931 329206327576388230774876397)
        ·
          refine ⟨123452372841145586540578649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329206327576388230774876397 123452372841145586540578649)
          ·
            refine ⟨92589279630859189905433987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123452372841145586540578649 92589279630859189905433987)
            ·
              refine ⟨138883919446288784858150981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92589279630859189905433987 138883919446288784858150981)
              ·
                refine ⟨26040734896179147160903309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138883919446288784858150981 26040734896179147160903309)
                ·
                  refine ⟨9765275586067180185338741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26040734896179147160903309 9765275586067180185338741)
                  ·
                    refine ⟨915494586193798142375507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9765275586067180185338741 915494586193798142375507)
                    ·
                      rfl

theorem cell22_2674379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_2674379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674379 prefixEnd_2674379 := by exact prefixLift 2674379
  have htrace : WordTrace (prefixWord ++ tailWord_2674379) baseStart_2674379 baseEnd_2674379 := by
    simpa [prefixWord, tailWord_2674379, baseEnd_2674379] using wordTrace_append hprefix tailTrace_2674379
  have hstable : (prefixWord ++ tailWord_2674379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674379).length < 2 ^ (prefixWord ++ tailWord_2674379).sum := by decide
  have hdescent : baseEnd_2674379 < baseStart_2674379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674413 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_2674413 : Nat := 118140960795 + 2674413 * 2 ^ 59
def prefixEnd_2674413 : Nat := 4983230072969 + 3 ^ 40 * 2674413 * 2
def baseEnd_2674413 : Nat := 915506225088633387025403

theorem tailTrace_2674413 : CollatzResearch.WordTrace tailWord_2674413 prefixEnd_2674413 915506225088633387025403 := by
  unfold tailWord_2674413
  simp only [CollatzResearch.WordTrace]
  refine ⟨97543855660065929221515893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65029237106710619481010595 97543855660065929221515893)
  ·
    refine ⟨9144736468131180864517115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97543855660065929221515893 9144736468131180864517115)
    ·
      refine ⟨13717104702196771296775673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9144736468131180864517115 13717104702196771296775673)
      ·
        refine ⟨10287828526647578472581755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13717104702196771296775673 10287828526647578472581755)
        ·
          refine ⟨15431742789971367708872633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10287828526647578472581755 15431742789971367708872633)
          ·
            refine ⟨11573807092478525781654475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15431742789971367708872633 11573807092478525781654475)
            ·
              refine ⟨17360710638717788672481713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11573807092478525781654475 17360710638717788672481713)
              ·
                refine ⟨13020532979038341504361285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17360710638717788672481713 13020532979038341504361285)
                ·
                  refine ⟨2441349933569689032067741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13020532979038341504361285 2441349933569689032067741)
                  ·
                    refine ⟨915506225088633387025403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441349933569689032067741 915506225088633387025403)
                    ·
                      rfl

theorem cell22_2674413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_2674413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674413 prefixEnd_2674413 := by exact prefixLift 2674413
  have htrace : WordTrace (prefixWord ++ tailWord_2674413) baseStart_2674413 baseEnd_2674413 := by
    simpa [prefixWord, tailWord_2674413, baseEnd_2674413] using wordTrace_append hprefix tailTrace_2674413
  have hstable : (prefixWord ++ tailWord_2674413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674413).length < 2 ^ (prefixWord ++ tailWord_2674413).sum := by decide
  have hdescent : baseEnd_2674413 < baseStart_2674413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674438 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2674438 : Nat := 118140960795 + 2674438 * 2 ^ 59
def prefixEnd_2674438 : Nat := 4983230072969 + 3 ^ 40 * 2674438 * 2
def baseEnd_2674438 : Nat := 305171594366513885050109

theorem tailTrace_2674438 : CollatzResearch.WordTrace tailWord_2674438 prefixEnd_2674438 305171594366513885050109 := by
  unfold tailWord_2674438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048273983905479952849249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65029844989983572327450645 3048273983905479952849249)
  ·
    refine ⟨2286205487929109964636937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3048273983905479952849249 2286205487929109964636937)
    ·
      refine ⟨1714654115946832473477703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2286205487929109964636937 1714654115946832473477703)
      ·
        refine ⟨2571981173920248710216555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714654115946832473477703 2571981173920248710216555)
        ·
          refine ⟨3857971760880373065324833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571981173920248710216555 3857971760880373065324833)
          ·
            refine ⟨2893478820660279798993625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3857971760880373065324833 2893478820660279798993625)
            ·
              refine ⟨2170109115495209849245219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893478820660279798993625 2170109115495209849245219)
              ·
                refine ⟨3255163673242814773867829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170109115495209849245219 3255163673242814773867829)
                ·
                  refine ⟨305171594366513885050109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3255163673242814773867829 305171594366513885050109)
                  ·
                    rfl

theorem cell22_2674438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2674438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674438 prefixEnd_2674438 := by exact prefixLift 2674438
  have htrace : WordTrace (prefixWord ++ tailWord_2674438) baseStart_2674438 baseEnd_2674438 := by
    simpa [prefixWord, tailWord_2674438, baseEnd_2674438] using wordTrace_append hprefix tailTrace_2674438
  have hstable : (prefixWord ++ tailWord_2674438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674438).length < 2 ^ (prefixWord ++ tailWord_2674438).sum := by decide
  have hdescent : baseEnd_2674438 < baseStart_2674438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674488 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_2674488 : Nat := 118140960795 + 2674488 * 2 ^ 59
def prefixEnd_2674488 : Nat := 4983230072969 + 3 ^ 40 * 2674488 * 2
def baseEnd_2674488 : Nat := 305177299707119397133391

theorem tailTrace_2674488 : CollatzResearch.WordTrace tailWord_2674488 prefixEnd_2674488 305177299707119397133391 := by
  unfold tailWord_2674488
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773295567397108515248059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65031060756529478020330745 48773295567397108515248059)
  ·
    refine ⟨73159943351095662772872089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48773295567397108515248059 73159943351095662772872089)
    ·
      refine ⟨54869957513321747079654067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73159943351095662772872089 54869957513321747079654067)
      ·
        refine ⟨82304936269982620619481101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54869957513321747079654067 82304936269982620619481101)
        ·
          refine ⟨30864351101243482732305413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82304936269982620619481101 30864351101243482732305413)
          ·
            refine ⟨5787065831483153012307265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30864351101243482732305413 5787065831483153012307265)
            ·
              refine ⟨4340299373612364759230449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787065831483153012307265 4340299373612364759230449)
              ·
                refine ⟨3255224530209273569422837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340299373612364759230449 3255224530209273569422837)
                ·
                  refine ⟨305177299707119397133391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3255224530209273569422837 305177299707119397133391)
                  ·
                    rfl

theorem cell22_2674488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_2674488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674488 prefixEnd_2674488 := by exact prefixLift 2674488
  have htrace : WordTrace (prefixWord ++ tailWord_2674488) baseStart_2674488 baseEnd_2674488 := by
    simpa [prefixWord, tailWord_2674488, baseEnd_2674488] using wordTrace_append hprefix tailTrace_2674488
  have hstable : (prefixWord ++ tailWord_2674488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674488).length < 2 ^ (prefixWord ++ tailWord_2674488).sum := by decide
  have hdescent : baseEnd_2674488 < baseStart_2674488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674492 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_2674492 : Nat := 118140960795 + 2674492 * 2 ^ 59
def prefixEnd_2674492 : Nat := 4983230072969 + 3 ^ 40 * 2674492 * 2
def baseEnd_2674492 : Nat := 915533268403103514300161

theorem tailTrace_2674492 : CollatzResearch.WordTrace tailWord_2674492 prefixEnd_2674492 915533268403103514300161 := by
  unfold tailWord_2674492
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773368513389862856820865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65031158017853150475761153 48773368513389862856820865)
  ·
    refine ⟨36580026385042397142615649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48773368513389862856820865 36580026385042397142615649)
    ·
      refine ⟨27435019788781797856961737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36580026385042397142615649 27435019788781797856961737)
      ·
        refine ⟨20576264841586348392721303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27435019788781797856961737 20576264841586348392721303)
        ·
          refine ⟨30864397262379522589081955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576264841586348392721303 30864397262379522589081955)
          ·
            refine ⟨46296595893569283883622933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30864397262379522589081955 46296595893569283883622933)
            ·
              refine ⟨2170152932511060182044825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46296595893569283883622933 2170152932511060182044825)
              ·
                refine ⟨1627614699383295136533619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170152932511060182044825 1627614699383295136533619)
                ·
                  refine ⟨2441422049074942704800429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627614699383295136533619 2441422049074942704800429)
                  ·
                    refine ⟨915533268403103514300161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441422049074942704800429 915533268403103514300161)
                    ·
                      rfl

theorem cell22_2674492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_2674492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674492 prefixEnd_2674492 := by exact prefixLift 2674492
  have htrace : WordTrace (prefixWord ++ tailWord_2674492) baseStart_2674492 baseEnd_2674492 := by
    simpa [prefixWord, tailWord_2674492, baseEnd_2674492] using wordTrace_append hprefix tailTrace_2674492
  have hstable : (prefixWord ++ tailWord_2674492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674492).length < 2 ^ (prefixWord ++ tailWord_2674492).sum := by decide
  have hdescent : baseEnd_2674492 < baseStart_2674492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674501 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2674501 : Nat := 118140960795 + 2674501 * 2 ^ 59
def prefixEnd_2674501 : Nat := 4983230072969 + 3 ^ 40 * 2674501 * 2
def baseEnd_2674501 : Nat := 915536349287030490825133

theorem tailTrace_2674501 : CollatzResearch.WordTrace tailWord_2674501 prefixEnd_2674501 915536349287030490825133 := by
  unfold tailWord_2674501
  simp only [CollatzResearch.WordTrace]
  refine ⟨97547065283747120250719357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65031376855831413500479571 97547065283747120250719357)
  ·
    refine ⟨36580149481405170094019759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97547065283747120250719357 36580149481405170094019759)
    ·
      refine ⟨54870224222107755141029639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36580149481405170094019759 54870224222107755141029639)
      ·
        refine ⟨82305336333161632711544459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54870224222107755141029639 82305336333161632711544459)
        ·
          refine ⟨123458004499742449067316689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82305336333161632711544459 123458004499742449067316689)
          ·
            refine ⟨92593503374806836800487517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123458004499742449067316689 92593503374806836800487517)
            ·
              refine ⟨34722563765552563800182819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92593503374806836800487517 34722563765552563800182819)
              ·
                refine ⟨52083845648328845700274229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34722563765552563800182819 52083845648328845700274229)
                ·
                  refine ⟨4882860529530829284400709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52083845648328845700274229 4882860529530829284400709)
                  ·
                    refine ⟨915536349287030490825133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882860529530829284400709 915536349287030490825133)
                    ·
                      rfl

theorem cell22_2674501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2674501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674501 prefixEnd_2674501 := by exact prefixLift 2674501
  have htrace : WordTrace (prefixWord ++ tailWord_2674501) baseStart_2674501 baseEnd_2674501 := by
    simpa [prefixWord, tailWord_2674501, baseEnd_2674501] using wordTrace_append hprefix tailTrace_2674501
  have hstable : (prefixWord ++ tailWord_2674501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674501).length < 2 ^ (prefixWord ++ tailWord_2674501).sum := by decide
  have hdescent : baseEnd_2674501 < baseStart_2674501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674584 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_2674584 : Nat := 118140960795 + 2674584 * 2 ^ 59
def prefixEnd_2674584 : Nat := 4983230072969 + 3 ^ 40 * 2674584 * 2
def baseEnd_2674584 : Nat := 305188253961081980333293

theorem tailTrace_2674584 : CollatzResearch.WordTrace tailWord_2674584 prefixEnd_2674584 305188253961081980333293 := by
  unfold tailWord_2674584
  simp only [CollatzResearch.WordTrace]
  refine ⟨48775046271223212712995403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65033395028297616950660537 48775046271223212712995403)
  ·
    refine ⟨73162569406834819069493105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48775046271223212712995403 73162569406834819069493105)
    ·
      refine ⟨54871927055126114302119829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73162569406834819069493105 54871927055126114302119829)
      ·
        refine ⟨2572121580709036607911867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54871927055126114302119829 2572121580709036607911867)
        ·
          refine ⟨3858182371063554911867801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572121580709036607911867 3858182371063554911867801)
          ·
            refine ⟨2893636778297666183900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3858182371063554911867801 2893636778297666183900851)
            ·
              refine ⟨4340455167446499275851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893636778297666183900851 4340455167446499275851277)
              ·
                refine ⟨1627670687792437228444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4340455167446499275851277 1627670687792437228444229)
                ·
                  refine ⟨305188253961081980333293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627670687792437228444229 305188253961081980333293)
                  ·
                    rfl

theorem cell22_2674584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_2674584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674584 prefixEnd_2674584 := by exact prefixLift 2674584
  have htrace : WordTrace (prefixWord ++ tailWord_2674584) baseStart_2674584 baseEnd_2674584 := by
    simpa [prefixWord, tailWord_2674584, baseEnd_2674584] using wordTrace_append hprefix tailTrace_2674584
  have hstable : (prefixWord ++ tailWord_2674584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674584).length < 2 ^ (prefixWord ++ tailWord_2674584).sum := by decide
  have hdescent : baseEnd_2674584 < baseStart_2674584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674612 : List Nat := [2, 5, 2, 1, 2, 1, 2, 7]
def baseStart_2674612 : Nat := 118140960795 + 2674612 * 2 ^ 59
def prefixEnd_2674612 : Nat := 4983230072969 + 3 ^ 40 * 2674612 * 2
def baseEnd_2674612 : Nat := 101730482983940355699977

theorem tailTrace_2674612 : CollatzResearch.WordTrace tailWord_2674612 prefixEnd_2674612 101730482983940355699977 := by
  unfold tailWord_2674612
  simp only [CollatzResearch.WordTrace]
  refine ⟨48775556893172493104005045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65034075857563324138673393 48775556893172493104005045)
  ·
    refine ⟨4572708458734921228500473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48775556893172493104005045 4572708458734921228500473)
    ·
      refine ⟨3429531344051190921375355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4572708458734921228500473 3429531344051190921375355)
      ·
        refine ⟨5144297016076786382063033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429531344051190921375355 5144297016076786382063033)
        ·
          refine ⟨3858222762057589786547275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5144297016076786382063033 3858222762057589786547275)
          ·
            refine ⟨5787334143086384679820913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858222762057589786547275 5787334143086384679820913)
            ·
              refine ⟨4340500607314788509865685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787334143086384679820913 4340500607314788509865685)
              ·
                refine ⟨101730482983940355699977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4340500607314788509865685 101730482983940355699977)
                ·
                  rfl

theorem cell22_2674612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_2674612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674612 prefixEnd_2674612 := by exact prefixLift 2674612
  have htrace : WordTrace (prefixWord ++ tailWord_2674612) baseStart_2674612 baseEnd_2674612 := by
    simpa [prefixWord, tailWord_2674612, baseEnd_2674612] using wordTrace_append hprefix tailTrace_2674612
  have hstable : (prefixWord ++ tailWord_2674612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674612).length < 2 ^ (prefixWord ++ tailWord_2674612).sum := by decide
  have hdescent : baseEnd_2674612 < baseStart_2674612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674623 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 5]
def baseStart_2674623 : Nat := 118140960795 + 2674623 * 2 ^ 59
def prefixEnd_2674623 : Nat := 4983230072969 + 3 ^ 40 * 2674623 * 2
def baseEnd_2674623 : Nat := 305192704126754279758253

theorem tailTrace_2674623 : CollatzResearch.WordTrace tailWord_2674623 prefixEnd_2674623 305192704126754279758253 := by
  unfold tailWord_2674623
  simp only [CollatzResearch.WordTrace]
  refine ⟨97551514989305135086660523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65034343326203423391107015 97551514989305135086660523)
  ·
    refine ⟨146327272483957702629990785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97551514989305135086660523 146327272483957702629990785)
    ·
      refine ⟨109745454362968276972493089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146327272483957702629990785 109745454362968276972493089)
      ·
        refine ⟨82309090772226207729369817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109745454362968276972493089 82309090772226207729369817)
        ·
          refine ⟨61731818079169655797027363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82309090772226207729369817 61731818079169655797027363)
          ·
            refine ⟨92597727118754483695541045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61731818079169655797027363 92597727118754483695541045)
            ·
              refine ⟨8681036917383232846456973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92597727118754483695541045 8681036917383232846456973)
              ·
                refine ⟨3255388844018712317421365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8681036917383232846456973 3255388844018712317421365)
                ·
                  refine ⟨305192704126754279758253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3255388844018712317421365 305192704126754279758253)
                  ·
                    rfl

theorem cell22_2674623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 5].length) (baseStart_2674623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674623 prefixEnd_2674623 := by exact prefixLift 2674623
  have htrace : WordTrace (prefixWord ++ tailWord_2674623) baseStart_2674623 baseEnd_2674623 := by
    simpa [prefixWord, tailWord_2674623, baseEnd_2674623] using wordTrace_append hprefix tailTrace_2674623
  have hstable : (prefixWord ++ tailWord_2674623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674623).length < 2 ^ (prefixWord ++ tailWord_2674623).sum := by decide
  have hdescent : baseEnd_2674623 < baseStart_2674623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674670 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2674670 : Nat := 118140960795 + 2674670 * 2 ^ 59
def prefixEnd_2674670 : Nat := 4983230072969 + 3 ^ 40 * 2674670 * 2
def baseEnd_2674670 : Nat := 915594201440770383349615

theorem tailTrace_2674670 : CollatzResearch.WordTrace tailWord_2674670 prefixEnd_2674670 915594201440770383349615 := by
  unfold tailWord_2674670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194153652516857764202683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65035486146756574742414309 12194153652516857764202683)
  ·
    refine ⟨18291230478775286646304025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194153652516857764202683 18291230478775286646304025)
    ·
      refine ⟨13718422859081464984728019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18291230478775286646304025 13718422859081464984728019)
      ·
        refine ⟨20577634288622197477092029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13718422859081464984728019 20577634288622197477092029)
        ·
          refine ⟨7716612858233324053909511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20577634288622197477092029 7716612858233324053909511)
          ·
            refine ⟨11574919287349986080864267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716612858233324053909511 11574919287349986080864267)
            ·
              refine ⟨17362378931024979121296401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11574919287349986080864267 17362378931024979121296401)
              ·
                refine ⟨13021784198268734340972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17362378931024979121296401 13021784198268734340972301)
                ·
                  refine ⟨4883169074350775377864613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13021784198268734340972301 4883169074350775377864613)
                  ·
                    refine ⟨915594201440770383349615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883169074350775377864613 915594201440770383349615)
                    ·
                      rfl

theorem cell22_2674670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2674670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674670 prefixEnd_2674670 := by exact prefixLift 2674670
  have htrace : WordTrace (prefixWord ++ tailWord_2674670) baseStart_2674670 baseEnd_2674670 := by
    simpa [prefixWord, tailWord_2674670, baseEnd_2674670] using wordTrace_append hprefix tailTrace_2674670
  have hstable : (prefixWord ++ tailWord_2674670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674670).length < 2 ^ (prefixWord ++ tailWord_2674670).sum := by decide
  have hdescent : baseEnd_2674670 < baseStart_2674670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674683 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_2674683 : Nat := 118140960795 + 2674683 * 2 ^ 59
def prefixEnd_2674683 : Nat := 4983230072969 + 3 ^ 40 * 2674683 * 2
def baseEnd_2674683 : Nat := 915598651606442682774575

theorem tailTrace_2674683 : CollatzResearch.WordTrace tailWord_2674683 prefixEnd_2674683 915598651606442682774575 := by
  unfold tailWord_2674683
  simp only [CollatzResearch.WordTrace]
  refine ⟨97553703369087765333844703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65035802246058510222563135 97553703369087765333844703)
  ·
    refine ⟨146330555053631648000767055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97553703369087765333844703 146330555053631648000767055)
    ·
      refine ⟨219495832580447472001150583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146330555053631648000767055 219495832580447472001150583)
      ·
        refine ⟨329243748870671208001725875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219495832580447472001150583 329243748870671208001725875)
        ·
          refine ⟨493865623306006812002588813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329243748870671208001725875 493865623306006812002588813)
          ·
            refine ⟨185199608739752554500970805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493865623306006812002588813 185199608739752554500970805)
            ·
              refine ⟨17362463319351801984466013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185199608739752554500970805 17362463319351801984466013)
              ·
                refine ⟨6510923744756925744174755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17362463319351801984466013 6510923744756925744174755)
                ·
                  refine ⟨9766385617135388616262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6510923744756925744174755 9766385617135388616262133)
                  ·
                    refine ⟨915598651606442682774575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766385617135388616262133 915598651606442682774575)
                    ·
                      rfl

theorem cell22_2674683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_2674683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674683 prefixEnd_2674683 := by exact prefixLift 2674683
  have htrace : WordTrace (prefixWord ++ tailWord_2674683) baseStart_2674683 baseEnd_2674683 := by
    simpa [prefixWord, tailWord_2674683, baseEnd_2674683] using wordTrace_append hprefix tailTrace_2674683
  have hstable : (prefixWord ++ tailWord_2674683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674683).length < 2 ^ (prefixWord ++ tailWord_2674683).sum := by decide
  have hdescent : baseEnd_2674683 < baseStart_2674683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674700 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_2674700 : Nat := 118140960795 + 2674700 * 2 ^ 59
def prefixEnd_2674700 : Nat := 4983230072969 + 3 ^ 40 * 2674700 * 2
def baseEnd_2674700 : Nat := 915604471053860305099523

theorem tailTrace_2674700 : CollatzResearch.WordTrace tailWord_2674700 prefixEnd_2674700 915604471053860305099523 := by
  unfold tailWord_2674700
  simp only [CollatzResearch.WordTrace]
  refine ⟨48777161705013088618606777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65036215606684118158142369 48777161705013088618606777)
  ·
    refine ⟨36582871278759816463955083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48777161705013088618606777 36582871278759816463955083)
    ·
      refine ⟨54874306918139724695932625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36582871278759816463955083 54874306918139724695932625)
      ·
        refine ⟨41155730188604793521949469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54874306918139724695932625 41155730188604793521949469)
        ·
          refine ⟨15433398820726797570731051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41155730188604793521949469 15433398820726797570731051)
          ·
            refine ⟨23150098231090196356096577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15433398820726797570731051 23150098231090196356096577)
            ·
              refine ⟨17362573673317647267072433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23150098231090196356096577 17362573673317647267072433)
              ·
                refine ⟨13021930254988235450304325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17362573673317647267072433 13021930254988235450304325)
                ·
                  refine ⟨2441611922810294146932061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13021930254988235450304325 2441611922810294146932061)
                  ·
                    refine ⟨915604471053860305099523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441611922810294146932061 915604471053860305099523)
                    ·
                      rfl

theorem cell22_2674700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_2674700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674700 prefixEnd_2674700 := by exact prefixLift 2674700
  have htrace : WordTrace (prefixWord ++ tailWord_2674700) baseStart_2674700 baseEnd_2674700 := by
    simpa [prefixWord, tailWord_2674700, baseEnd_2674700] using wordTrace_append hprefix tailTrace_2674700
  have hstable : (prefixWord ++ tailWord_2674700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674700).length < 2 ^ (prefixWord ++ tailWord_2674700).sum := by decide
  have hdescent : baseEnd_2674700 < baseStart_2674700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674702 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_2674702 : Nat := 118140960795 + 2674702 * 2 ^ 59
def prefixEnd_2674702 : Nat := 4983230072969 + 3 ^ 40 * 2674702 * 2
def baseEnd_2674702 : Nat := 305201718564910988849839

theorem tailTrace_2674702 : CollatzResearch.WordTrace tailWord_2674702 prefixEnd_2674702 305201718564910988849839 := by
  unfold tailWord_2674702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194299544502366447348295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65036264237345954385857573 12194299544502366447348295)
  ·
    refine ⟨18291449316753549671022443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194299544502366447348295 18291449316753549671022443)
    ·
      refine ⟨27437173975130324506533665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18291449316753549671022443 27437173975130324506533665)
      ·
        refine ⟨20577880481347743379900249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27437173975130324506533665 20577880481347743379900249)
        ·
          refine ⟨15433410361010807534925187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20577880481347743379900249 15433410361010807534925187)
          ·
            refine ⟨23150115541516211302387781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15433410361010807534925187 23150115541516211302387781)
            ·
              refine ⟨4340646664034289619197709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23150115541516211302387781 4340646664034289619197709)
              ·
                refine ⟨1627742499012858607199141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4340646664034289619197709 1627742499012858607199141)
                ·
                  refine ⟨305201718564910988849839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627742499012858607199141 305201718564910988849839)
                  ·
                    rfl

theorem cell22_2674702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_2674702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674702 prefixEnd_2674702 := by exact prefixLift 2674702
  have htrace : WordTrace (prefixWord ++ tailWord_2674702) baseStart_2674702 baseEnd_2674702 := by
    simpa [prefixWord, tailWord_2674702, baseEnd_2674702] using wordTrace_append hprefix tailTrace_2674702
  have hstable : (prefixWord ++ tailWord_2674702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674702).length < 2 ^ (prefixWord ++ tailWord_2674702).sum := by decide
  have hdescent : baseEnd_2674702 < baseStart_2674702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674717 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2674717 : Nat := 118140960795 + 2674717 * 2 ^ 59
def prefixEnd_2674717 : Nat := 4983230072969 + 3 ^ 40 * 2674717 * 2
def baseEnd_2674717 : Nat := 915610290501277927424471

theorem tailTrace_2674717 : CollatzResearch.WordTrace tailWord_2674717 prefixEnd_2674717 915610290501277927424471 := by
  unfold tailWord_2674717
  simp only [CollatzResearch.WordTrace]
  refine ⟨97554943450964589140582405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65036628967309726093721603 97554943450964589140582405)
  ·
    refine ⟨18291551897055860463859201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97554943450964589140582405 18291551897055860463859201)
    ·
      refine ⟨13718663922791895347894401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18291551897055860463859201 13718663922791895347894401)
      ·
        refine ⟨10288997942093921510920801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13718663922791895347894401 10288997942093921510920801)
        ·
          refine ⟨7716748456570441133190601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10288997942093921510920801 7716748456570441133190601)
          ·
            refine ⟨5787561342427830849892951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7716748456570441133190601 5787561342427830849892951)
            ·
              refine ⟨8681342013641746274839427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787561342427830849892951 8681342013641746274839427)
              ·
                refine ⟨13022013020462619412259141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681342013641746274839427 13022013020462619412259141)
                ·
                  refine ⟨2441627441336741139798589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13022013020462619412259141 2441627441336741139798589)
                  ·
                    refine ⟨915610290501277927424471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441627441336741139798589 915610290501277927424471)
                    ·
                      rfl

theorem cell22_2674717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2674717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674717 prefixEnd_2674717 := by exact prefixLift 2674717
  have htrace : WordTrace (prefixWord ++ tailWord_2674717) baseStart_2674717 baseEnd_2674717 := by
    simpa [prefixWord, tailWord_2674717, baseEnd_2674717] using wordTrace_append hprefix tailTrace_2674717
  have hstable : (prefixWord ++ tailWord_2674717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674717).length < 2 ^ (prefixWord ++ tailWord_2674717).sum := by decide
  have hdescent : baseEnd_2674717 < baseStart_2674717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674743 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2674743 : Nat := 118140960795 + 2674743 * 2 ^ 59
def prefixEnd_2674743 : Nat := 4983230072969 + 3 ^ 40 * 2674743 * 2
def baseEnd_2674743 : Nat := 915619190832622526274391

theorem tailTrace_2674743 : CollatzResearch.WordTrace tailWord_2674743 prefixEnd_2674743 915619190832622526274391 := by
  unfold tailWord_2674743
  simp only [CollatzResearch.WordTrace]
  refine ⟨97555891748870395581028883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65037261165913597054019255 97555891748870395581028883)
  ·
    refine ⟨146333837623305593371543325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97555891748870395581028883 146333837623305593371543325)
    ·
      refine ⟨54875189108739597514328747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146333837623305593371543325 54875189108739597514328747)
      ·
        refine ⟨82312783663109396271493121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54875189108739597514328747 82312783663109396271493121)
        ·
          refine ⟨61734587747332047203619841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82312783663109396271493121 61734587747332047203619841)
          ·
            refine ⟨46300940810499035402714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61734587747332047203619841 46300940810499035402714881)
            ·
              refine ⟨34725705607874276552036161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46300940810499035402714881 34725705607874276552036161)
              ·
                refine ⟨26044279205905707414027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34725705607874276552036161 26044279205905707414027121)
                ·
                  refine ⟨19533209404429280560520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26044279205905707414027121 19533209404429280560520341)
                  ·
                    refine ⟨915619190832622526274391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19533209404429280560520341 915619190832622526274391)
                    ·
                      rfl

theorem cell22_2674743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2674743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674743 prefixEnd_2674743 := by exact prefixLift 2674743
  have htrace : WordTrace (prefixWord ++ tailWord_2674743) baseStart_2674743 baseEnd_2674743 := by
    simpa [prefixWord, tailWord_2674743, baseEnd_2674743] using wordTrace_append hprefix tailTrace_2674743
  have hstable : (prefixWord ++ tailWord_2674743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674743).length < 2 ^ (prefixWord ++ tailWord_2674743).sum := by decide
  have hdescent : baseEnd_2674743 < baseStart_2674743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674830 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_2674830 : Nat := 118140960795 + 2674830 * 2 ^ 59
def prefixEnd_2674830 : Nat := 4983230072969 + 3 ^ 40 * 2674830 * 2
def baseEnd_2674830 : Nat := 915648972710583299349125

theorem tailTrace_2674830 : CollatzResearch.WordTrace tailWord_2674830 prefixEnd_2674830 915648972710583299349125 := by
  unfold tailWord_2674830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194883112444401179930743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65039376599703472959630629 12194883112444401179930743)
  ·
    refine ⟨18292324668666601769896115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194883112444401179930743 18292324668666601769896115)
    ·
      refine ⟨27438487002999902654844173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18292324668666601769896115 27438487002999902654844173)
      ·
        refine ⟨10289432626124963495566565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27438487002999902654844173 10289432626124963495566565)
        ·
          refine ⟨1929268617398430655418731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10289432626124963495566565 1929268617398430655418731)
          ·
            refine ⟨2893902926097645983128097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929268617398430655418731 2893902926097645983128097)
            ·
              refine ⟨2170427194573234487346073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893902926097645983128097 2170427194573234487346073)
              ·
                refine ⟨1627820395929925865509555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170427194573234487346073 1627820395929925865509555)
                ·
                  refine ⟨2441730593894888798264333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627820395929925865509555 2441730593894888798264333)
                  ·
                    refine ⟨915648972710583299349125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441730593894888798264333 915648972710583299349125)
                    ·
                      rfl

theorem cell22_2674830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_2674830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674830 prefixEnd_2674830 := by exact prefixLift 2674830
  have htrace : WordTrace (prefixWord ++ tailWord_2674830) baseStart_2674830 baseEnd_2674830 := by
    simpa [prefixWord, tailWord_2674830, baseEnd_2674830] using wordTrace_append hprefix tailTrace_2674830
  have hstable : (prefixWord ++ tailWord_2674830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674830).length < 2 ^ (prefixWord ++ tailWord_2674830).sum := by decide
  have hdescent : baseEnd_2674830 < baseStart_2674830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674837 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 4]
def baseStart_2674837 : Nat := 118140960795 + 2674837 * 2 ^ 59
def prefixEnd_2674837 : Nat := 4983230072969 + 3 ^ 40 * 2674837 * 2
def baseEnd_2674837 : Nat := 305217122984545871474701

theorem tailTrace_2674837 : CollatzResearch.WordTrace tailWord_2674837 prefixEnd_2674837 305217122984545871474701 := by
  unfold tailWord_2674837
  simp only [CollatzResearch.WordTrace]
  refine ⟨97559320210529849634950765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65039546807019899756633843 97559320210529849634950765)
  ·
    refine ⟨36584745078948693613106537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97559320210529849634950765 36584745078948693613106537)
    ·
      refine ⟨27438558809211520209829903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36584745078948693613106537 27438558809211520209829903)
      ·
        refine ⟨41157838213817280314744855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27438558809211520209829903 41157838213817280314744855)
        ·
          refine ⟨61736757320725920472117283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41157838213817280314744855 61736757320725920472117283)
          ·
            refine ⟨92605135981088880708175925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61736757320725920472117283 92605135981088880708175925)
            ·
              refine ⟨8681731498227082566391493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92605135981088880708175925 8681731498227082566391493)
              ·
                refine ⟨1627824655917577981198405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8681731498227082566391493 1627824655917577981198405)
                ·
                  refine ⟨305217122984545871474701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627824655917577981198405 305217122984545871474701)
                  ·
                    rfl

theorem cell22_2674837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_2674837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674837 prefixEnd_2674837 := by exact prefixLift 2674837
  have htrace : WordTrace (prefixWord ++ tailWord_2674837) baseStart_2674837 baseEnd_2674837 := by
    simpa [prefixWord, tailWord_2674837, baseEnd_2674837] using wordTrace_append hprefix tailTrace_2674837
  have hstable : (prefixWord ++ tailWord_2674837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674837).length < 2 ^ (prefixWord ++ tailWord_2674837).sum := by decide
  have hdescent : baseEnd_2674837 < baseStart_2674837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674897 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_2674897 : Nat := 118140960795 + 2674897 * 2 ^ 59
def prefixEnd_2674897 : Nat := 4983230072969 + 3 ^ 40 * 2674897 * 2
def baseEnd_2674897 : Nat := 915671908179817457923919

theorem tailTrace_2674897 : CollatzResearch.WordTrace tailWord_2674897 prefixEnd_2674897 915671908179817457923919 := by
  unfold tailWord_2674897
  simp only [CollatzResearch.WordTrace]
  refine ⟨97561508590312479882134945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65041005726874986588089963 97561508590312479882134945)
  ·
    refine ⟨73171131442734359911601209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97561508590312479882134945 73171131442734359911601209)
    ·
      refine ⟨54878348582050769933700907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73171131442734359911601209 54878348582050769933700907)
      ·
        refine ⟨82317522873076154900551361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54878348582050769933700907 82317522873076154900551361)
        ·
          refine ⟨61738142154807116175413521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82317522873076154900551361 61738142154807116175413521)
          ·
            refine ⟨46303606616105337131560141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61738142154807116175413521 46303606616105337131560141)
            ·
              refine ⟨17363852481039501424335053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46303606616105337131560141 17363852481039501424335053)
              ·
                refine ⟨6511444680389813034125645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17363852481039501424335053 6511444680389813034125645)
                ·
                  refine ⟨2441791755146179887797117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6511444680389813034125645 2441791755146179887797117)
                  ·
                    refine ⟨915671908179817457923919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441791755146179887797117 915671908179817457923919)
                    ·
                      rfl

theorem cell22_2674897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_2674897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674897 prefixEnd_2674897 := by exact prefixLift 2674897
  have htrace : WordTrace (prefixWord ++ tailWord_2674897) baseStart_2674897 baseEnd_2674897 := by
    simpa [prefixWord, tailWord_2674897, baseEnd_2674897] using wordTrace_append hprefix tailTrace_2674897
  have hstable : (prefixWord ++ tailWord_2674897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674897).length < 2 ^ (prefixWord ++ tailWord_2674897).sum := by decide
  have hdescent : baseEnd_2674897 < baseStart_2674897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2674948 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2674948 : Nat := 118140960795 + 2674948 * 2 ^ 59
def prefixEnd_2674948 : Nat := 4983230072969 + 3 ^ 40 * 2674948 * 2
def baseEnd_2674948 : Nat := 915689366522070324898763

theorem tailTrace_2674948 : CollatzResearch.WordTrace tailWord_2674948 prefixEnd_2674948 915689366522070324898763 := by
  unfold tailWord_2674948
  simp only [CollatzResearch.WordTrace]
  refine ⟨48781684356563857796120749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65042245808751810394827665 48781684356563857796120749)
  ·
    refine ⟨18293131633711446673545281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48781684356563857796120749 18293131633711446673545281)
    ·
      refine ⟨13719848725283585005158961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18293131633711446673545281 13719848725283585005158961)
      ·
        refine ⟨10289886543962688753869221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13719848725283585005158961 10289886543962688753869221)
        ·
          refine ⟨1929353726993004141350479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10289886543962688753869221 1929353726993004141350479)
          ·
            refine ⟨2894030590489506212025719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929353726993004141350479 2894030590489506212025719)
            ·
              refine ⟨4341045885734259318038579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894030590489506212025719 4341045885734259318038579)
              ·
                refine ⟨6511568828601388977057869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341045885734259318038579 6511568828601388977057869)
                ·
                  refine ⟨2441838310725520866396701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6511568828601388977057869 2441838310725520866396701)
                  ·
                    refine ⟨915689366522070324898763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441838310725520866396701 915689366522070324898763)
                    ·
                      rfl

theorem cell22_2674948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2674948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2674948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2674948 prefixEnd_2674948 := by exact prefixLift 2674948
  have htrace : WordTrace (prefixWord ++ tailWord_2674948) baseStart_2674948 baseEnd_2674948 := by
    simpa [prefixWord, tailWord_2674948, baseEnd_2674948] using wordTrace_append hprefix tailTrace_2674948
  have hstable : (prefixWord ++ tailWord_2674948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2674948).length < 2 ^ (prefixWord ++ tailWord_2674948).sum := by decide
  have hdescent : baseEnd_2674948 < baseStart_2674948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2674948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675006 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2675006 : Nat := 118140960795 + 2675006 * 2 ^ 59
def prefixEnd_2675006 : Nat := 4983230072969 + 3 ^ 40 * 2675006 * 2
def baseEnd_2675006 : Nat := 305236407035792502316195

theorem tailTrace_2675006 : CollatzResearch.WordTrace tailWord_2675006 prefixEnd_2675006 305236407035792502316195 := by
  unfold tailWord_2675006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195685518364698937231609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65043656097945060998568581 12195685518364698937231609)
  ·
    refine ⟨9146764138773524202923707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12195685518364698937231609 9146764138773524202923707)
    ·
      refine ⟨13720146208160286304385561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146764138773524202923707 13720146208160286304385561)
      ·
        refine ⟨10290109656120214728289171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13720146208160286304385561 10290109656120214728289171)
        ·
          refine ⟨15435164484180322092433757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290109656120214728289171 15435164484180322092433757)
          ·
            refine ⟨5788186681567620784662659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15435164484180322092433757 5788186681567620784662659)
            ·
              refine ⟨8682280022351431176993989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788186681567620784662659 8682280022351431176993989)
              ·
                refine ⟨1627927504190893345686373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8682280022351431176993989 1627927504190893345686373)
                ·
                  refine ⟨305236407035792502316195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627927504190893345686373 305236407035792502316195)
                  ·
                    rfl

theorem cell22_2675006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2675006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675006 prefixEnd_2675006 := by exact prefixLift 2675006
  have htrace : WordTrace (prefixWord ++ tailWord_2675006) baseStart_2675006 baseEnd_2675006 := by
    simpa [prefixWord, tailWord_2675006, baseEnd_2675006] using wordTrace_append hprefix tailTrace_2675006
  have hstable : (prefixWord ++ tailWord_2675006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675006).length < 2 ^ (prefixWord ++ tailWord_2675006).sum := by decide
  have hdescent : baseEnd_2675006 < baseStart_2675006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675036 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2675036 : Nat := 118140960795 + 2675036 * 2 ^ 59
def prefixEnd_2675036 : Nat := 4983230072969 + 3 ^ 40 * 2675036 * 2
def baseEnd_2675036 : Nat := 915719490720467428698493

theorem tailTrace_2675036 : CollatzResearch.WordTrace tailWord_2675036 prefixEnd_2675036 915719490720467428698493 := by
  unfold tailWord_2675036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48783289168404453310722481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65044385557872604414296641 48783289168404453310722481)
  ·
    refine ⟨36587466876303339983041861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48783289168404453310722481 36587466876303339983041861)
    ·
      refine ⟨6860150039306876246820349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36587466876303339983041861 6860150039306876246820349)
      ·
        refine ⟨2572556264740078592557631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6860150039306876246820349 2572556264740078592557631)
        ·
          refine ⟨3858834397110117888836447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572556264740078592557631 3858834397110117888836447)
          ·
            refine ⟨5788251595665176833254671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858834397110117888836447 5788251595665176833254671)
            ·
              refine ⟨8682377393497765249882007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788251595665176833254671 8682377393497765249882007)
              ·
                refine ⟨13023566090246647874823011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8682377393497765249882007 13023566090246647874823011)
                ·
                  refine ⟨19535349135369971812234517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13023566090246647874823011 19535349135369971812234517)
                  ·
                    refine ⟨915719490720467428698493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19535349135369971812234517 915719490720467428698493)
                    ·
                      rfl

theorem cell22_2675036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2675036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675036 prefixEnd_2675036 := by exact prefixLift 2675036
  have htrace : WordTrace (prefixWord ++ tailWord_2675036) baseStart_2675036 baseEnd_2675036 := by
    simpa [prefixWord, tailWord_2675036, baseEnd_2675036] using wordTrace_append hprefix tailTrace_2675036
  have hstable : (prefixWord ++ tailWord_2675036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675036).length < 2 ^ (prefixWord ++ tailWord_2675036).sum := by decide
  have hdescent : baseEnd_2675036 < baseStart_2675036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675109 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2675109 : Nat := 118140960795 + 2675109 * 2 ^ 59
def prefixEnd_2675109 : Nat := 4983230072969 + 3 ^ 40 * 2675109 * 2
def baseEnd_2675109 : Nat := 915744480112319571623269

theorem tailTrace_2675109 : CollatzResearch.WordTrace tailWord_2675109 prefixEnd_2675109 915744480112319571623269 := by
  unfold tailWord_2675109
  simp only [CollatzResearch.WordTrace]
  refine ⟨97569240865544440088852381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65046160577029626725901587 97569240865544440088852381)
  ·
    refine ⟨36588465324579165033319643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97569240865544440088852381 36588465324579165033319643)
    ·
      refine ⟨54882697986868747549979465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36588465324579165033319643 54882697986868747549979465)
      ·
        refine ⟨41162023490151560662484599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54882697986868747549979465 41162023490151560662484599)
        ·
          refine ⟨61743035235227340993726899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41162023490151560662484599 61743035235227340993726899)
          ·
            refine ⟨92614552852841011490590349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61743035235227340993726899 92614552852841011490590349)
            ·
              refine ⟨34730457319815379308971381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92614552852841011490590349 34730457319815379308971381)
              ·
                refine ⟨3255980373732691810216067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34730457319815379308971381 3255980373732691810216067)
                ·
                  refine ⟨4883970560599037715324101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255980373732691810216067 4883970560599037715324101)
                  ·
                    refine ⟨915744480112319571623269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883970560599037715324101 915744480112319571623269)
                    ·
                      rfl

theorem cell22_2675109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2675109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675109 prefixEnd_2675109 := by exact prefixLift 2675109
  have htrace : WordTrace (prefixWord ++ tailWord_2675109) baseStart_2675109 baseEnd_2675109 := by
    simpa [prefixWord, tailWord_2675109, baseEnd_2675109] using wordTrace_append hprefix tailTrace_2675109
  have hstable : (prefixWord ++ tailWord_2675109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675109).length < 2 ^ (prefixWord ++ tailWord_2675109).sum := by decide
  have hdescent : baseEnd_2675109 < baseStart_2675109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675117 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_2675117 : Nat := 118140960795 + 2675117 * 2 ^ 59
def prefixEnd_2675117 : Nat := 4983230072969 + 3 ^ 40 * 2675117 * 2
def baseEnd_2675117 : Nat := 915747218675810217423245

theorem tailTrace_2675117 : CollatzResearch.WordTrace tailWord_2675117 prefixEnd_2675117 915747218675810217423245 := by
  unfold tailWord_2675117
  simp only [CollatzResearch.WordTrace]
  refine ⟨97569532649515457455143605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65046355099676971636762403 97569532649515457455143605)
  ·
    refine ⟨9147143685892074136419713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97569532649515457455143605 9147143685892074136419713)
    ·
      refine ⟨6860357764419055602314785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9147143685892074136419713 6860357764419055602314785)
      ·
        refine ⟨5145268323314291701736089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6860357764419055602314785 5145268323314291701736089)
        ·
          refine ⟨3858951242485718776302067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5145268323314291701736089 3858951242485718776302067)
          ·
            refine ⟨5788426863728578164453101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858951242485718776302067 5788426863728578164453101)
            ·
              refine ⟨2170660073898216811669913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5788426863728578164453101 2170660073898216811669913)
              ·
                refine ⟨1627995055423662608752435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170660073898216811669913 1627995055423662608752435)
                ·
                  refine ⟨2441992583135493913128653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627995055423662608752435 2441992583135493913128653)
                  ·
                    refine ⟨915747218675810217423245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2441992583135493913128653 915747218675810217423245)
                    ·
                      rfl

theorem cell22_2675117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_2675117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675117 prefixEnd_2675117 := by exact prefixLift 2675117
  have htrace : WordTrace (prefixWord ++ tailWord_2675117) baseStart_2675117 baseEnd_2675117 := by
    simpa [prefixWord, tailWord_2675117, baseEnd_2675117] using wordTrace_append hprefix tailTrace_2675117
  have hstable : (prefixWord ++ tailWord_2675117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675117).length < 2 ^ (prefixWord ++ tailWord_2675117).sum := by decide
  have hdescent : baseEnd_2675117 < baseStart_2675117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675156 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2675156 : Nat := 118140960795 + 2675156 * 2 ^ 59
def prefixEnd_2675156 : Nat := 4983230072969 + 3 ^ 40 * 2675156 * 2
def baseEnd_2675156 : Nat := 915760569172827115698125

theorem tailTrace_2675156 : CollatzResearch.WordTrace tailWord_2675156 prefixEnd_2675156 915760569172827115698125 := by
  unfold tailWord_2675156
  simp only [CollatzResearch.WordTrace]
  refine ⟨48785477548187083557906661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65047303397582778077208881 48785477548187083557906661)
  ·
    refine ⟨9147277040285078167107499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48785477548187083557906661 9147277040285078167107499)
    ·
      refine ⟨13720915560427617250661249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9147277040285078167107499 13720915560427617250661249)
      ·
        refine ⟨10290686670320712937995937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13720915560427617250661249 10290686670320712937995937)
        ·
          refine ⟨7718015002740534703496953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10290686670320712937995937 7718015002740534703496953)
          ·
            refine ⟨5788511252055401027622715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7718015002740534703496953 5788511252055401027622715)
            ·
              refine ⟨8682766878083101541434073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788511252055401027622715 8682766878083101541434073)
              ·
                refine ⟨6512075158562326156075555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682766878083101541434073 6512075158562326156075555)
                ·
                  refine ⟨9768112737843489234113333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512075158562326156075555 9768112737843489234113333)
                  ·
                    refine ⟨915760569172827115698125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9768112737843489234113333 915760569172827115698125)
                    ·
                      rfl

theorem cell22_2675156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2675156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675156 prefixEnd_2675156 := by exact prefixLift 2675156
  have htrace : WordTrace (prefixWord ++ tailWord_2675156) baseStart_2675156 baseEnd_2675156 := by
    simpa [prefixWord, tailWord_2675156, baseEnd_2675156] using wordTrace_append hprefix tailTrace_2675156
  have hstable : (prefixWord ++ tailWord_2675156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675156).length < 2 ^ (prefixWord ++ tailWord_2675156).sum := by decide
  have hdescent : baseEnd_2675156 < baseStart_2675156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675158 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2675158 : Nat := 118140960795 + 2675158 * 2 ^ 59
def prefixEnd_2675158 : Nat := 4983230072969 + 3 ^ 40 * 2675158 * 2
def baseEnd_2675158 : Nat := 305253751271233259049373

theorem tailTrace_2675158 : CollatzResearch.WordTrace tailWord_2675158 prefixEnd_2675158 305253751271233259049373 := by
  unfold tailWord_2675158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098189252647932591086633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65047352028244614304924085 6098189252647932591086633)
  ·
    refine ⟨4573641939485949443314975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6098189252647932591086633 4573641939485949443314975)
    ·
      refine ⟨6860462909228924164972463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573641939485949443314975 6860462909228924164972463)
      ·
        refine ⟨10290694363843386247458695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860462909228924164972463 10290694363843386247458695)
        ·
          refine ⟨15436041545765079371188043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290694363843386247458695 15436041545765079371188043)
          ·
            refine ⟨23154062318647619056782065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15436041545765079371188043 23154062318647619056782065)
            ·
              refine ⟨17365546738985714292586549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23154062318647619056782065 17365546738985714292586549)
              ·
                refine ⟨1628020006779910714929989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17365546738985714292586549 1628020006779910714929989)
                ·
                  refine ⟨305253751271233259049373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628020006779910714929989 305253751271233259049373)
                  ·
                    rfl

theorem cell22_2675158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2675158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675158 prefixEnd_2675158 := by exact prefixLift 2675158
  have htrace : WordTrace (prefixWord ++ tailWord_2675158) baseStart_2675158 baseEnd_2675158 := by
    simpa [prefixWord, tailWord_2675158, baseEnd_2675158] using wordTrace_append hprefix tailTrace_2675158
  have hstable : (prefixWord ++ tailWord_2675158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675158).length < 2 ^ (prefixWord ++ tailWord_2675158).sum := by decide
  have hdescent : baseEnd_2675158 < baseStart_2675158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675201 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2675201 : Nat := 118140960795 + 2675201 * 2 ^ 59
def prefixEnd_2675201 : Nat := 4983230072969 + 3 ^ 40 * 2675201 * 2
def baseEnd_2675201 : Nat := 915775973592461998322987

theorem tailTrace_2675201 : CollatzResearch.WordTrace tailWord_2675201 prefixEnd_2675201 915775973592461998322987 := by
  unfold tailWord_2675201
  simp only [CollatzResearch.WordTrace]
  refine ⟨97572596381211139801201457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65048397587474093200800971 97572596381211139801201457)
  ·
    refine ⟨73179447285908354850901093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97572596381211139801201457 73179447285908354850901093)
    ·
      refine ⟨13721146366107816534543955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73179447285908354850901093 13721146366107816534543955)
      ·
        refine ⟨20581719549161724801815933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13721146366107816534543955 20581719549161724801815933)
        ·
          refine ⟨7718144830935646800680975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20581719549161724801815933 7718144830935646800680975)
          ·
            refine ⟨11577217246403470201021463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718144830935646800680975 11577217246403470201021463)
            ·
              refine ⟨17365825869605205301532195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577217246403470201021463 17365825869605205301532195)
              ·
                refine ⟨26048738804407807952298293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17365825869605205301532195 26048738804407807952298293)
                ·
                  refine ⟨2442069262913231995527965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26048738804407807952298293 2442069262913231995527965)
                  ·
                    refine ⟨915775973592461998322987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442069262913231995527965 915775973592461998322987)
                    ·
                      rfl

theorem cell22_2675201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2675201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675201 prefixEnd_2675201 := by exact prefixLift 2675201
  have htrace : WordTrace (prefixWord ++ tailWord_2675201) baseStart_2675201 baseEnd_2675201 := by
    simpa [prefixWord, tailWord_2675201, baseEnd_2675201] using wordTrace_append hprefix tailTrace_2675201
  have hstable : (prefixWord ++ tailWord_2675201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675201).length < 2 ^ (prefixWord ++ tailWord_2675201).sum := by decide
  have hdescent : baseEnd_2675201 < baseStart_2675201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675244 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_2675244 : Nat := 118140960795 + 2675244 * 2 ^ 59
def prefixEnd_2675244 : Nat := 4983230072969 + 3 ^ 40 * 2675244 * 2
def baseEnd_2675244 : Nat := 915790693371224219497855

theorem tailTrace_2675244 : CollatzResearch.WordTrace tailWord_2675244 prefixEnd_2675244 915790693371224219497855 := by
  unfold tailWord_2675244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48787082360027679072508393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65049443146703572096677857 48787082360027679072508393)
  ·
    refine ⟨36590311770020759304381295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48787082360027679072508393 36590311770020759304381295)
    ·
      refine ⟨54885467655031138956571943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36590311770020759304381295 54885467655031138956571943)
      ·
        refine ⟨82328201482546708434857915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54885467655031138956571943 82328201482546708434857915)
        ·
          refine ⟨123492302223820062652286873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82328201482546708434857915 123492302223820062652286873)
          ·
            refine ⟨92619226667865046989215155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123492302223820062652286873 92619226667865046989215155)
            ·
              refine ⟨138928840001797570483822733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92619226667865046989215155 138928840001797570483822733)
              ·
                refine ⟨52098315000674088931433525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138928840001797570483822733 52098315000674088931433525)
                ·
                  refine ⟨4884217031313195837321893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52098315000674088931433525 4884217031313195837321893)
                  ·
                    refine ⟨915790693371224219497855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4884217031313195837321893 915790693371224219497855)
                    ·
                      rfl

theorem cell22_2675244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_2675244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675244 prefixEnd_2675244 := by exact prefixLift 2675244
  have htrace : WordTrace (prefixWord ++ tailWord_2675244) baseStart_2675244 baseEnd_2675244 := by
    simpa [prefixWord, tailWord_2675244, baseEnd_2675244] using wordTrace_append hprefix tailTrace_2675244
  have hstable : (prefixWord ++ tailWord_2675244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675244).length < 2 ^ (prefixWord ++ tailWord_2675244).sum := by decide
  have hdescent : baseEnd_2675244 < baseStart_2675244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675306 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2675306 : Nat := 118140960795 + 2675306 * 2 ^ 59
def prefixEnd_2675306 : Nat := 4983230072969 + 3 ^ 40 * 2675306 * 2
def baseEnd_2675306 : Nat := 915811917238276724447665

theorem tailTrace_2675306 : CollatzResearch.WordTrace tailWord_2675306 prefixEnd_2675306 915811917238276724447665 := by
  unfold tailWord_2675306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24394106511457685683443443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65050950697220495155849181 24394106511457685683443443)
  ·
    refine ⟨36591159767186528525165165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24394106511457685683443443 36591159767186528525165165)
    ·
      refine ⟨13721684912694948196936937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36591159767186528525165165 13721684912694948196936937)
      ·
        refine ⟨10291263684521211147702703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13721684912694948196936937 10291263684521211147702703)
        ·
          refine ⟨15436895526781816721554055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10291263684521211147702703 15436895526781816721554055)
          ·
            refine ⟨23155343290172725082331083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15436895526781816721554055 23155343290172725082331083)
            ·
              refine ⟨34733014935259087623496625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23155343290172725082331083 34733014935259087623496625)
              ·
                refine ⟨26049761201444315717622469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34733014935259087623496625 26049761201444315717622469)
                ·
                  refine ⟨4884330225270809197054213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26049761201444315717622469 4884330225270809197054213)
                  ·
                    refine ⟨915811917238276724447665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4884330225270809197054213 915811917238276724447665)
                    ·
                      rfl

theorem cell22_2675306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2675306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675306 prefixEnd_2675306 := by exact prefixLift 2675306
  have htrace : WordTrace (prefixWord ++ tailWord_2675306) baseStart_2675306 baseEnd_2675306 := by
    simpa [prefixWord, tailWord_2675306, baseEnd_2675306] using wordTrace_append hprefix tailTrace_2675306
  have hstable : (prefixWord ++ tailWord_2675306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675306).length < 2 ^ (prefixWord ++ tailWord_2675306).sum := by decide
  have hdescent : baseEnd_2675306 < baseStart_2675306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675319 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2675319 : Nat := 118140960795 + 2675319 * 2 ^ 59
def prefixEnd_2675319 : Nat := 4983230072969 + 3 ^ 40 * 2675319 * 2
def baseEnd_2675319 : Nat := 915816367403949023872625

theorem tailTrace_2675319 : CollatzResearch.WordTrace tailWord_2675319 prefixEnd_2675319 915816367403949023872625 := by
  unfold tailWord_2675319
  simp only [CollatzResearch.WordTrace]
  refine ⟨97576900194783645953997011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65051266796522430635998007 97576900194783645953997011)
  ·
    refine ⟨146365350292175468930995517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97576900194783645953997011 146365350292175468930995517)
    ·
      refine ⟨54887006359565800849123319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146365350292175468930995517 54887006359565800849123319)
      ·
        refine ⟨82330509539348701273684979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54887006359565800849123319 82330509539348701273684979)
        ·
          refine ⟨123495764309023051910527469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82330509539348701273684979 123495764309023051910527469)
          ·
            refine ⟨46310911615883644466447801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123495764309023051910527469 46310911615883644466447801)
            ·
              refine ⟨34733183711912733349835851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46310911615883644466447801 34733183711912733349835851)
              ·
                refine ⟨52099775567869100024753777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34733183711912733349835851 52099775567869100024753777)
                ·
                  refine ⟨39074831675901825018565333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52099775567869100024753777 39074831675901825018565333)
                  ·
                    refine ⟨915816367403949023872625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39074831675901825018565333 915816367403949023872625)
                    ·
                      rfl

theorem cell22_2675319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2675319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675319 prefixEnd_2675319 := by exact prefixLift 2675319
  have htrace : WordTrace (prefixWord ++ tailWord_2675319) baseStart_2675319 baseEnd_2675319 := by
    simpa [prefixWord, tailWord_2675319, baseEnd_2675319] using wordTrace_append hprefix tailTrace_2675319
  have hstable : (prefixWord ++ tailWord_2675319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675319).length < 2 ^ (prefixWord ++ tailWord_2675319).sum := by decide
  have hdescent : baseEnd_2675319 < baseStart_2675319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675441 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2675441 : Nat := 118140960795 + 2675441 * 2 ^ 59
def prefixEnd_2675441 : Nat := 4983230072969 + 3 ^ 40 * 2675441 * 2
def baseEnd_2675441 : Nat := 915858130497181372322251

theorem tailTrace_2675441 : CollatzResearch.WordTrace tailWord_2675441 prefixEnd_2675441 915858130497181372322251 := by
  unfold tailWord_2675441
  simp only [CollatzResearch.WordTrace]
  refine ⟨97581349900341660789938177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65054233266894440526625451 97581349900341660789938177)
  ·
    refine ⟨73186012425256245592453633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97581349900341660789938177 73186012425256245592453633)
    ·
      refine ⟨54889509318942184194340225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73186012425256245592453633 54889509318942184194340225)
      ·
        refine ⟨41167131989206638145755169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54889509318942184194340225 41167131989206638145755169)
        ·
          refine ⟨30875348991904978609316377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41167131989206638145755169 30875348991904978609316377)
          ·
            refine ⟨23156511743928733956987283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30875348991904978609316377 23156511743928733956987283)
            ·
              refine ⟨34734767615893100935480925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23156511743928733956987283 34734767615893100935480925)
              ·
                refine ⟨13025537855959912850805347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34734767615893100935480925 13025537855959912850805347)
                ·
                  refine ⟨19538306783939869276208021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13025537855959912850805347 19538306783939869276208021)
                  ·
                    refine ⟨915858130497181372322251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19538306783939869276208021 915858130497181372322251)
                    ·
                      rfl

theorem cell22_2675441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2675441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675441 prefixEnd_2675441 := by exact prefixLift 2675441
  have htrace : WordTrace (prefixWord ++ tailWord_2675441) baseStart_2675441 baseEnd_2675441 := by
    simpa [prefixWord, tailWord_2675441, baseEnd_2675441] using wordTrace_append hprefix tailTrace_2675441
  have hstable : (prefixWord ++ tailWord_2675441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675441).length < 2 ^ (prefixWord ++ tailWord_2675441).sum := by decide
  have hdescent : baseEnd_2675441 < baseStart_2675441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675460 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2675460 : Nat := 118140960795 + 2675460 * 2 ^ 59
def prefixEnd_2675460 : Nat := 4983230072969 + 3 ^ 40 * 2675460 * 2
def baseEnd_2675460 : Nat := 915864634585471656097193

theorem tailTrace_2675460 : CollatzResearch.WordTrace tailWord_2675460 prefixEnd_2675460 915864634585471656097193 := by
  unfold tailWord_2675460
  simp only [CollatzResearch.WordTrace]
  refine ⟨48791021443636413517439917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65054695258181884689919889 48791021443636413517439917)
  ·
    refine ⟨18296633041363655069039969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48791021443636413517439917 18296633041363655069039969)
    ·
      refine ⟨13722474781022741301779977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18296633041363655069039969 13722474781022741301779977)
      ·
        refine ⟨10291856085767055976334983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13722474781022741301779977 10291856085767055976334983)
        ·
          refine ⟨15437784128650583964502475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10291856085767055976334983 15437784128650583964502475)
          ·
            refine ⟨23156676192975875946753713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15437784128650583964502475 23156676192975875946753713)
            ·
              refine ⟨17367507144731906960065285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23156676192975875946753713 17367507144731906960065285)
              ·
                refine ⟨3256407589637232555012241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17367507144731906960065285 3256407589637232555012241)
                ·
                  refine ⟨2442305692227924416259181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3256407589637232555012241 2442305692227924416259181)
                  ·
                    refine ⟨915864634585471656097193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442305692227924416259181 915864634585471656097193)
                    ·
                      rfl

theorem cell22_2675460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2675460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675460 prefixEnd_2675460 := by exact prefixLift 2675460
  have htrace : WordTrace (prefixWord ++ tailWord_2675460) baseStart_2675460 baseEnd_2675460 := by
    simpa [prefixWord, tailWord_2675460, baseEnd_2675460] using wordTrace_append hprefix tailTrace_2675460
  have hstable : (prefixWord ++ tailWord_2675460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675460).length < 2 ^ (prefixWord ++ tailWord_2675460).sum := by decide
  have hdescent : baseEnd_2675460 < baseStart_2675460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
