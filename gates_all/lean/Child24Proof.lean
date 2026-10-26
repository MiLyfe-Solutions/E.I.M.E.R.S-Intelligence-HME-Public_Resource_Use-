import BoundedDescent

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace EimersChild24
open CollatzResearch

-- Generated from an independently replayed exact trace, not a sampled lift.
def child_word : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 1, 5]

theorem child_q8388658_trace : WordTrace child_word 4835732101496250010959899 2153706800091972785348135 := by
  unfold child_word
  refine ⟨7253598152244375016439849, (by decide +kernel), ?_⟩
  refine ⟨5440198614183281262329887, (by decide +kernel), ?_⟩
  refine ⟨8160297921274921893494831, (by decide +kernel), ?_⟩
  refine ⟨12240446881912382840242247, (by decide +kernel), ?_⟩
  refine ⟨18360670322868574260363371, (by decide +kernel), ?_⟩
  refine ⟨27541005484302861390545057, (by decide +kernel), ?_⟩
  refine ⟨20655754113227146042908793, (by decide +kernel), ?_⟩
  refine ⟨15491815584920359532181595, (by decide +kernel), ?_⟩
  refine ⟨23237723377380539298272393, (by decide +kernel), ?_⟩
  refine ⟨17428292533035404473704295, (by decide +kernel), ?_⟩
  refine ⟨26142438799553106710556443, (by decide +kernel), ?_⟩
  refine ⟨39213658199329660065834665, (by decide +kernel), ?_⟩
  refine ⟨29410243649497245049375999, (by decide +kernel), ?_⟩
  refine ⟨44115365474245867574063999, (by decide +kernel), ?_⟩
  refine ⟨66173048211368801361095999, (by decide +kernel), ?_⟩
  refine ⟨99259572317053202041643999, (by decide +kernel), ?_⟩
  refine ⟨148889358475579803062465999, (by decide +kernel), ?_⟩
  refine ⟨223334037713369704593698999, (by decide +kernel), ?_⟩
  refine ⟨335001056570054556890548499, (by decide +kernel), ?_⟩
  refine ⟨502501584855081835335822749, (by decide +kernel), ?_⟩
  refine ⟨188438094320655688250933531, (by decide +kernel), ?_⟩
  refine ⟨282657141480983532376400297, (by decide +kernel), ?_⟩
  refine ⟨211992856110737649282300223, (by decide +kernel), ?_⟩
  refine ⟨317989284166106473923450335, (by decide +kernel), ?_⟩
  refine ⟨476983926249159710885175503, (by decide +kernel), ?_⟩
  refine ⟨715475889373739566327763255, (by decide +kernel), ?_⟩
  refine ⟨1073213834060609349491644883, (by decide +kernel), ?_⟩
  refine ⟨1609820751090914024237467325, (by decide +kernel), ?_⟩
  refine ⟨603682781659092759089050247, (by decide +kernel), ?_⟩
  refine ⟨905524172488639138633575371, (by decide +kernel), ?_⟩
  refine ⟨1358286258732958707950363057, (by decide +kernel), ?_⟩
  refine ⟨1018714694049719030962772293, (by decide +kernel), ?_⟩
  refine ⟨191009005134322318305519805, (by decide +kernel), ?_⟩
  refine ⟨71628376925370869364569927, (by decide +kernel), ?_⟩
  refine ⟨107442565388056304046854891, (by decide +kernel), ?_⟩
  refine ⟨161163848082084456070282337, (by decide +kernel), ?_⟩
  refine ⟨120872886061563342052711753, (by decide +kernel), ?_⟩
  refine ⟨90654664546172506539533815, (by decide +kernel), ?_⟩
  refine ⟨135981996819258759809300723, (by decide +kernel), ?_⟩
  refine ⟨203972995228888139713951085, (by decide +kernel), ?_⟩
  refine ⟨76489873210833052392731657, (by decide +kernel), ?_⟩
  refine ⟨57367404908124789294548743, (by decide +kernel), ?_⟩
  refine ⟨86051107362187183941823115, (by decide +kernel), ?_⟩
  refine ⟨129076661043280775912734673, (by decide +kernel), ?_⟩
  refine ⟨96807495782460581934551005, (by decide +kernel), ?_⟩
  refine ⟨36302810918422718225456627, (by decide +kernel), ?_⟩
  refine ⟨54454216377634077338184941, (by decide +kernel), ?_⟩
  refine ⟨20420331141612779001819353, (by decide +kernel), ?_⟩
  refine ⟨15315248356209584251364515, (by decide +kernel), ?_⟩
  refine ⟨22972872534314376377046773, (by decide +kernel), ?_⟩
  refine ⟨2153706800091972785348135, (by decide +kernel), ?_⟩
  rfl

theorem child_time : child_word.sum + child_word.length = 133 := by decide +kernel

theorem child_q8388658_family_descent :
    ∀ u : Nat, ∃ endpoint, ordinaryRun 133 (4835732101496250010959899 + u * 2^83) = endpoint ∧
      endpoint < 4835732101496250010959899 + u * 2^83 := by
  have htrace : BoundedWordTrace child_word 4835732101496250010959899 2153706800091972785348135 :=
    ⟨2153706800091972785348135, child_q8388658_trace, Nat.le_refl _, (by decide +kernel)⟩
  have result := family_descent_by_bound child_word
    4835732101496250010959899 2153706800091972785348135 htrace (by decide +kernel) (by decide +kernel)
  simpa only [child_time, LIFT_BITS] using result

theorem child_q8388658_exact_endpoint (u : Nat) :
    ordinaryRun 133 (4835732101496250010959899 + u * 2^83) = 2153706800091972785348135 + 4307387926151115532621494 * u := by
  have lifted := word_trace_lift child_word (b := 83) (q := u)
    child_q8388658_trace (by decide +kernel)
  have hk : child_word.length = 51 := by decide +kernel
  have hS : child_word.sum = 82 := by decide +kernel
  have hc : 3^51 * 2^(83-82) = 4307387926151115532621494 := by decide +kernel
  have hr : 3^child_word.length * u * 2^(83-child_word.sum) = 4307387926151115532621494 * u := by
    rw [hk, hS]
    calc
      3^51 * u * 2^(83-82) = (3^51 * 2^(83-82)) * u := by ac_rfl
      _ = 4307387926151115532621494 * u := by rw [hc]
  have result := wordTrace_ordinary lifted
  rw [child_time, hr] at result
  exact result

theorem child_q8388658_ordinary_descent (u : Nat) :
    ordinaryRun 133 (4835732101496250010959899 + u * 2^83) < 4835732101496250010959899 + u * 2^83 := by
  rcases child_q8388658_family_descent u with ⟨endpoint, heq, hlt⟩
  rw [heq]
  exact hlt

theorem child_q8388658_coordinate_bridge (u : Nat) :
    118140960795 + (8388658 + u * 2^24) * 2^59 = 4835732101496250010959899 + u * 2^83 := by
  change 118140960795 + (8388658 + u * 16777216) * 576460752303423488 = 4835732101496250010959899 + u * 9671406556917033397649408
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

theorem child_q8388658_trunk_descent (u : Nat) :
    ordinaryRun 133 (118140960795 + (8388658 + u * 2^24) * 2^59)
      < 118140960795 + (8388658 + u * 2^24) * 2^59 := by
  rw [child_q8388658_coordinate_bridge]
  exact child_q8388658_ordinary_descent u

#check child_q8388658_trace
#print axioms child_q8388658_trace
#check child_q8388658_family_descent
#print axioms child_q8388658_family_descent
#check child_q8388658_exact_endpoint
#print axioms child_q8388658_exact_endpoint
#check child_q8388658_ordinary_descent
#print axioms child_q8388658_ordinary_descent
#check child_q8388658_coordinate_bridge
#print axioms child_q8388658_coordinate_bridge
#check child_q8388658_trunk_descent
#print axioms child_q8388658_trunk_descent

end EimersChild24
