Theory vfmTest1115[no_sig_docs]
Ancestors vfmTestDefs1115
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1115_0.nsv", "result1115_1.nsv", "result1115_2.nsv"];
val thyn = "vfmTestDefs1115";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
