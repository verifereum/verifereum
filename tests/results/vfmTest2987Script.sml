Theory vfmTest2987[no_sig_docs]
Ancestors vfmTestDefs2987
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2987_0.nsv", "result2987_1.nsv", "result2987_2.nsv", "result2987_3.nsv", "result2987_4.nsv", "result2987_5.nsv"];
val thyn = "vfmTestDefs2987";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
