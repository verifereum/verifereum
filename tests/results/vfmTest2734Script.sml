Theory vfmTest2734[no_sig_docs]
Ancestors vfmTestDefs2734
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2734_0.nsv", "result2734_1.nsv", "result2734_2.nsv", "result2734_3.nsv"];
val thyn = "vfmTestDefs2734";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
