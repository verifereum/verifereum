Theory vfmTest2780[no_sig_docs]
Ancestors vfmTestDefs2780
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2780_0.nsv", "result2780_1.nsv", "result2780_2.nsv", "result2780_3.nsv"];
val thyn = "vfmTestDefs2780";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
