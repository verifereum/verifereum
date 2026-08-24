Theory vfmTest2694[no_sig_docs]
Ancestors vfmTestDefs2694
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2694_0.nsv", "result2694_1.nsv", "result2694_2.nsv", "result2694_3.nsv"];
val thyn = "vfmTestDefs2694";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
