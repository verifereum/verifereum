Theory vfmTest2703[no_sig_docs]
Ancestors vfmTestDefs2703
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2703_0.nsv", "result2703_1.nsv", "result2703_2.nsv", "result2703_3.nsv"];
val thyn = "vfmTestDefs2703";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
