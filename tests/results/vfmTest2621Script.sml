Theory vfmTest2621[no_sig_docs]
Ancestors vfmTestDefs2621
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2621_0.nsv", "result2621_1.nsv", "result2621_2.nsv", "result2621_3.nsv"];
val thyn = "vfmTestDefs2621";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
