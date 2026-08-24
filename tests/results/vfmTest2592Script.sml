Theory vfmTest2592[no_sig_docs]
Ancestors vfmTestDefs2592
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2592_0.nsv", "result2592_1.nsv", "result2592_2.nsv", "result2592_3.nsv"];
val thyn = "vfmTestDefs2592";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
