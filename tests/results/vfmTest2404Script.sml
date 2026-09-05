Theory vfmTest2404[no_sig_docs]
Ancestors vfmTestDefs2404
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2404_0.nsv", "result2404_1.nsv", "result2404_2.nsv", "result2404_3.nsv", "result2404_4.nsv", "result2404_5.nsv"];
val thyn = "vfmTestDefs2404";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
