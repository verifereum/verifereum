Theory vfmTest2376[no_sig_docs]
Ancestors vfmTestDefs2376
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2376_0.nsv", "result2376_1.nsv", "result2376_2.nsv", "result2376_3.nsv", "result2376_4.nsv", "result2376_5.nsv", "result2376_6.nsv", "result2376_7.nsv"];
val thyn = "vfmTestDefs2376";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
