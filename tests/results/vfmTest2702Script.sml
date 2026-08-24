Theory vfmTest2702[no_sig_docs]
Ancestors vfmTestDefs2702
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2702_0.nsv", "result2702_1.nsv", "result2702_2.nsv", "result2702_3.nsv"];
val thyn = "vfmTestDefs2702";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
