Theory vfmTest2994[no_sig_docs]
Ancestors vfmTestDefs2994
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2994_0.nsv", "result2994_1.nsv", "result2994_2.nsv", "result2994_3.nsv", "result2994_4.nsv", "result2994_5.nsv"];
val thyn = "vfmTestDefs2994";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
