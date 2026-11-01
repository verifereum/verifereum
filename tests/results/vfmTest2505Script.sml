Theory vfmTest2505[no_sig_docs]
Ancestors vfmTestDefs2505
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2505_0.nsv", "result2505_1.nsv", "result2505_2.nsv", "result2505_3.nsv", "result2505_4.nsv", "result2505_5.nsv", "result2505_6.nsv", "result2505_7.nsv", "result2505_8.nsv"];
val thyn = "vfmTestDefs2505";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
