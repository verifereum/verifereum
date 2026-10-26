Theory vfmTest2958[no_sig_docs]
Ancestors vfmTestDefs2958
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2958_0.nsv", "result2958_1.nsv", "result2958_2.nsv", "result2958_3.nsv", "result2958_4.nsv", "result2958_5.nsv", "result2958_6.nsv", "result2958_7.nsv", "result2958_8.nsv", "result2958_9.nsv", "result2958_10.nsv"];
val thyn = "vfmTestDefs2958";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
