Theory vfmTest1753[no_sig_docs]
Ancestors vfmTestDefs1753
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1753_0.nsv", "result1753_1.nsv", "result1753_2.nsv", "result1753_3.nsv", "result1753_4.nsv", "result1753_5.nsv", "result1753_6.nsv", "result1753_7.nsv", "result1753_8.nsv", "result1753_9.nsv", "result1753_10.nsv", "result1753_11.nsv", "result1753_12.nsv", "result1753_13.nsv", "result1753_14.nsv", "result1753_15.nsv"];
val thyn = "vfmTestDefs1753";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
