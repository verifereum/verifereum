Theory vfmTest0274[no_sig_docs]
Ancestors vfmTestDefs0274
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0274_0.nsv", "result0274_1.nsv", "result0274_2.nsv", "result0274_3.nsv", "result0274_4.nsv", "result0274_5.nsv", "result0274_6.nsv", "result0274_7.nsv", "result0274_8.nsv", "result0274_9.nsv", "result0274_10.nsv", "result0274_11.nsv", "result0274_12.nsv", "result0274_13.nsv", "result0274_14.nsv"];
val thyn = "vfmTestDefs0274";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
