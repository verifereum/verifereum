Theory vfmTest0622[no_sig_docs]
Ancestors vfmTestDefs0622
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0622_0.nsv", "result0622_1.nsv", "result0622_2.nsv", "result0622_3.nsv", "result0622_4.nsv", "result0622_5.nsv", "result0622_6.nsv", "result0622_7.nsv", "result0622_8.nsv", "result0622_9.nsv", "result0622_10.nsv", "result0622_11.nsv"];
val thyn = "vfmTestDefs0622";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
