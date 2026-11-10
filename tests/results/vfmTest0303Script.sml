Theory vfmTest0303[no_sig_docs]
Ancestors vfmTestDefs0303
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0303_0.nsv", "result0303_1.nsv", "result0303_2.nsv", "result0303_3.nsv", "result0303_4.nsv", "result0303_5.nsv", "result0303_6.nsv", "result0303_7.nsv", "result0303_8.nsv", "result0303_9.nsv", "result0303_10.nsv", "result0303_11.nsv"];
val thyn = "vfmTestDefs0303";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
