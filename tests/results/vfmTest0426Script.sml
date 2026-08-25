Theory vfmTest0426[no_sig_docs]
Ancestors vfmTestDefs0426
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0426_0.nsv", "result0426_1.nsv", "result0426_2.nsv", "result0426_3.nsv", "result0426_4.nsv", "result0426_5.nsv", "result0426_6.nsv", "result0426_7.nsv", "result0426_8.nsv", "result0426_9.nsv", "result0426_10.nsv", "result0426_11.nsv", "result0426_12.nsv", "result0426_13.nsv", "result0426_14.nsv", "result0426_15.nsv"];
val thyn = "vfmTestDefs0426";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
