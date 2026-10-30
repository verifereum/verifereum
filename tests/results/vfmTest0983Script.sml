Theory vfmTest0983[no_sig_docs]
Ancestors vfmTestDefs0983
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0983_0.nsv", "result0983_1.nsv", "result0983_2.nsv", "result0983_3.nsv", "result0983_4.nsv", "result0983_5.nsv", "result0983_6.nsv", "result0983_7.nsv", "result0983_8.nsv", "result0983_9.nsv", "result0983_10.nsv", "result0983_11.nsv", "result0983_12.nsv", "result0983_13.nsv", "result0983_14.nsv", "result0983_15.nsv", "result0983_16.nsv", "result0983_17.nsv"];
val thyn = "vfmTestDefs0983";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
