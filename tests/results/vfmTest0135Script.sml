Theory vfmTest0135[no_sig_docs]
Ancestors vfmTestDefs0135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0135_0.nsv", "result0135_1.nsv", "result0135_2.nsv", "result0135_3.nsv", "result0135_4.nsv", "result0135_5.nsv", "result0135_6.nsv", "result0135_7.nsv", "result0135_8.nsv", "result0135_9.nsv", "result0135_10.nsv", "result0135_11.nsv", "result0135_12.nsv", "result0135_13.nsv", "result0135_14.nsv", "result0135_15.nsv", "result0135_16.nsv", "result0135_17.nsv"];
val thyn = "vfmTestDefs0135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
