Theory vfmTest0849[no_sig_docs]
Ancestors vfmTestDefs0849
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0849_0.nsv", "result0849_1.nsv", "result0849_2.nsv", "result0849_3.nsv", "result0849_4.nsv", "result0849_5.nsv", "result0849_6.nsv", "result0849_7.nsv", "result0849_8.nsv", "result0849_9.nsv", "result0849_10.nsv", "result0849_11.nsv", "result0849_12.nsv", "result0849_13.nsv", "result0849_14.nsv", "result0849_15.nsv", "result0849_16.nsv", "result0849_17.nsv", "result0849_18.nsv", "result0849_19.nsv", "result0849_20.nsv", "result0849_21.nsv", "result0849_22.nsv", "result0849_23.nsv", "result0849_24.nsv"];
val thyn = "vfmTestDefs0849";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
