Theory vfmTest0015[no_sig_docs]
Ancestors vfmTestDefs0015
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0015_0.nsv", "result0015_1.nsv", "result0015_2.nsv", "result0015_3.nsv", "result0015_4.nsv", "result0015_5.nsv", "result0015_6.nsv", "result0015_7.nsv", "result0015_8.nsv", "result0015_9.nsv", "result0015_10.nsv", "result0015_11.nsv", "result0015_12.nsv", "result0015_13.nsv", "result0015_14.nsv", "result0015_15.nsv", "result0015_16.nsv", "result0015_17.nsv", "result0015_18.nsv", "result0015_19.nsv", "result0015_20.nsv", "result0015_21.nsv", "result0015_22.nsv", "result0015_23.nsv", "result0015_24.nsv", "result0015_25.nsv", "result0015_26.nsv", "result0015_27.nsv", "result0015_28.nsv", "result0015_29.nsv"];
val thyn = "vfmTestDefs0015";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
