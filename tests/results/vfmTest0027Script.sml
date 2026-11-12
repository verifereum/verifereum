Theory vfmTest0027[no_sig_docs]
Ancestors vfmTestDefs0027
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0027_0.nsv", "result0027_1.nsv", "result0027_2.nsv", "result0027_3.nsv", "result0027_4.nsv", "result0027_5.nsv", "result0027_6.nsv", "result0027_7.nsv", "result0027_8.nsv", "result0027_9.nsv", "result0027_10.nsv", "result0027_11.nsv", "result0027_12.nsv", "result0027_13.nsv", "result0027_14.nsv", "result0027_15.nsv", "result0027_16.nsv", "result0027_17.nsv", "result0027_18.nsv", "result0027_19.nsv", "result0027_20.nsv", "result0027_21.nsv", "result0027_22.nsv", "result0027_23.nsv", "result0027_24.nsv", "result0027_25.nsv", "result0027_26.nsv", "result0027_27.nsv", "result0027_28.nsv", "result0027_29.nsv", "result0027_30.nsv", "result0027_31.nsv", "result0027_32.nsv"];
val thyn = "vfmTestDefs0027";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
