Theory vfmTest0034[no_sig_docs]
Ancestors vfmTestDefs0034
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0034_0.nsv", "result0034_1.nsv", "result0034_2.nsv", "result0034_3.nsv", "result0034_4.nsv", "result0034_5.nsv", "result0034_6.nsv", "result0034_7.nsv", "result0034_8.nsv", "result0034_9.nsv", "result0034_10.nsv", "result0034_11.nsv", "result0034_12.nsv", "result0034_13.nsv", "result0034_14.nsv", "result0034_15.nsv", "result0034_16.nsv", "result0034_17.nsv", "result0034_18.nsv", "result0034_19.nsv", "result0034_20.nsv", "result0034_21.nsv", "result0034_22.nsv", "result0034_23.nsv", "result0034_24.nsv", "result0034_25.nsv", "result0034_26.nsv", "result0034_27.nsv", "result0034_28.nsv", "result0034_29.nsv", "result0034_30.nsv", "result0034_31.nsv", "result0034_32.nsv", "result0034_33.nsv", "result0034_34.nsv", "result0034_35.nsv"];
val thyn = "vfmTestDefs0034";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
