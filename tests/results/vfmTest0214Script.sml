Theory vfmTest0214[no_sig_docs]
Ancestors vfmTestDefs0214
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0214_0.nsv", "result0214_1.nsv", "result0214_2.nsv", "result0214_3.nsv", "result0214_4.nsv", "result0214_5.nsv", "result0214_6.nsv", "result0214_7.nsv", "result0214_8.nsv", "result0214_9.nsv", "result0214_10.nsv", "result0214_11.nsv", "result0214_12.nsv", "result0214_13.nsv", "result0214_14.nsv", "result0214_15.nsv", "result0214_16.nsv", "result0214_17.nsv", "result0214_18.nsv", "result0214_19.nsv", "result0214_20.nsv", "result0214_21.nsv", "result0214_22.nsv", "result0214_23.nsv", "result0214_24.nsv", "result0214_25.nsv", "result0214_26.nsv", "result0214_27.nsv", "result0214_28.nsv", "result0214_29.nsv"];
val thyn = "vfmTestDefs0214";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
