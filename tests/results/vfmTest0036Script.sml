Theory vfmTest0036[no_sig_docs]
Ancestors vfmTestDefs0036
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0036_0.nsv", "result0036_1.nsv", "result0036_2.nsv", "result0036_3.nsv", "result0036_4.nsv", "result0036_5.nsv", "result0036_6.nsv", "result0036_7.nsv", "result0036_8.nsv", "result0036_9.nsv", "result0036_10.nsv", "result0036_11.nsv", "result0036_12.nsv", "result0036_13.nsv", "result0036_14.nsv", "result0036_15.nsv", "result0036_16.nsv", "result0036_17.nsv", "result0036_18.nsv", "result0036_19.nsv", "result0036_20.nsv", "result0036_21.nsv", "result0036_22.nsv", "result0036_23.nsv", "result0036_24.nsv", "result0036_25.nsv", "result0036_26.nsv", "result0036_27.nsv", "result0036_28.nsv", "result0036_29.nsv", "result0036_30.nsv", "result0036_31.nsv", "result0036_32.nsv", "result0036_33.nsv", "result0036_34.nsv", "result0036_35.nsv"];
val thyn = "vfmTestDefs0036";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
