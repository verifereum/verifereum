Theory vfmTest0242[no_sig_docs]
Ancestors vfmTestDefs0242
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0242_0.nsv", "result0242_1.nsv", "result0242_2.nsv", "result0242_3.nsv", "result0242_4.nsv", "result0242_5.nsv", "result0242_6.nsv", "result0242_7.nsv", "result0242_8.nsv", "result0242_9.nsv", "result0242_10.nsv", "result0242_11.nsv", "result0242_12.nsv", "result0242_13.nsv", "result0242_14.nsv", "result0242_15.nsv", "result0242_16.nsv", "result0242_17.nsv", "result0242_18.nsv", "result0242_19.nsv", "result0242_20.nsv", "result0242_21.nsv", "result0242_22.nsv", "result0242_23.nsv", "result0242_24.nsv", "result0242_25.nsv", "result0242_26.nsv", "result0242_27.nsv", "result0242_28.nsv", "result0242_29.nsv", "result0242_30.nsv", "result0242_31.nsv"];
val thyn = "vfmTestDefs0242";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
