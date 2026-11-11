Theory vfmTest0328[no_sig_docs]
Ancestors vfmTestDefs0328
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0328_0.nsv", "result0328_1.nsv", "result0328_2.nsv", "result0328_3.nsv", "result0328_4.nsv", "result0328_5.nsv", "result0328_6.nsv", "result0328_7.nsv", "result0328_8.nsv", "result0328_9.nsv", "result0328_10.nsv", "result0328_11.nsv", "result0328_12.nsv", "result0328_13.nsv", "result0328_14.nsv", "result0328_15.nsv", "result0328_16.nsv", "result0328_17.nsv", "result0328_18.nsv", "result0328_19.nsv", "result0328_20.nsv", "result0328_21.nsv", "result0328_22.nsv", "result0328_23.nsv", "result0328_24.nsv", "result0328_25.nsv", "result0328_26.nsv", "result0328_27.nsv", "result0328_28.nsv", "result0328_29.nsv"];
val thyn = "vfmTestDefs0328";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
