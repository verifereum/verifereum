Theory vfmTest0904[no_sig_docs]
Ancestors vfmTestDefs0904
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0904_0.nsv", "result0904_1.nsv", "result0904_2.nsv", "result0904_3.nsv", "result0904_4.nsv", "result0904_5.nsv", "result0904_6.nsv", "result0904_7.nsv", "result0904_8.nsv", "result0904_9.nsv", "result0904_10.nsv", "result0904_11.nsv", "result0904_12.nsv", "result0904_13.nsv", "result0904_14.nsv", "result0904_15.nsv", "result0904_16.nsv", "result0904_17.nsv", "result0904_18.nsv", "result0904_19.nsv", "result0904_20.nsv", "result0904_21.nsv", "result0904_22.nsv", "result0904_23.nsv", "result0904_24.nsv", "result0904_25.nsv", "result0904_26.nsv", "result0904_27.nsv", "result0904_28.nsv", "result0904_29.nsv", "result0904_30.nsv", "result0904_31.nsv", "result0904_32.nsv", "result0904_33.nsv", "result0904_34.nsv", "result0904_35.nsv"];
val thyn = "vfmTestDefs0904";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
