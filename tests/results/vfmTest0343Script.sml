Theory vfmTest0343[no_sig_docs]
Ancestors vfmTestDefs0343
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0343_0.nsv", "result0343_1.nsv", "result0343_2.nsv", "result0343_3.nsv", "result0343_4.nsv", "result0343_5.nsv", "result0343_6.nsv", "result0343_7.nsv", "result0343_8.nsv", "result0343_9.nsv", "result0343_10.nsv", "result0343_11.nsv", "result0343_12.nsv", "result0343_13.nsv", "result0343_14.nsv", "result0343_15.nsv", "result0343_16.nsv", "result0343_17.nsv", "result0343_18.nsv", "result0343_19.nsv", "result0343_20.nsv", "result0343_21.nsv", "result0343_22.nsv", "result0343_23.nsv", "result0343_24.nsv", "result0343_25.nsv", "result0343_26.nsv", "result0343_27.nsv", "result0343_28.nsv", "result0343_29.nsv"];
val thyn = "vfmTestDefs0343";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
