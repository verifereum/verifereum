Theory vfmTest3127[no_sig_docs]
Ancestors vfmTestDefs3127
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3127_0.nsv", "result3127_1.nsv", "result3127_2.nsv", "result3127_3.nsv", "result3127_4.nsv", "result3127_5.nsv", "result3127_6.nsv", "result3127_7.nsv", "result3127_8.nsv", "result3127_9.nsv", "result3127_10.nsv", "result3127_11.nsv", "result3127_12.nsv", "result3127_13.nsv", "result3127_14.nsv", "result3127_15.nsv", "result3127_16.nsv", "result3127_17.nsv", "result3127_18.nsv", "result3127_19.nsv", "result3127_20.nsv", "result3127_21.nsv", "result3127_22.nsv"];
val thyn = "vfmTestDefs3127";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
