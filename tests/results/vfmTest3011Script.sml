Theory vfmTest3011[no_sig_docs]
Ancestors vfmTestDefs3011
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3011_0.nsv", "result3011_1.nsv", "result3011_2.nsv", "result3011_3.nsv", "result3011_4.nsv", "result3011_5.nsv", "result3011_6.nsv", "result3011_7.nsv", "result3011_8.nsv", "result3011_9.nsv", "result3011_10.nsv", "result3011_11.nsv", "result3011_12.nsv", "result3011_13.nsv", "result3011_14.nsv", "result3011_15.nsv", "result3011_16.nsv", "result3011_17.nsv", "result3011_18.nsv", "result3011_19.nsv", "result3011_20.nsv", "result3011_21.nsv", "result3011_22.nsv", "result3011_23.nsv", "result3011_24.nsv", "result3011_25.nsv", "result3011_26.nsv"];
val thyn = "vfmTestDefs3011";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
