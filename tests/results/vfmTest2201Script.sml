Theory vfmTest2201[no_sig_docs]
Ancestors vfmTestDefs2201
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2201_0.nsv", "result2201_1.nsv", "result2201_2.nsv", "result2201_3.nsv", "result2201_4.nsv", "result2201_5.nsv", "result2201_6.nsv", "result2201_7.nsv", "result2201_8.nsv", "result2201_9.nsv", "result2201_10.nsv", "result2201_11.nsv", "result2201_12.nsv", "result2201_13.nsv", "result2201_14.nsv", "result2201_15.nsv", "result2201_16.nsv", "result2201_17.nsv", "result2201_18.nsv", "result2201_19.nsv", "result2201_20.nsv", "result2201_21.nsv", "result2201_22.nsv", "result2201_23.nsv", "result2201_24.nsv", "result2201_25.nsv", "result2201_26.nsv", "result2201_27.nsv", "result2201_28.nsv", "result2201_29.nsv"];
val thyn = "vfmTestDefs2201";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
