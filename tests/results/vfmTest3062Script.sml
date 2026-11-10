Theory vfmTest3062[no_sig_docs]
Ancestors vfmTestDefs3062
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3062_0.nsv", "result3062_1.nsv", "result3062_2.nsv", "result3062_3.nsv", "result3062_4.nsv", "result3062_5.nsv", "result3062_6.nsv", "result3062_7.nsv"];
val thyn = "vfmTestDefs3062";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
