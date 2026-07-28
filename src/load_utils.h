//
// Created by Troy Frever on 4/21/25.
//

#ifndef LOAD_UTILS_H
#define LOAD_UTILS_H

#include <netcdf>
#include <string>
#include "custom_exceptions.h"

class NcVarFillModeInterface {
public:
    virtual void getFillModeParameters(bool &fillActive, float *fillValue) const = 0;
    virtual void getFillModeParameters(bool &fillActive, int *fillValue) const = 0;

    virtual ~NcVarFillModeInterface() = default;
};

class NetCDFVarFillAdapter : public NcVarFillModeInterface {
public:
    NetCDFVarFillAdapter(const netCDF::NcVar &ncVar) : ncVar_(ncVar) {
    }

    void getFillModeParameters(bool &fillActive, float *fillValue) const override {
        ncVar_.getFillModeParameters(fillActive, fillValue);
    }

    void getFillModeParameters(bool &fillActive, int *fillValue) const override {
        ncVar_.getFillModeParameters(fillActive, fillValue);
    }

private:
    const netCDF::NcVar &ncVar_;
};

bool is_missing_indicator(float value, float missing_indicator);
bool is_missing_indicator(int value, int missing_indicator);

bool fix_missing_value(float &cell, float &last_good_value, float missing_indicator);
/**
 * Validates that a value read from a NetCDF variable is not a missing/fill value.
 * Throws MissingRequiredValueException if the value matches the fill indicator.
 */
template <typename T>
void validate_required_value(const NcVarFillModeInterface &ncVar, T actual_value, std::string exception_msg) {
    bool is_fill_active;
    T missing_indicator;

    ncVar.getFillModeParameters(is_fill_active, &missing_indicator);
    if (is_missing_indicator(actual_value, missing_indicator)) {
        throw MissingRequiredValueException(exception_msg);
    }
}

float find_first_non_missing_value(const std::vector<float> &values, float missing_indicator);
void fix_all_missing_values(size_t stepCount, const NcVarFillModeInterface &nc_var_vector, std::vector<float> &hydro_vector,
                            const std::string &vector_name = "", std::vector<std
                                ::string> *error_log = nullptr);

#endif //LOAD_UTILS_H
